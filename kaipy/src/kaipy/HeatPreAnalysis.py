import dataclasses
import typing as T

import pyk.kore.rpc as KoreRpc
import pyk.kore.syntax as Kore
import pyk.kore.prelude as KorePrelude

import kaipy.rs_utils as RSUtils

from .kore_utils import extract_equalities_from_witness
from .ReachabilitySystem import ReachabilitySystem
from .rs_utils import cleanup_pattern


@dataclasses.dataclass
class ContextAlias:
    before: Kore.Pattern
    after: Kore.Pattern


@dataclasses.dataclass
class ContextAliases:
    aliases: T.Tuple[ContextAlias, ...]


# Our goal here is to finitely approximate the set of 'rests of the K cell'
# (that is, typically, the set or chains of freezers) that can be generated from given input term.
# The resulting set R of this pre-analysis can then be used to generate the powerset lattice \mathcal{P}(R)
# whose elements can serve as abstract values in another analysis.
# It is not such a problem if R contains elements that in fact cannot be derived - it just means that \mathcal{P}(R)
# will be larger than necessary, and some of its elements will never be used.
# On the other hand, if an element is missing from R, that can never affect the soundness of the subsequent analysis,
# only its precision.
#
# Terms that cannot be further reduced by heating are typically handled in another way by the semantics.
# Consider for example the configuration fragment
# <k> foo(3, bar(4)) ~> #freezer1(1,2) ~> . </k>
# In general, the semantics of `foo` can do anything. It can, for example, clear the rest of the `<k>` cell
# (potentially preserving it somewhere else; e.g., in a cell representing a language's stack).
# Also, it often happens that the subterms of the heat-irreducible term are heat-reducible, and actually heat-reduced
# - but in a different context.
# Therefore, we want to take these subterms and try to evaluate them in the heat-semantics, too.
#
#
# An interesting situation is with multi-ary seqstrict symbols.
# These try to evaluate the first argument first, and then the second argument, and so on.
# The next argument is evaluated only after the previous argument is turned into a value `v` such that
# `isKResult(v)` returns true, and after the argument is cooled.
# That means that only preserving heating rules is not enough to get all the interesting RESTs;
# we also have to preserve cooling rules. But we do not know in advance which value can be put there.
# Maybe we could just invent variable, say `A:AExp`, and assume in the side condition that `isKResult(A)`.
# But what if there is no value of the particular sort that would be KResult? That is a static-time contradiction,
# and I do not want feed the symbolic execution engine contradictions, for obvious reasons.
# But is it such a problem? First, this situation is probably not very frequent, since it would mean that the
# language's designer made a mistake of wanting to reduce something irreducible.
# Second, the execution could not continue in reallity afterwards, and therefore all the RESTs that we discover
# afterwards are unreachable - which is not such a big issue.
# Third, we can just ask the engine if `isKResult(A:AExp)` has a model :) And if not, at least warn the user.
#


# Assumes that rs has only heat rules, otherwise non-termination would happen.
def collect_rests(
    rs: ReachabilitySystem, ca: ContextAlias, term: Kore.Pattern
) -> T.Set[Kore.Pattern]:
    # TODO we have to make sure that the variable names do not clash
    collected: T.Set[Kore.Pattern] = set()
    rest: Kore.Pattern = Kore.EVar(name="VARREST2", sort=Kore.SortApp(name="SortK"))
    #rest: Kore.Pattern = KorePrelude.DOTK
    while True:
        # plug 'term' into the 'before' part of the alias
        input_pattern = Kore.And(
            rs.top_sort,
            Kore.And(
                rs.top_sort,
                ca.before,
                Kore.Equals(
                    Kore.SortApp(name="SortKItem"),
                    rs.top_sort,
                    Kore.EVar(name="VARHERE", sort=Kore.SortApp(name="SortKItem")),
                    term,
                ),
            ),
            Kore.Equals(
                Kore.SortApp(name="SortK"),
                rs.top_sort,
                Kore.EVar(name="VARREST", sort=Kore.SortApp(name="SortK")),
                rest,
            ),
        )
        input_pattern_simplified = cleanup_pattern(
            rs, rs.kcs.client.simplify(input_pattern)[0]
        )
        print(f"input_pattern_simplified: {rs.kprint.kore_to_pretty(input_pattern_simplified)}")
        execute_result: KoreRpc.ExecuteResult = rs.kcs.client.execute(
            input_pattern_simplified, max_depth=1
        )
        if execute_result.reason == KoreRpc.StopReason.STUCK:
            return collected
        assert execute_result.reason == KoreRpc.StopReason.DEPTH_BOUND
        new_state = execute_result.state.kore
        print(f"new state: {rs.kprint.kore_to_pretty(new_state)}")
        mapping = RSUtils.match_ca(rs, ca.after, new_state)
        new_term: Kore.Pattern = mapping[
            Kore.EVar(name="VARHERE", sort=Kore.SortApp(name="SortKItem"))
        ]
        new_rest: Kore.Pattern = mapping[
            Kore.EVar(name="VARREST", sort=Kore.SortApp(name="SortK"))
        ]
        print(f"new term: {rs.kprint.kore_to_pretty(new_term)}")
        print(f"new rest: {rs.kprint.kore_to_pretty(new_rest)}")
        #print(f"(kore): {new_rest.text}")
        collected.add(new_rest)

        term = new_term
        rest = new_rest
