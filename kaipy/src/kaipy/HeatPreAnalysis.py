import dataclasses
import itertools
import logging
import typing as T

import pyk.kore.prelude as KorePrelude
import pyk.kore.rpc as KoreRpc
import pyk.kore.syntax as Kore

import kaipy.rs_utils as RSUtils
from kaipy.KompiledDefinitionWrapper import KompiledDefinitionWrapper

from .kore_utils import (
    extract_equalities_from_witness,
    free_evars_of_pattern,
    some_subpatterns_of,
)
from .ReachabilitySystem import ReachabilitySystem
from .rs_utils import cleanup_pattern

_LOGGER: T.Final = logging.getLogger(__name__)


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
# But the problem is: what should be the sort of this variable? Because the cooling rules expect
# the value to have a certain sort. So, we can transform the semantics so that there is a new sort
# that is a subsort to any other sort. But is that legal? Like, can we subsort hooked sort?


@dataclasses.dataclass(frozen=True)
class HPAResult:
    rests: T.List[Kore.Pattern]
    irreducibles: T.List[Kore.Pattern]


# Assumes that rs has only heat rules, otherwise non-termination would happen.
def collect_rests(
    rs: ReachabilitySystem, ca: ContextAlias, term: Kore.Pattern
) -> HPAResult:
    # TODO we have to make sure that the variable names do not clash
    collected: T.List[Kore.Pattern] = []
    irreducibles: T.List[Kore.Pattern] = []
    rest: Kore.Pattern = Kore.EVar(name="VARREST2", sort=Kore.SortApp(name="SortK"))
    stage = "heating"
    side_condition: Kore.Pattern = Kore.Top(rs.top_sort)
    while True:
        # plug 'term' into the 'before' part of the alias
        # TODO: this is probably not the most efficient way of replacing `VARHERE` with `term`
        # and `VARREST` with `rest`. It works for now, but we probably want to use a substitution instead.
        #  Although, we need to do the conjunction with the side condition anyway.
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

        input_pattern_with_side: Kore.Pattern = Kore.And(
            rs.top_sort, input_pattern, side_condition
        )
        # _LOGGER.info(
        #    f"input_pattern_with_side: {rs.kprint.kore_to_pretty(input_pattern_with_side)}"
        # )
        input_pattern_simplified0 = rs.kcs.client.simplify(input_pattern_with_side)[0]
        # _LOGGER.info(
        #    f"input_pattern_simplified0: {rs.kprint.kore_to_pretty(input_pattern_simplified0)}"
        # )
        input_pattern_simplified = cleanup_pattern(rs, input_pattern_simplified0)
        # input_pattern_simplified = input_pattern_simplified0
        # _LOGGER.info(
        #    f"input_pattern_simplified: {rs.kprint.kore_to_pretty(input_pattern_simplified)}"
        # )

        # print(f"input_pattern_with_side: {rs.kprint.kore_to_pretty(input_pattern_with_side)}")
        execute_result: KoreRpc.ExecuteResult = rs.kcs.client.execute(
            input_pattern_simplified, max_depth=1
        )
        # print(f"input_pattern_with_side (kore): {input_pattern_with_side.text}")
        # _LOGGER.info(f"execute result depth: {execute_result.depth}")
        # _LOGGER.info(f"execute result reason: {execute_result.reason}")
        if execute_result.reason == KoreRpc.StopReason.STUCK:
            _LOGGER.info(f"Stuck {stage}")
            irreducibles.append(term)
            # _LOGGER.info(f"stuck with: {rs.kprint.kore_to_pretty(input_pattern_simplified)}")
            if stage == "heating":
                stage = "cooling"

                # Compute a fresh name for the result. TODO: extract a function
                names = [
                    v.name
                    for v in (
                        free_evars_of_pattern(side_condition).union(
                            free_evars_of_pattern(input_pattern_simplified)
                        )
                    )
                ]
                prefix = "VARRESULT"
                n: int = 0
                while (prefix + str(n)) in names:
                    n = n + 1
                var_result_name = prefix + str(n)

                var_result = Kore.EVar(
                    name=var_result_name, sort=Kore.SortApp(name="SortKItem")
                )
                var_result_k = Kore.App(
                    KorePrelude.KSEQ, (), (var_result, KorePrelude.DOTK)
                )
                # var_result_k = KorePrelude.kseq([var_result])
                side_condition = Kore.And(
                    rs.top_sort,
                    side_condition,
                    Kore.Equals(
                        KorePrelude.BOOL,
                        rs.top_sort,
                        KorePrelude.TRUE,
                        Kore.App("LblisKResult", (), (var_result_k,)),
                    ),
                )
                # side_condition = Kore.Equals(
                #     KorePrelude.BOOL,
                #     rs.top_sort,
                #     KorePrelude.TRUE,
                #     Kore.App("LblisKResult", (), (var_result_k,)),
                # )
                term = var_result
                continue
            else:
                return HPAResult(collected, irreducibles)
        elif (
            execute_result.reason == KoreRpc.StopReason.BRANCHING
        ):  # and stage == "cooling":
            assert execute_result.next_states is not None
            # There should be one subsequent state and one residual
            if len(execute_result.next_states) != 2:
                _LOGGER.warning(
                    f"Too many ({len(execute_result.next_states)}) next states; ending the analysis"
                )
                return HPAResult(collected, irreducibles)
                for i, ns in enumerate(execute_result.next_states):
                    _LOGGER.warning(f"ns[{i}]: {rs.kprint.kore_to_pretty(ns.kore)}")
            assert len(execute_result.next_states) == 2
            # if execute_result.next_states[0].substitution is None:
            #    print(f"next_states[0]: {rs.kprint.kore_to_pretty(execute_result.next_states[0].kore)}")
            #    print(f"next_states[1]: {rs.kprint.kore_to_pretty(execute_result.next_states[1].kore)}")
            # assert execute_result.next_states[0].substitution is not None
            assert execute_result.next_states[1].substitution is None  # the residual
            new_state = execute_result.next_states[0].kore
            side_condition = execute_result.next_states[0].predicate or Kore.Top(
                rs.top_sort
            )
        else:
            assert execute_result.reason == KoreRpc.StopReason.DEPTH_BOUND
            new_state = execute_result.state.kore
            side_condition = execute_result.state.predicate or Kore.Top(rs.top_sort)
        # _LOGGER.info(f"new state: {rs.kprint.kore_to_pretty(new_state)}")
        # print(f"new state (kore): {new_state.text}")
        # mapping = RSUtils.match_ca(rs, ca.after if stage == "heating" else ca.before, new_state)
        mapping = RSUtils.match_ca(rs, ca.after, new_state)

        new_term: Kore.Pattern = mapping[
            Kore.EVar(name="VARHERE", sort=Kore.SortApp(name="SortKItem"))
        ]
        new_rest: Kore.Pattern = mapping[
            Kore.EVar(name="VARREST", sort=Kore.SortApp(name="SortK"))
        ]
        #_LOGGER.warning(f"new term: {rs.kprint.kore_to_pretty(new_term)}")
        #_LOGGER.warning(f"new rest: {rs.kprint.kore_to_pretty(new_rest)}")
        if stage == "heating":
            #_LOGGER.warning(f"adding new rest")
            collected.append(new_rest)

        term = new_term
        rest = new_rest
        stage = "heating"


def get_direct_subterms(t: Kore.Pattern) -> T.List[Kore.Pattern]:
    match t:
        case Kore.App("inj", _, (arg,)):
            return get_direct_subterms(arg)
        case Kore.App(_, _, args):
            return list(args)
    return []


def collect_rests_recursively(
    rs: ReachabilitySystem, ca: ContextAlias, term: Kore.Pattern
) -> T.List[Kore.Pattern]:
    subs = some_subpatterns_of(term)
    to_reduce = {term}
    rests: T.List[Kore.Pattern] = []
    iteration = 0
    while len(to_reduce) > 0:
        iteration = iteration + 1
        _LOGGER.info(f"***** Iteration {iteration} *****")
        t = to_reduce.pop()

        # if it is not KItem, we have to inj{T, KItem} it
        match t:
            case Kore.App("inj", (_, to), _):
                tsort = to
            case Kore.App(sym, _, _):
                tsort = rs.get_symbol_sort(sym)
            case _:
                assert False
        if tsort != KorePrelude.SORT_K_ITEM:
            t = KorePrelude.inj(tsort, KorePrelude.SORT_K_ITEM, t)

        # _LOGGER.info(f"collecting from (kore) {t.text}")
        # _LOGGER.info(f"collecting from {rs.kprint.kore_to_pretty(t)}")
        hparesult = collect_rests(rs, ca, t)
        rests = rests + hparesult.rests
        irs_sub = [get_direct_subterms(ir) for ir in hparesult.irreducibles]
        flattened = list(itertools.chain(*irs_sub))
        flattened_filtered = [x for x in flattened if x in subs and type(x) is Kore.App]
        _LOGGER.info(
            f"Adding {len(flattened_filtered)} elements (out of {len(flattened)}) to be reduced"
        )
        if len(flattened_filtered) == 1:
            _LOGGER.info(f"{rs.kprint.kore_to_pretty(flattened_filtered[0])}")
        # for ff in flattened_filtered:
        #    _LOGGER.info(f"{rs.kprint.kore_to_pretty(ff)}")
        _LOGGER.info(f"{flattened_filtered}")
        to_reduce.update(flattened_filtered)

    return rests


def pre_analyze(
    rs: ReachabilitySystem,
    context_aliases: ContextAliases,
    initial_configuration: Kore.Pattern,
) -> T.List[Kore.Pattern]:
    heat_cool_only_def: KompiledDefinitionWrapper = rs.kdw.heat_cool_only
    with ReachabilitySystem(heat_cool_only_def) as rs_heatcoolonly:
        input_simplified = rs_heatcoolonly.simplify(initial_configuration)
        mapping = RSUtils.match_ca(
            rs_heatcoolonly, context_aliases.aliases[0].before, input_simplified
        )
        initial_here = mapping[
            Kore.EVar(name="VARHERE", sort=Kore.SortApp(name="SortKItem"))
        ]
        rests = collect_rests_recursively(
            rs_heatcoolonly, context_aliases.aliases[0], initial_here
        )
    return rests
