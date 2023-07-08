import dataclasses
import typing as T

import pyk.kore.rpc as KoreRpc
import pyk.kore.syntax as Kore

import kaipy.rs_utils as RSUtils

from .kore_utils import extract_equalities_from_witness
from .ReachabilitySystem import ReachabilitySystem


@dataclasses.dataclass
class ContextAlias:
    before: Kore.Pattern
    after: Kore.Pattern


@dataclasses.dataclass
class ContextAliases:
    aliases: T.Tuple[ContextAlias, ...]


# Assumes that rs has only heat rules, otherwise non-termination would happen.
def collect_rests(
    rs: ReachabilitySystem, ca: ContextAlias, term: Kore.Pattern
) -> T.Set[Kore.Pattern]:
    # TODO we have to make sure that the variable names do not clash
    collected: T.Set[Kore.Pattern] = set()
    rest: Kore.Pattern = Kore.EVar(name="VARREST2", sort=Kore.SortApp(name="SortKItem"))
    while True:
        # plug 'term' into the 'before' part of the alias
        input_pattern = Kore.And(
            rs.top_sort,
            Kore.And(
                rs.top_sort,
                ca.before,
                Kore.Equals(
                    rs.top_sort,
                    Kore.SortApp(name="SortKItem"),
                    Kore.EVar(name="VARHERE", sort=Kore.SortApp(name="SortKItem")),
                    term,
                ),
            ),
            Kore.Equals(
                rs.top_sort,
                Kore.SortApp(name="SortKItem"),
                Kore.EVar(name="VARREST", sort=Kore.SortApp(name="SortK")),
                rest,
            ),
        )
        execute_result: KoreRpc.ExecuteResult = rs.kcs.client.execute(
            input_pattern, max_depth=1
        )
        print(f"Stop reason: {execute_result.reason}")
        if execute_result.reason == KoreRpc.StopReason.STUCK:
            return collected
        assert execute_result.reason == KoreRpc.StopReason.STUCK
        mapping = RSUtils.match_ca(rs, ca.after, execute_result.state.kore)
        new_term: Kore.Pattern = mapping[
            Kore.EVar(name="VARHERE", sort=Kore.SortApp(name="SortKItem"))
        ]
        new_rest: Kore.Pattern = mapping[Kore.EVar(name="VARREST", sort=Kore.SortApp(name="SortK"))]
        print(f"new term: {rs.kprint.kore_to_pretty(new_term)}")
        print(f"new rest: {rs.kprint.kore_to_pretty(new_rest)}")
        collected.add(new_rest)

        term = new_term
        rest = new_rest
