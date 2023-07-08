import typing as T

import pyk.kore.rpc as KoreRpc
import pyk.kore.syntax as Kore

from .kore_utils import (
    existentially_quantify_free_variables,
    extract_equalities_and_rest_from_witness,
    extract_equalities_from_witness,
    filter_out_predicates,
    free_evars_of_pattern,
    mapping_to_pattern,
)
from .ReachabilitySystem import ReachabilitySystem


def make_conjunction(rs: ReachabilitySystem, l: T.List[Kore.Pattern]) -> Kore.Pattern:
    result: Kore.Pattern = Kore.Top(rs.top_sort)
    for x in l:
        result = Kore.And(rs.top_sort, result, x)
    return result


def cleanup_pattern(rs: ReachabilitySystem, phi: Kore.Pattern) -> Kore.Pattern:
    main_part, _ = filter_out_predicates(phi)
    assert main_part is not None
    fvphi = free_evars_of_pattern(phi)
    eqs, rest = extract_equalities_and_rest_from_witness({v.name for v in fvphi}, phi)
    evs2_p = cleanup_eqs(rs, main_part, eqs)
    if rest is None:
        return evs2_p
    return Kore.And(rs.top_sort, rest, evs2_p)


def cleanup_eqs(
    rs: ReachabilitySystem,
    main_part: Kore.Pattern,
    eqs: T.Dict[Kore.EVar, Kore.Pattern],
) -> Kore.Pattern:
    fvs = free_evars_of_pattern(main_part)
    evs2 = {k: v for k, v in eqs.items() if (k in fvs)}
    evs2_p = mapping_to_pattern(rs.top_sort, evs2)
    return evs2_p


def match_ca(
    rs: ReachabilitySystem, ca: Kore.Pattern, data: Kore.Pattern
) -> T.Dict[Kore.EVar, Kore.Pattern]:
    eca = existentially_quantify_free_variables(rs.top_sort, ca)
    ir: KoreRpc.ImpliesResult = rs.kcs.client.implies(data, eca)
    if not ir.satisfiable:
        raise ValueError("No match. Bad context?")
    if ir.substitution is None:
        raise ValueError("No substitution. Bad context?")
    fev = {fv.name for fv in free_evars_of_pattern(ca)}
    return extract_equalities_from_witness(fev, ir.substitution)
