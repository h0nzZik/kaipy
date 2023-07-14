import typing as T

import pyk.kore.rpc as KoreRpc
import pyk.kore.syntax as Kore

from .kore_utils import (
    compute_renaming0,
    existentially_quantify_free_variables,
    extract_equalities_and_rest_from_witness,
    extract_equalities_from_witness,
    filter_out_predicates,
    free_evars_of_pattern,
    mapping_to_pattern,
    rename_vars,
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
    vars_to_rename = [
        ev for ev in free_evars_of_pattern(ca) if ev.name not in {"VARHERE", "VARREST"}
    ]
    vars_to_avoid = list(free_evars_of_pattern(data))
    ca_renamed: Kore.Pattern = rename_vars(
        compute_renaming0(vars_to_avoid=vars_to_avoid, vars_to_rename=vars_to_rename),
        ca,
    )
    #print(f"ca_renamed: {rs.kprint.kore_to_pretty(ca_renamed)}")
    eca = existentially_quantify_free_variables(rs.top_sort, ca_renamed)
    ir: KoreRpc.ImpliesResult = rs.kcs.client.implies(data, eca)
    if not ir.satisfiable:
        raise ValueError("No match. Bad context?")
    if ir.substitution is None:
        raise ValueError("No substitution. Bad context?")
    fev = {fv.name for fv in free_evars_of_pattern(ca)}
    return extract_equalities_from_witness(fev, ir.substitution)
