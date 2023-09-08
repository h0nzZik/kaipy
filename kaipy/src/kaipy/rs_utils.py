import typing as T

import pyk.kore.rpc as KoreRpc
import pyk.kore.syntax as Kore

from .kore_utils import (
    compute_renaming0,
    existentially_quantify_free_variables,
    extract_equalities_and_rest_from_witness,
    extract_equalities_from_witness,
    free_evars_of_pattern,
    mapping_to_pattern,
    rename_vars,
)
import kaipy.kore_utils as KoreUtils
import kaipy.predicate_filter as PredicateFilter
from .ReachabilitySystem import ReachabilitySystem


def make_conjunction(rs: ReachabilitySystem, l: T.Sequence[Kore.Pattern]) -> Kore.Pattern:
    return KoreUtils.make_conjunction(rs.top_sort, l)

def make_disjunction(rs: ReachabilitySystem, l: T.Sequence[Kore.Pattern]) -> Kore.Pattern:
    return KoreUtils.make_disjunction(rs.top_sort, l)

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
    # print(f"ca_renamed: {rs.kprint.kore_to_pretty(ca_renamed)}")
    eca = existentially_quantify_free_variables(rs.top_sort, ca_renamed)
    ir: KoreRpc.ImpliesResult = rs.kcs.client.implies(data, eca)
    if not ir.satisfiable:
        raise ValueError("No match. Bad context?")
    if ir.substitution is None:
        raise ValueError("No substitution. Bad context?")
    fev = {fv.name for fv in free_evars_of_pattern(ca)}
    return extract_equalities_from_witness(fev, ir.substitution)
