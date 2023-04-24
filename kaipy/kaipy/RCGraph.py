import pyk.kore.syntax as Kore
import networkx as nx # type: ignore

import typing as Type

from .ReachabilitySystem import ReachabilitySystem

from .kore_utils import (
    get_lhs,
    get_rhs,
    free_evars_of_pattern,
    compute_renaming0,
    compute_renaming,
    rename_vars,
    get_predicates,
    is_bottom,
    extract_equalities_and_rest_from_witness,
    extract_equalities_from_witness,
    mapping_to_pattern,
)

from .rs_utils import (
    make_conjunction,
    cleanup_eqs,
    cleanup_pattern,
)

def compose_rules(rs: ReachabilitySystem, first_rule: Kore.Axiom, second_rule: Kore.Axiom, vars_to_avoid: Type.Set[Kore.EVar]) -> Type.Optional[Kore.Rewrites]:
    curr_lhs = get_lhs(first_rule)
    curr_lhs = rs.simplify(curr_lhs)
    curr_rhs = get_rhs(first_rule)
    other_lhs = get_lhs(second_rule)
    other_rhs = get_rhs(second_rule)
    vars_to_avoid = vars_to_avoid.union(free_evars_of_pattern(curr_rhs)).union(free_evars_of_pattern(curr_lhs))
    other_renaming = compute_renaming(other_lhs, list(vars_to_avoid))
    other_lhs_renamed: Kore.Pattern = rename_vars(other_renaming, other_lhs)
    other_rhs_renamed: Kore.Pattern = rename_vars(other_renaming, other_rhs)
    #simplified_conj = rs.kcs.client.simplify(Kore.And(rs.top_sort, curr_rhs, other_lhs_renamed))
    simplified_conj = rs.simplify(Kore.And(rs.top_sort, Kore.And(rs.top_sort, curr_rhs, make_conjunction(rs, get_predicates(curr_lhs))), other_lhs_renamed))
    if is_bottom(simplified_conj):
        return None
    #print(f"not bottom: {rs.kprint.kore_to_pretty(simplified_conj)}")
    #print(f"Axiom1 lhs: {rs.kprint.kore_to_pretty(curr_lhs)}")
    #print(f"Axiom1 rhs: {rs.kprint.kore_to_pretty(curr_rhs)}")
    #print(f"Axiom2 lhs {rs.kprint.kore_to_pretty(other_lhs_renamed)}")
    #print(f"Axiom2 rhs {rs.kprint.kore_to_pretty(other_rhs_renamed)}")
    eqs1,rest1 = extract_equalities_and_rest_from_witness({ v.name for v in free_evars_of_pattern(curr_lhs)}, simplified_conj)
    preds1 = get_predicates(rest1) if rest1 is not None else []
    #print(f"lhs1 equalities: {eqs1}")
    eqs2 = extract_equalities_from_witness({ v.name for v in free_evars_of_pattern(other_rhs_renamed)}, simplified_conj)
    #print(f"lhs1 equalities: {eqs2}")
    # TODO new lhs has to have all the side conditions, not only equalities
    # TODO we also should mark some nodes initial, during the analysis, and then during the optimization phase we can
    #      maybe target only the reachable nodes from the initial ones...

    preds1_conj = make_conjunction(rs, preds1)
    eqs1_p = mapping_to_pattern(rs.top_sort, eqs1)
    side_cond: Kore.Pattern = Kore.And(rs.top_sort, eqs1_p, preds1_conj)
    #print(f"preds1_conj: {rs.kprint.kore_to_pretty(preds1_conj)}")
    new_lhs = rs.simplify(Kore.And(rs.top_sort, curr_lhs, side_cond))
    if is_bottom(new_lhs):
        print(f"not bottom: {rs.kprint.kore_to_pretty(simplified_conj)}")
        print(f"Axiom1 lhs: {rs.kprint.kore_to_pretty(curr_lhs)}")
        print(f"Axiom1 rhs: {rs.kprint.kore_to_pretty(curr_rhs)}")
        print(f"Axiom2 lhs {rs.kprint.kore_to_pretty(other_lhs_renamed)}")
        print(f"Axiom2 rhs {rs.kprint.kore_to_pretty(other_rhs_renamed)}")
        raise RuntimeError("new_lhs is unexpectedly bottom.")
    #new_lhs = rs.kcs.client.simplify(Kore.And(rs.top_sort, curr_lhs, mapping_to_pattern(rs, eqs1))) # FIXME I know this is not enough
    new_rhs = rs.simplify(Kore.And(rs.top_sort, other_rhs_renamed, mapping_to_pattern(rs.top_sort, eqs2)))
    # After the simplification, the intermediate variables (from 'other_renaming') should disappear
    #print(f"New lhs {rs.kprint.kore_to_pretty(new_lhs)}")
    #print(f"New rhs {rs.kprint.kore_to_pretty(new_rhs)}")
    new_lhs_clean = cleanup_pattern(rs, new_lhs)

    new_rhs_clean = cleanup_pattern(rs, new_rhs)
    #print(f"New lhs clean {rs.kprint.kore_to_pretty(new_lhs_clean)}")
    #print(f"New rhs clean {rs.kprint.kore_to_pretty(new_rhs_clean)}")
    rewrite = Kore.Rewrites(rs.top_sort, new_lhs_clean, new_rhs_clean)
    #print(f"rewrite: {rs.kprint.kore_to_pretty(rewrite)}")
    return rewrite


class RCGraph:
    '''RCGraph means 'Rule-Composition Graph'. Nodes are rewrite rules, edges are compositions of such rules
    '''
    g: nx.DiGraph

    def __init__(self):
        self.fresh_int = 0
        self.g = nx.DiGraph()
        self.node_labels = dict()
        pass

    def add_node(self, rule: Kore.Rewrites) -> None:
        self.g.add_node(rule)
    
    # Assume: `edge` is a composition of `fr` and `to`
    def __add_edge(self, fr: Kore.Rewrites, to: Kore.Rewrites, edge: Kore.Rewrites):
        self.g.add_edge(u_of_edge=fr, v_of_edge=to, composition=edge)
    

