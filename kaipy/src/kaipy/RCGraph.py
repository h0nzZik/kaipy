import typing as Type

import pyk.kore.syntax as Kore

from .kore_utils import (
    axiom_label,
    compute_renaming,
    compute_renaming0,
    extract_equalities_and_rest_from_witness,
    extract_equalities_from_witness,
    free_evars_of_pattern,
    get_lhs,
    get_rhs,
    is_bottom,
    mapping_to_pattern,
    rename_vars,
)
import kaipy.predicate_filter as PredicateFilter
import kaipy.kore_utils as KoreUtils
from .ReachabilitySystem import ReachabilitySystem
from .rs_utils import make_conjunction


def compose_rules(
    rs: ReachabilitySystem,
    first_rule: Kore.Rewrites,
    second_rule: Kore.Rewrites,
    vars_to_avoid: Type.Set[Kore.EVar],
) -> Type.Optional[Kore.Rewrites]:
    curr_lhs = first_rule.left
    curr_lhs = rs.simplify(curr_lhs)
    curr_rhs = first_rule.right
    other_lhs = second_rule.left
    other_rhs = second_rule.right
    vars_to_avoid = vars_to_avoid.union(free_evars_of_pattern(curr_rhs)).union(
        free_evars_of_pattern(curr_lhs)
    )
    other_renaming = compute_renaming(other_lhs, list(vars_to_avoid))
    other_lhs_renamed: Kore.Pattern = rename_vars(other_renaming, other_lhs)
    other_rhs_renamed: Kore.Pattern = rename_vars(other_renaming, other_rhs)
    # simplified_conj = rs.kcs.client.simplify(Kore.And(rs.top_sort, curr_rhs, other_lhs_renamed))
    simplified_conj = rs.simplify(
        Kore.And(
            rs.top_sort,
            Kore.And(
                rs.top_sort, curr_rhs, make_conjunction(rs, PredicateFilter.get_predicates(curr_lhs))
            ),
            other_lhs_renamed,
        )
    )
    if is_bottom(simplified_conj):
        return None
    # print(f"not bottom: {rs.kprint.kore_to_pretty(simplified_conj)}")
    # print(f"Axiom1 lhs: {rs.kprint.kore_to_pretty(curr_lhs)}")
    # print(f"Axiom1 rhs: {rs.kprint.kore_to_pretty(curr_rhs)}")
    # print(f"Axiom2 lhs {rs.kprint.kore_to_pretty(other_lhs_renamed)}")
    # print(f"Axiom2 rhs {rs.kprint.kore_to_pretty(other_rhs_renamed)}")
    eqs1, rest1 = extract_equalities_and_rest_from_witness(
        {v.name for v in free_evars_of_pattern(curr_lhs)}, simplified_conj
    )
    preds1 = PredicateFilter.get_predicates(rest1) if rest1 is not None else []
    # print(f"lhs1 equalities: {eqs1}")
    eqs2 = extract_equalities_from_witness(
        {v.name for v in free_evars_of_pattern(other_rhs_renamed)}, simplified_conj
    )
    # print(f"lhs1 equalities: {eqs2}")
    # TODO new lhs has to have all the side conditions, not only equalities
    # TODO we also should mark some nodes initial, during the analysis, and then during the optimization phase we can
    #      maybe target only the reachable nodes from the initial ones...

    preds1_conj = make_conjunction(rs, preds1)
    eqs1_p = mapping_to_pattern(rs.top_sort, eqs1)
    side_cond: Kore.Pattern = Kore.And(rs.top_sort, eqs1_p, preds1_conj)
    # print(f"preds1_conj: {rs.kprint.kore_to_pretty(preds1_conj)}")
    new_lhs = rs.simplify(Kore.And(rs.top_sort, curr_lhs, side_cond))
    if is_bottom(new_lhs):
        print(f"not bottom: {rs.kprint.kore_to_pretty(simplified_conj)}")
        print(f"Axiom1 lhs: {rs.kprint.kore_to_pretty(curr_lhs)}")
        print(f"Axiom1 rhs: {rs.kprint.kore_to_pretty(curr_rhs)}")
        print(f"Axiom2 lhs {rs.kprint.kore_to_pretty(other_lhs_renamed)}")
        print(f"Axiom2 rhs {rs.kprint.kore_to_pretty(other_rhs_renamed)}")
        raise RuntimeError("new_lhs is unexpectedly bottom.")
    # new_lhs = rs.kcs.client.simplify(Kore.And(rs.top_sort, curr_lhs, mapping_to_pattern(rs, eqs1))) # FIXME I know this is not enough
    new_rhs = rs.simplify(
        Kore.And(rs.top_sort, other_rhs_renamed, mapping_to_pattern(rs.top_sort, eqs2))
    )
    # After the simplification, the intermediate variables (from 'other_renaming') should disappear
    # print(f"New lhs {rs.kprint.kore_to_pretty(new_lhs)}")
    # print(f"New rhs {rs.kprint.kore_to_pretty(new_rhs)}")
    new_lhs_clean = KoreUtils.cleanup_pattern_new(new_lhs)

    new_rhs_clean = KoreUtils.cleanup_pattern_new(new_rhs)
    # print(f"New lhs clean {rs.kprint.kore_to_pretty(new_lhs_clean)}")
    # print(f"New rhs clean {rs.kprint.kore_to_pretty(new_rhs_clean)}")
    rewrite = Kore.Rewrites(rs.top_sort, new_lhs_clean, new_rhs_clean)
    # print(f"rewrite: {rs.kprint.kore_to_pretty(rewrite)}")
    return rewrite


# class RCGraph:
#     """RCGraph means 'Rule-Composition Graph'. Nodes are rewrite rules, edges are compositions of such rules"""

#     def __init__(self):
#         self.fresh_int = 0
#         self.node_labels = dict()
#         pass

#     def add_node(self, rule: Kore.Rewrites) -> None:
#         self.g.add_node(rule)

#     # Assume: `edge` is a composition of `fr` and `to`
#     def __add_edge(self, fr: Kore.Rewrites, to: Kore.Rewrites, edge: Kore.Rewrites):
#         self.g.add_edge(u_of_edge=fr, v_of_edge=to, composition=edge)

#     def try_add_edge(
#         self, rs: ReachabilitySystem, fr: Kore.Rewrites, to: Kore.Rewrites
#     ):
#         edge = compose_rules(rs, fr, to, set())
#         if edge:
#             self.__add_edge(fr, to, edge)

#     def to_dict(self) -> Type.Dict[str, Type.Any]:
#         nodes: Type.Dict[int, Kore.Rewrites] = {
#             i: n for i, n in enumerate(self.g.nodes) if type(n) is Kore.Rewrites
#         }
#         edges: Type.List[Type.Tuple[int, int, Kore.Rewrites]] = [
#             (i1, i2, self.g.get_edge_data(r1, r2)["composition"])
#             for i1, r1 in nodes.items()
#             for i2, r2 in nodes.items()
#             if self.g.has_edge(r1, r2)
#         ]
#         return {
#             "nodes": {i: n.dict for i, n in nodes.items()},
#             "edges": [(i1, i2, c.dict) for i1, i2, c in edges],
#         }

#     @staticmethod
#     def from_dict(d: Type.Dict[str, Type.Any]):
#         rcg = RCGraph()
#         nodes = d["nodes"]
#         edges = d["edges"]
#         for r in nodes:
#             rcg.add_node(Kore.Rewrites.from_dict(r))

#         for i1, i2, c in edges:
#             rcg.__add_edge(nodes[i1], nodes[i2], Kore.Rewrites.from_dict(c))

#         return rcg


# def make_RCG_from_rs(rs: ReachabilitySystem) -> RCGraph:
#     rws: Type.List[Type.Tuple[Kore.Rewrites, str]] = []
#     for axiom in rs.kdw.rewrite_rules:
#         match axiom:
#             case Kore.Axiom(_, Kore.Rewrites(_, _, _) as rewrite, _):
#                 # For some reason, the frontend is able to generate a rule with unsatisfiable lhs.
#                 # We skip such rules.
#                 left_simplified = rs.simplify(rewrite.left)
#                 if is_bottom(left_simplified):
#                     print(f"skipping {axiom_label(axiom)} (unsat lhs)")
#                     continue
#                 rws.append((rewrite, axiom_label(axiom)))

#     rcg = RCGraph()
#     for rewrite, _ in rws:
#         rcg.add_node(rewrite)

#     total = len(rws) * len(rws)
#     current = 1
#     for rw1, name1 in rws:
#         for rw2, name2 in rws:
#             print(f"Generating RCG: {current} / {total}")
#             print(f"{name1} * {name2}")
#             rcg.try_add_edge(rs, rw1, rw2)
#             current = current + 1
#
#    return rcg
