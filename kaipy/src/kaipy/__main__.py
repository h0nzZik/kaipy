import argparse
import functools
import json
import logging
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import (
    IO,
    Any,
    Callable,
    Dict,
    Final,
    Iterable,
    List,
    Mapping,
    Optional,
    Set,
    Tuple,
    Union,
)

import matplotlib.pyplot as plt  # type: ignore
import networkx as nx  # type: ignore
import pyk.kore.rpc
import pyk.kore.syntax as Kore
from immutabledict import immutabledict
from pyk.kore.kompiled import KompiledKore
from pyk.kore.parser import KoreParser

from .kcommands import KRUN_COMMAND
from .kore_utils import (
    axiom_label,
    axiom_uuid,
    compute_renaming,
    compute_renaming0,
    extract_equalities_and_rest_from_witness,
    extract_equalities_from_witness,
    free_evars_of_pattern,
    get_fresh_evar,
    get_fresh_evars_with_sorts,
    get_lhs,
    get_predicates,
    get_rhs,
    is_bottom,
    mapping_to_pattern,
    rename_vars,
    some_subpatterns_of,
    existentially_quantify_free_variables,
    existentially_quantify_variables,
)

# from .RCGraph import RCGraph, make_RCG_from_rs
from .ReachabilitySystem import ReachabilitySystem
from .rs_utils import cleanup_eqs, cleanup_pattern, make_conjunction
from .TriviallyManagedKompiledKore import TriviallyManagedKompiledKore


def compute_conjunction(
    rs: ReachabilitySystem, a: Kore.Pattern, b: Kore.Pattern
) -> Kore.Pattern:
    return rs.simplify(Kore.And(rs.top_sort, a, b))


def compute_match(
    rs: ReachabilitySystem, patt_from: Kore.Pattern, axiom: Kore.Rewrites
) -> Tuple[Kore.Pattern, Dict[str, str]]:
    vars_to_rename = list(free_evars_of_pattern(axiom.left))
    vars_to_avoid = vars_to_rename + list(free_evars_of_pattern(patt_from))
    new_vars = get_fresh_evars_with_sorts(
        avoid=list(vars_to_avoid), sorts=list(map(lambda ev: ev.sort, vars_to_rename))
    )
    vars_fr: List[str] = list(map(lambda e: e.name, vars_to_rename))
    vars_to: List[str] = list(map(lambda e: e.name, new_vars))
    renaming = dict(zip(vars_fr, vars_to))
    axiom_left = rename_vars(renaming, axiom.left)
    lhs_match = compute_conjunction(rs, patt_from, axiom_left)
    return lhs_match, renaming


def may_transit(
    rs: ReachabilitySystem, patt_from: Kore.Pattern, axiom: Kore.Rewrites
) -> bool:
    lhs_match, _ = compute_match(rs, patt_from, axiom)
    return not is_bottom(lhs_match)


@dataclass(frozen=True)
class SemanticsPreGraph:
    @dataclass(frozen=True)
    class Node:
        pattern: Kore.Pattern
        original_rule_label: str
        applicable_rules: List[str]

        @property
        def dict(self) -> Dict[str, Any]:
            return {
                "pattern": self.pattern.dict,
                "original_rule_label": self.original_rule_label,
                "applicable_rules": self.applicable_rules,
            }

        @staticmethod
        def from_dict(dct: Dict[str, Any]):
            return SemanticsPreGraph.Node(
                Kore.Pattern.from_dict(dct["pattern"]),
                dct["original_rule_label"],
                dct["applicable_rules"],
            )

    nodes: List[Node]

    @property
    def dict(self) -> Dict[str, Any]:
        return {"nodes": [n.dict for n in self.nodes]}

    @staticmethod
    def from_dict(dct: Dict[str, Any]):
        return SemanticsPreGraph(
            [SemanticsPreGraph.Node.from_dict(n) for n in dct["nodes"]]
        )


def compute_semantics_pregraph(rs: ReachabilitySystem) -> SemanticsPreGraph:
    nodes: List[SemanticsPreGraph.Node] = []

    for axiom in rs.kdw.rewrite_rules:
        match axiom:
            case Kore.Axiom(_, Kore.Rewrites(_, lhs, _), _):
                pattern: Kore.Pattern = lhs
                original_rule_label: str = axiom_label(axiom)
                applicable_rules: List[str] = []
                for rule_to_apply in rs.kdw.rewrite_rules:
                    match rule_to_apply:
                        case Kore.Axiom(_, Kore.Rewrites(_, _, _) as r, _):
                            if may_transit(rs, pattern, r):
                                applicable_rule: str = axiom_label(rule_to_apply)
                                print(
                                    f"May transit from {original_rule_label} using {applicable_rule} "
                                )
                                applicable_rules.append(applicable_rule)
                nodes.append(
                    SemanticsPreGraph.Node(
                        pattern, original_rule_label, applicable_rules
                    )
                )

    return SemanticsPreGraph(nodes)


@dataclass(frozen=True)
class Substitution:
    mapping: Mapping[Kore.EVar, Kore.Pattern]

    def free_evars(self) -> Set[Kore.EVar]:
        fe: Set[Kore.EVar] = set()
        for _, p in self.mapping.items():
            fe = fe.union(free_evars_of_pattern(p))
        return fe


def subst_to_pattern(sort: Kore.Sort, subst: Substitution) -> Kore.Pattern:
    return mapping_to_pattern(sort, subst.mapping)



def substitution_subsumed_by(
    rs: ReachabilitySystem, subst1: Substitution, subst2: Substitution, verbose: bool
) -> bool:
    sortList = Kore.SortApp("SortList", ())
    pattern1 = subst_to_pattern(sortList, subst1)
    pattern2 = subst_to_pattern(sortList, subst2)
    fes = subst1.free_evars().union(subst2.free_evars())
    keys = set(subst1.mapping.keys()).union(subst2.mapping.keys())
    list_pattern = Kore.App("Lbl'Stop'List", (), ())
    for k in keys:
        inj = Kore.App(
            "inj",
            (
                k.sort,
                Kore.SortApp("SortKItem", ()),
            ),
            (k,),
        )
        list_pattern = Kore.App(
            "Lbl'Unds'List'Unds'",
            (),
            (list_pattern, Kore.App("LblListItem", (), (inj,))),
        )

    lhs = Kore.And(sortList, list_pattern, pattern1)
    rhs = Kore.And(sortList, list_pattern, pattern2)
    renaming = compute_renaming0(
        vars_to_avoid=list(keys.union(fes)), vars_to_rename=list(subst2.free_evars())
    )
    rhs_renamed = rename_vars(renaming, rhs)
    # lhs = rs.kcs.client.simplify(lhs)
    # rhs_renamed = rs.kcs.client.simplify(rhs_renamed)
    rhs_renamed_quantified = existentially_quantify_variables(
        sortList,
        rhs_renamed,
        [Kore.EVar(renaming[x.name], x.sort) for x in subst2.free_evars()],
    )
    if verbose:
        print("Subsumption?")
        print(f"lhs = {rs.kprint.kore_to_pretty(lhs)}")
        print(f"rhs = {rs.kprint.kore_to_pretty(rhs_renamed_quantified)}")
    try:
        impl_result = rs.kcs.client.implies(lhs, rhs_renamed_quantified)
    except:
        print("An exception occurred.")
        # print(f"lhs = {rs.kprint.kore_to_pretty(lhs)}")
        # print(f"rhs = {rs.kprint.kore_to_pretty(rhs_renamed_quantified)}")
        print(f"lhs = {lhs.text}")
        print(f"rhs = {rhs_renamed_quantified.text}")
        print(f"pattern1 = {pattern1.text}")
        print(f"pattern2 = {pattern2.text}")
        raise
    if verbose:
        print(f"sat? {impl_result.satisfiable}")
    return impl_result.satisfiable


# The graph on which we do the analysis
class SCFG:
    @dataclass(frozen=True)
    class Node:
        pattern: Kore.Pattern
        original_rule_label: str
        applicable_rules: Tuple[str, ...]

    @dataclass
    class NodeRuleInfo:
        initial: bool
        substitutions: Set[Substitution]
        new_substitutions: Set[Substitution]

    rs: ReachabilitySystem
    nodes: Set[Node]
    node_rule_info: Dict[Tuple[Node, str], NodeRuleInfo]
    # graph: nx.Graph

    def __init__(self, rs: ReachabilitySystem, spg: SemanticsPreGraph):
        self.rs = rs
        self.graph = nx.Graph()
        self.nodes = {
            SCFG.Node(
                pattern=node.pattern,
                original_rule_label=node.original_rule_label,
                applicable_rules=tuple(node.applicable_rules),
            )
            for node in spg.nodes
        }
        self.node_rule_info = {}
        for n in self.nodes:
            for rl in n.applicable_rules:
                self.node_rule_info[(n, rl)] = SCFG.NodeRuleInfo(
                    initial=False, substitutions=set(), new_substitutions=set()
                )

    def break_pattern(
        self,
        pattern: Kore.Pattern,
        normalize: Callable[[Set[Kore.EVar], Substitution], Substitution],
        mark_initial: bool,
    ):
        # VarARGS:SortList{}
        # print(f"Original {self.rs.kprint.kore_to_pretty(pattern)}")
        # vars_to_rename = [v for v in self.rs.rules_variables if v.name != 'VarARGS']

        vars_to_rename = [v for v in self.rs.kdw.rules_variables]
        renaming = compute_renaming0(
            list(free_evars_of_pattern(pattern)), vars_to_rename
        )
        ##print(f"Renaming: {renaming}")
        input_kore_renamed: Kore.Pattern = rename_vars(renaming, pattern)

        # input_kore_renamed = pattern
        print(f"Breaking {self.rs.kprint.kore_to_pretty(input_kore_renamed)}")
        # print(f"Breaking: {input_kore_renamed.text}")
        for node in self.nodes:
            for ruleid in node.applicable_rules:
                rule: Kore.Axiom = self.rs.rule_by_id(ruleid)
                match rule:
                    case Kore.Axiom(_, Kore.Rewrites(_, lhs, _) as rewrites, _):
                        m = compute_conjunction(self.rs, input_kore_renamed, lhs)
                        if is_bottom(m):
                            continue
                        print(f"{node.original_rule_label}.{ruleid}:")
                        nri = self.node_rule_info[(node, ruleid)]
                        if mark_initial:
                            nri.initial = True
                        # print(f"Matched rule's lhs: {self.rs.kprint.kore_to_pretty(lhs)}")
                        eqs = extract_equalities_from_witness(
                            {v.name for v in free_evars_of_pattern(rewrites)}, m
                        )
                        # if ruleid == 'IMP.getArg':
                        #    print(self.rs.kprint.kore_to_pretty(m))

                        substitution = Substitution(immutabledict(eqs))
                        normalized_substitution = normalize(
                            free_evars_of_pattern(lhs).union(
                                free_evars_of_pattern(node.pattern)
                            ),
                            substitution,
                        )

                        verbose = ruleid == "IMP.while-unroll"
                        if any(
                            [
                                substitution_subsumed_by(
                                    self.rs,
                                    normalized_substitution,
                                    subst,
                                    verbose=verbose,
                                )
                                for subst in nri.substitutions
                            ]
                        ):
                            continue
                        # impl_result = self.rs.kcs.client.implies(nsp, ecover)
                        # if impl_result.satisfiable:
                        #    continue
                        print("Adding a substitution")
                        nri.substitutions.add(normalized_substitution)
                        nri.new_substitutions.add(normalized_substitution)

    def choose(self) -> Optional[Tuple[Node, str, Substitution]]:
        for (node, ruleid), nri in self.node_rule_info.items():
            if list(nri.new_substitutions) != []:
                substitution = list(nri.new_substitutions)[0]
                nri.new_substitutions.remove(substitution)
                return (node, ruleid, substitution)
        return None


def app_size(p: Kore.Pattern) -> int:
    match p:
        case Kore.App(_, _, args):
            return 1 + sum([app_size(a) for a in args])
    return 1


# TODO maybe we could allow constants of sort Bool, since there are only two of them.
# Or finite / non-recursive sorts.
def is_linear_combination_of(
    subpatterns: Dict[Kore.Pattern, int],
    allowed_outliers: int,
    allowed_outlier_size: int,
    remaining_unary_size: int,
    candidate: Kore.Pattern,
) -> Tuple[bool, Dict[Kore.Pattern, int], int, int]:
    if subpatterns.get(candidate, 0) >= 1:
        subpatterns2 = subpatterns.copy()
        subpatterns2[candidate] = subpatterns2[candidate] - 1
        return True, subpatterns2, allowed_outliers, remaining_unary_size

    match candidate:
        case Kore.EVar(_, _):
            return True, subpatterns, allowed_outliers, remaining_unary_size
        # There is only finitely many nullary constructors, so we allow these
        case Kore.App(_, _, ()):
            return True, subpatterns, allowed_outliers, remaining_unary_size
        # There are subsort hierarchies of finite height only.
        # We assume that `inj` is used for upcasting only.
        case Kore.App("inj", _, (arg,)):
            return is_linear_combination_of(
                subpatterns,
                allowed_outliers=allowed_outliers,
                allowed_outlier_size=allowed_outlier_size,
                candidate=arg,
                remaining_unary_size=remaining_unary_size,
            )
        # The problem is that we often get chains of freezers of length that is linear to the size of the input program.
        # like, the expression `(x+y)+z` will lead to a chain similar to `x ~> #freezer+R(y) ~> #freezer+R(z)`
        case Kore.App(_, _, (arg,)):
            if remaining_unary_size <= 0:
                pass
            return is_linear_combination_of(
                subpatterns,
                allowed_outliers=allowed_outliers,
                allowed_outlier_size=allowed_outlier_size,
                remaining_unary_size=(remaining_unary_size - 1),
                candidate=arg,
            )
            # return False,[],0
            # no fall-through, break
        # Constructors of arity 2 or more
        case Kore.App(_, _, args):
            assert len(args) >= 2
            b, u, a, r = True, subpatterns, allowed_outliers, remaining_unary_size
            for arg in args:
                b, u, a, r = is_linear_combination_of(
                    subpatterns=u,
                    allowed_outliers=a,
                    allowed_outlier_size=allowed_outlier_size,
                    remaining_unary_size=r,
                    candidate=arg,
                )
                if not b:
                    break
            if b:
                return True, u, a, r

    # Outliers allowed?
    if allowed_outliers >= 1 and app_size(candidate) <= allowed_outlier_size:
        return True, subpatterns, (allowed_outliers - 1), remaining_unary_size

    return False, {}, 0, 0


def make_constructor_pattern(
    rs: ReachabilitySystem, pattern: Kore.Pattern, avoid: Set[Kore.EVar]
) -> Kore.Pattern:
    modified: bool = False

    def go(
        p: Kore.Pattern, avoid: Set[Kore.EVar]
    ) -> Tuple[Kore.Pattern, Set[Kore.EVar]]:
        # print(f"go {p.text}")
        match p:
            # We cannot use the generic Kore.App case for injections
            # because the return sort of 'inj' is 'To' - that is, the second sort parameter.
            case Kore.App("inj", sorts, (arg,)):
                r, a = go(arg, avoid)
                return Kore.App("inj", sorts, (r,)), a
            case Kore.App(symbol, sorts, args):
                if len(sorts) != 0:
                    raise RuntimeError(f"Weird pattern {p}")
                if not rs.is_nonhooked_constructor(symbol):
                    nonlocal modified
                    modified = True
                    x = get_fresh_evar(list(avoid), rs.get_symbol_sort(symbol))
                    # print(f"fresh evar: {x}")
                    return x, avoid.union({x})

                new_args: List[Kore.Pattern] = []
                a = avoid
                for arg in args:
                    r, a = go(arg, a)
                    new_args.append(r)
                return Kore.App(symbol, sorts, tuple(new_args)), a
            case Kore.EVar(_, _):
                return p, avoid
            case Kore.DV(_, _):
                return p, avoid
            case _:
                raise NotImplementedError(f"Not implemented: {p.text}")

    fvs = free_evars_of_pattern(pattern)
    new_pattern, _ = go(pattern, fvs.union(avoid))

    if modified:
        pass
        print(f"old: {pattern.text}")
        print(f"new: {new_pattern.text}")
        # print(f"old: {rs.kprint.kore_to_pretty(pattern)}")
        # print(f"new: {rs.kprint.kore_to_pretty(new_pattern)}")
    return new_pattern


def make_normalizer(
    rs: ReachabilitySystem, pattern: Kore.Pattern, avoid: Set[Kore.EVar]
) -> Callable[[Set[Kore.EVar], Substitution], Substitution]:
    # print(f"Make normalizer from {rs.kprint.kore_to_pretty(pattern)}")
    # subpatterns = [s for s in some_subpatterns_of(pattern) if type(s) is not Kore.EVar]
    subpatterns = some_subpatterns_of(pattern)
    allowed_outliers = 0  # 1.
    allowed_outlier_size = 3
    max_unary_size = int(app_size(pattern))
    # print(f"max unary size: {max_unary_size}")
    # app_size
    # print(f"vars in subpatterns: {[v for v in subpatterns if type(v) is Kore.EVar]}")

    def is_there(s: Kore.Sort, candidate: Kore.Pattern) -> bool:
        match s:
            case Kore.SortApp("SortMap", _):
                return False
            case Kore.SortApp("SortList", _):
                return False
            case Kore.SortApp("SortInt", _):
                return False
            case Kore.SortApp("SortSet", _):
                return False
        b, _, _, _ = is_linear_combination_of(
            subpatterns=subpatterns.copy(),
            allowed_outliers=allowed_outliers,
            allowed_outlier_size=allowed_outlier_size,
            remaining_unary_size=max_unary_size,
            candidate=candidate,
        )
        if b:
            return True
        if type(candidate) is Kore.EVar:
            # print(f"Filtering out a variable {candidate}") # Do not spend time pretty printing
            return False
        print(f"***Filtering out {rs.kprint.kore_to_pretty(candidate)}")
        # print(f"***Filtering out {candidate.text}")
        # print("tracing")
        # is_app_combination(subpatterns, candidate, trace=True)
        return False

    def f(avoid2: Set[Kore.EVar], s: Substitution) -> Substitution:
        s2: Dict[Kore.EVar, Kore.Pattern] = dict()
        for k, v in s.mapping.items():
            constr = make_constructor_pattern(rs, v, avoid=avoid2.union(avoid))
            avoid2 = avoid2.union(free_evars_of_pattern(constr))
            s2[k] = constr
        # s2 = {k : make_constructor_pattern(rs, v, avoid=avoid2.union(avoid)) for k,v in s.mapping.items()}
        new_subst = Substitution(
            immutabledict({k: v for k, v in s2.items() if is_there(k.sort, v)})
        )
        # Try validatiny
        # print(f"new subst: {subst_to_pattern(rs.top_sort, new_subst).text}")
        # print(f"new subst simplified: {rs.simplify(subst_to_pattern(rs.top_sort, new_subst)).text}")
        return new_subst

    return f


def perform_analysis(rs: ReachabilitySystem, spg, normalize, input_kore):
    scfg = SCFG(rs, spg)
    scfg.break_pattern(input_kore, normalize=normalize, mark_initial=True)
    while True:
        x = scfg.choose()
        if x is None:
            return scfg
        (node, ruleid, substitution) = x
        print(f"Choosing node {node.original_rule_label}")
        sp = subst_to_pattern(rs.top_sort, substitution)
        # print(f"Node: {rs.kprint.kore_to_pretty(node.pattern)}")
        # print(f"Substitution: {rs.kprint.kore_to_pretty(sp)}")
        patt: Kore.Pattern = Kore.And(rs.top_sort, node.pattern, sp)
        simplified_patt = cleanup_pattern(rs, rs.simplify(patt))
        # print(f"Executing pattern: {rs.kprint.kore_to_pretty(simplified_patt)}")
        # exec_result = rs.kcs.client.execute(pattern=patt, max_depth=1)
        exec_result = rs.kcs.client.execute(pattern=simplified_patt, max_depth=1)

        next_patterns: List[Kore.Pattern] = (
            [exec_result.state.kore]
            if exec_result.next_states is None
            else [s.kore for s in exec_result.next_states]
        )
        print(f"Has {len(next_patterns)} successors")
        for new_pattern in next_patterns:
            # print("Breaking a pattern")
            scfg.break_pattern(new_pattern, normalize=normalize, mark_initial=False)
    return scfg


def print_analyze_results(rs, scfg: SCFG):
    print("****** ANALYSIS RESULTS *********")
    for node in scfg.nodes:
        for ruleid in node.applicable_rules:
            ri = scfg.node_rule_info[(node, ruleid)]
            print(f"{node.original_rule_label}/{ruleid}")
            for sub in ri.substitutions:
                print(
                    f"  {rs.kprint.kore_to_pretty(subst_to_pattern(rs.top_sort, sub))}"
                )

    print("States/rules without empty substitution")
    for node in scfg.nodes:
        for ruleid in node.applicable_rules:
            ri = scfg.node_rule_info[(node, ruleid)]
            has_empty = False
            for sub in ri.substitutions:
                if not bool(sub.mapping):
                    has_empty = True
            if not has_empty:
                print(f"{node.original_rule_label}/{ruleid}")


def next_patterns_of(rs: ReachabilitySystem, pattern: Kore.Pattern):
    exec_result = rs.kcs.client.execute(pattern, max_depth=1)
    next_patterns: List[Kore.Pattern] = (
        [exec_result.state.kore]
        if exec_result.next_states is None
        else [s.kore for s in exec_result.next_states]
    )
    return next_patterns


def can_self_loop(rs: ReachabilitySystem, rule: Kore.Axiom):
    match rule:
        case Kore.Axiom(vs, Kore.Rewrites(sort, lhs, rhs) as rewrites, _):
            lhs_renamed: Kore.Pattern = rename_vars(
                compute_renaming(lhs, list(free_evars_of_pattern(lhs))), lhs
            )
            if not is_bottom(rs.simplify(Kore.And(rs.top_sort, rhs, lhs_renamed))):
                return True
            return False

    raise RuntimeError("Not a rewrite rule")


def to_axiom_list(rs: ReachabilitySystem, scfg: SCFG) -> List[Tuple[Kore.Axiom, bool]]:
    rewrite_axioms: List[Tuple[Kore.Axiom, bool]] = []
    for node in scfg.nodes:
        if len(node.applicable_rules) != 1:
            print(
                f"warn: applicable rules = {node.applicable_rules} for {node.original_rule_label}"
            )
        for rule_id in node.applicable_rules:
            rule: Kore.Axiom = rs.rule_by_id(rule_id)
            match rule:
                case Kore.Axiom(vs, Kore.Rewrites(sort, lhs, rhs) as rewrites, _):
                    ri = scfg.node_rule_info[(node, rule_id)]
                    for sub in ri.substitutions:
                        conjunction = rs.simplify(
                            Kore.And(sort, lhs, subst_to_pattern(rs.top_sort, sub))
                        )
                        rewrite_axioms.append(
                            (
                                Kore.Axiom(
                                    vs, Kore.Rewrites(sort, conjunction, rhs), ()
                                ),
                                ri.initial,
                            )
                        )
    return rewrite_axioms


def axiom_list_to_json(rewrite_axioms: List[Tuple[Kore.Axiom, bool]]) -> str:
    return json.dumps([(a.text, b) for a, b in rewrite_axioms])


def parse_axiom(s: str) -> Kore.Axiom:
    parser = KoreParser(s)
    return parser.axiom()


def json_to_axiom_list(s: str) -> List[Tuple[Kore.Axiom, bool]]:
    return [(parse_axiom(x[0]), x[1]) for x in json.loads(s)]


def analyze(rs: ReachabilitySystem, args) -> int:
    with open(args["analyzer"], mode="r") as fr:
        jsa = json.load(fr)
    spg: SemanticsPreGraph = SemanticsPreGraph.from_dict(jsa)
    input_kore: Kore.Pattern = rs.kdw.get_input_kore(Path(args["input"]))

    input_kore_simplified = rs.simplify(input_kore)
    normalize = make_normalizer(rs, input_kore_simplified, avoid=rs.kdw.rules_variables)
    scfg = perform_analysis(rs, spg, normalize, input_kore_simplified)
    print_analyze_results(rs, scfg)
    axiom_list: List[Tuple[Kore.Axiom, bool]] = to_axiom_list(rs, scfg)
    with open(args["output"], mode="w") as fw:
        fw.write(axiom_list_to_json(axiom_list))

    return 0


def generate_analyzer(rs: ReachabilitySystem, args) -> int:
    with open(args["analyzer"], mode="w") as fw:
        semantics_pregraph = compute_semantics_pregraph(rs)
        fw.write(json.dumps(semantics_pregraph.dict))
    return 0


def combine_rules(
    rs: ReachabilitySystem,
    first_rule: Kore.Axiom,
    second_rule: Kore.Axiom,
    vars_to_avoid: Set[Kore.EVar],
) -> Optional[Tuple[Kore.Axiom, Kore.Pattern]]:
    curr_lhs = get_lhs(first_rule)
    curr_lhs = rs.simplify(curr_lhs)
    curr_rhs = get_rhs(first_rule)
    other_lhs = get_lhs(second_rule)
    other_rhs = get_rhs(second_rule)
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
                rs.top_sort, curr_rhs, make_conjunction(rs, get_predicates(curr_lhs))
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
    preds1 = get_predicates(rest1) if rest1 is not None else []
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
    new_lhs_clean = cleanup_pattern(rs, new_lhs)

    new_rhs_clean = cleanup_pattern(rs, new_rhs)
    # print(f"New lhs clean {rs.kprint.kore_to_pretty(new_lhs_clean)}")
    # print(f"New rhs clean {rs.kprint.kore_to_pretty(new_rhs_clean)}")
    rewrite = Kore.Rewrites(rs.top_sort, new_lhs_clean, new_rhs_clean)
    # print(f"rewrite: {rs.kprint.kore_to_pretty(rewrite)}")
    return Kore.Axiom((), rewrite, ()), side_cond


@dataclass
class AxiomInfo:
    axiom_id: int
    is_looping: bool
    is_terminal: bool
    is_initial: bool
    is_exploding: bool
    non_successors: List[Kore.Axiom]


def pick_non_looping_non_terminal_axiom(
    axioms: Mapping[Kore.Axiom, AxiomInfo]
) -> Optional[Tuple[Kore.Axiom, AxiomInfo]]:
    non_looping = [
        (ax, ai)
        for ax, ai in axioms.items()
        if (not ai.is_looping) and (not ai.is_terminal) and (not ai.is_exploding)
    ]
    if len(non_looping) >= 1:
        return non_looping[0]
    return None


@dataclass
class AxiomStats:
    total: int
    n_initial: int
    n_looping: int
    n_terminal: int
    n_exploding: int


def compute_stats(axioms: Mapping[Kore.Axiom, AxiomInfo]) -> AxiomStats:
    stats = AxiomStats(0, 0, 0, 0, 0)
    for _, ai in axioms.items():
        stats.total = stats.total + 1
        if ai.is_initial:
            stats.n_initial = stats.n_initial + 1
        if ai.is_looping:
            stats.n_looping = stats.n_looping + 1
        if ai.is_terminal:
            stats.n_terminal = stats.n_terminal + 1
        if ai.is_exploding:
            stats.n_exploding = stats.n_exploding + 1
    return stats


def choose_node(g: nx.DiGraph):
    for n in g.nodes:
        if len(g.successors(n)) != 1:
            continue
        n2 = g.successors(n)[0]
        if len(g.predecessors(n2)) != 1:
            continue
        return n, n2
    return None


def optimize(
    rs: ReachabilitySystem, rewrite_axioms: List[Tuple[Kore.Axiom, bool]], treshold=2
) -> List[Tuple[Kore.Axiom, bool]]:
    print(
        f"Total axioms: {len(rewrite_axioms)} (original was: {len(rs.kdw.rewrite_rules)})"
    )

    plt.ion()
    g: nx.DiGraph = nx.DiGraph()
    for ax, _ in rewrite_axioms:
        g.add_node(ax)

    print("Building the graph")
    for i, ax1 in enumerate(g.nodes):
        nx.draw(g, with_labels=False, font_weight="bold")
        plt.show()
        plt.pause(1)
        for j, ax2 in enumerate(g.nodes):
            # plt.show(block=False)
            result = combine_rules(rs, ax1, ax2, vars_to_avoid=set())
            print(f"{i},{j} = {result is not None}")
            if result is None:
                continue
            combined, side_cond = result
            g.add_edge(ax1, ax2, composition=combined)

    while True:
        nx.draw(g, with_labels=False, font_weight="bold")
        plt.show()
        plt.pause(1)
        # plt.show(block=False)
        choice = choose_node(g)
        if choice is None:
            break
        ax1, ax2 = choice
        composition = g.edges(ax1, ax2)["composition"]
        g.remove_edge(ax1, ax2)
        for ax3 in g.successors(ax2):
            composition2 = g.edges(ax2, ax3)["composition"]
            g.remove_edge(ax2, ax3)
            new_composition = combine_rules(
                rs, composition, composition2, vars_to_avoid=set()
            )
            g.add_edge(ax1, ax3, composition=new_composition)
        g.remove_node(ax2)

    print("finished")
    return [(ax, False) for ax in g.nodes()]

    axiom_map = {
        ax: AxiomInfo(
            axiom_id=i,
            is_looping=can_self_loop(rs, ax),
            is_initial=b,
            is_terminal=False,
            non_successors=[],
            is_exploding=False,
        )
        for i, (ax, b) in enumerate(rewrite_axioms)
    }
    next_id = 1 + len(rewrite_axioms)

    non_edges: Set[Tuple[int, int]] = set()

    while True:
        print(f"Stats: {compute_stats(axiom_map)}")
        # print(f"non-edges: {len(list(non_edges))}")
        # print(f"non-edges: {non_edges}")
        choice = pick_non_looping_non_terminal_axiom(axiom_map)
        if choice is None:
            print("No reasonable candidate; finishing")
            break
        axiom, axiom_info = choice
        axiom_map.pop(axiom)
        newly_combined: List[
            Tuple[Kore.Axiom, AxiomInfo, AxiomInfo, Kore.Axiom, Kore.Axiom]
        ] = []
        negated_sides: Kore.Pattern = Kore.Top(rs.top_sort)
        vars_to_avoid: Set[Kore.EVar] = set()
        some_failed: bool = False
        # For each other axiom2
        for idx, (axiom2, axiom_info2) in enumerate(axiom_map.items()):
            if len(newly_combined) > treshold:
                break
            if axiom == axiom2:
                continue
            if axiom_info2.is_looping:
                continue
            print(f"Trying edge {(axiom_info.axiom_id,axiom_info2.axiom_id)}")
            # if (axiom_info.axiom_id,axiom_info2.axiom_id) in non_edges:
            #    print("Skipping a non-edge")
            # if axiom2 in axiom_info.non_successors:
            #    print("Filtering out an impossiblec combination")
            #    continue
            print(f"Combining with {idx}-th other")
            try:
                result = combine_rules(rs, axiom, axiom2, vars_to_avoid=vars_to_avoid)
            except pyk.kore.rpc.KoreClientError:
                print(f"Got an exception when combining axioms")
                print("Continuing as if the two axioms cannot be combined.")
                some_failed = True
                non_edges.add((axiom_info.axiom_id, axiom_info2.axiom_id))
                axiom_info.non_successors.append(axiom2)
                continue
            print(f"succeeded: {result is not None}")
            if result is None:
                some_failed = True
                non_edges.add((axiom_info.axiom_id, axiom_info2.axiom_id))
                axiom_info.non_successors.append(axiom2)
                continue
            combined, side_cond = result
            vars_to_avoid = vars_to_avoid.union(free_evars_of_pattern(side_cond))
            negated_sides = Kore.And(
                rs.top_sort, negated_sides, Kore.Not(rs.top_sort, side_cond)
            )
            newly_combined.append((combined, axiom_info, axiom_info2, axiom, axiom2))

        # if not some_failed:
        #    print("A suspicuous rule can be combined with any other one")
        #    print(rs.kprint.kore_to_pretty(axiom.pattern))

        if len(newly_combined) > treshold:
            print(
                f"Too many ({len(newly_combined)}) combinations - marking as exploding"
            )
            axiom_info.is_exploding = True
            axiom_map[axiom] = axiom_info
            continue

        resulting_lhs_before_simplification = Kore.And(
            rs.top_sort, get_lhs(axiom), negated_sides
        )
        # print(rs.kprint.kore_to_pretty(resulting_lhs_before_simplification))
        resulting_lhs = rs.simplify(resulting_lhs_before_simplification)
        if is_bottom(resulting_lhs):
            print(f"Residual lhs is bottom")
        else:
            # print(f"Residual lhs is not bottom: {rs.kprint.kore_to_pretty(resulting_lhs)}")
            print(f"Residual lhs is not bottom.")
            axiom_map[
                Kore.Axiom(
                    (), Kore.Rewrites(rs.top_sort, resulting_lhs, get_rhs(axiom)), ()
                )
            ] = AxiomInfo(
                axiom_id=next_id,
                is_initial=True,
                is_looping=False,
                is_terminal=True,
                non_successors=[],
                is_exploding=False,
            )
            next_id = next_id + 1

        for combined, axiom_info1, axiom_info2, axiom1, axiom2 in newly_combined:
            combined_id = next_id
            next_id = next_id + 1
            new_ai = AxiomInfo(
                axiom_id=combined_id,
                is_initial=axiom_info1.is_initial,
                is_looping=can_self_loop(rs, combined),
                is_terminal=axiom_info2.is_terminal,
                non_successors=axiom_info2.non_successors,
                is_exploding=axiom_info2.is_exploding,
            )
            # print(rs.kprint.kore_to_pretty(combined.pattern))
            axiom_map[combined] = new_ai
            ne1 = {
                (combined_id, to)
                for (fr, to) in non_edges
                if fr == axiom_info2.axiom_id
            }
            ne2 = {
                (fr, combined_id) for (fr, to) in non_edges if to == axiom_info.axiom_id
            }
            new_ne = ne1.union(ne2)
            # print(f"Added {len(list(new_ne))} non-edges")
            # print(f"Added {new_ne} non-edges")
            non_edges = non_edges.union(new_ne)

    return [(ax, ai.is_initial) for ax, ai in axiom_map.items()]
    # print(f"Resulting axioms: ({compute_stats(axiom_map)})")
    # for ax,ai in axiom_map.items():
    #     print(f"ai: {ai}")
    #     match ax:
    #         case Kore.Axiom(_, rewrite, _):
    #             print(rs.kprint.kore_to_pretty(rewrite))
    # return 0


def print_rewrite_axioms(
    rs: ReachabilitySystem, rewrite_axioms: List[Tuple[Kore.Axiom, bool]]
) -> None:
    for ax, b in rewrite_axioms:
        print(f"initial={b}, {rs.kprint.kore_to_pretty(ax.pattern)}")


def do_optimize(rs: ReachabilitySystem, args) -> int:
    with open(args["analysis_result"], mode="r") as fr:
        with open(args["output"], mode="w") as fw:
            axiom_list: List[Tuple[Kore.Axiom, bool]] = json_to_axiom_list(fr.read())
            new_axiom_list = optimize(
                rs, axiom_list, treshold=int(args["max_branching"])
            )
            fw.write(axiom_list_to_json(new_axiom_list))
    return 0


def do_print(rs: ReachabilitySystem, args) -> int:
    with open(args["input"], mode="r") as fr:
        axiom_list: List[Tuple[Kore.Axiom, bool]] = json_to_axiom_list(fr.read())
        print_rewrite_axioms(rs, axiom_list)
    return 0


# def do_mk_rcgraph(rs: ReachabilitySystem, args) -> int:
#    with open(args["store_rcg"], mode="w") as fw:
#        rcg: RCGraph = make_RCG_from_rs(rs)
#        fw.write(json.dumps(rcg.to_dict(), sort_keys=True, indent=True))
#    return 0


def create_argument_parser() -> argparse.ArgumentParser:
    argument_parser = argparse.ArgumentParser(
        prog="kaipy", description="A K abstract interpreter"
    )
    argument_parser.add_argument("-d", "--definition", required=True)
    argument_parser.add_argument("--print-rpc-logs", action="store_true")

    subparsers = argument_parser.add_subparsers(dest="command")

    subparser_mk_rcgraph = subparsers.add_parser(
        "mk-rcgraph", help="Create a Rule-Composition graph from the semantics"
    )
    subparser_mk_rcgraph.add_argument("--store-rcg", required=True)

    subparser_generate_analyzer = subparsers.add_parser(
        "generate-analyzer", help="Create an analyzer from given semantics"
    )
    subparser_generate_analyzer.add_argument("--analyzer", required=True)

    subparser_analyze = subparsers.add_parser(
        "analyze", help="Analyze given input program"
    )
    subparser_analyze.add_argument("--analyzer", required=True)
    subparser_analyze.add_argument("--input", required=True)
    subparser_analyze.add_argument("--output", required=True)

    subparser_optimize = subparsers.add_parser("optimize")
    subparser_optimize.add_argument("--analysis-result", required=True)
    subparser_optimize.add_argument("--max-branching", required=True)
    subparser_optimize.add_argument("--output", required=True)

    subparser_print = subparsers.add_parser("print")
    subparser_print.add_argument("--input", required=True)

    return argument_parser


def main():
    argument_parser = create_argument_parser()
    args = vars(argument_parser.parse_args())
    # print(f"args: {args}")
    logging.basicConfig(encoding="utf-8", level=logging.DEBUG)
    if not args["print_rpc_logs"]:
        logging.getLogger("pyk.kore.rpc").disabled = True
    logging.getLogger("pyk.ktool.kprint").disabled = True
    logging.getLogger("pyk.kast.inner").disabled = True

    kk = KompiledKore(definition_dir=Path(args["definition"]))
    with KompiledDefinitionWrapper(
        managed_kompiled_kore=TriviallyManagedKompiledKore(kk)
    ) as kdw:
        with ReachabilitySystem(
            kore_rpc_args=(),
            connect_to_port=None,
            kdw=kdw,
        ) as rs:
            if args["command"] == "analyze":
                retval = analyze(rs, args)
            # elif args["command"] == "mk-rcgraph":
            #    retval = do_mk_rcgraph(rs, args)
            elif args["command"] == "generate-analyzer":
                retval = generate_analyzer(rs, args)
            elif args["command"] == "optimize":
                retval = do_optimize(rs, args)
            elif args["command"] == "print":
                retval = do_print(rs, args)
            else:
                retval = 1

        sys.exit(retval)
