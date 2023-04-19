import argparse
import logging
import sys
import json
import argparse
from dataclasses import dataclass
import frozendict

from pathlib import Path
import networkx as nx # type: ignore


from typing import (
    Any,
    Final,
    Iterable,
    Optional,
    IO,
    List,
    Dict,
    Set,
    Tuple,
    Mapping,
    Union,
    Callable,
)


from pyk.ktool import krun
from pyk.kore.parser import KoreParser
import pyk.kore.rpc
import pyk.kore.syntax as Kore

from .kcommands import KRUN_COMMAND
from .ReachabilitySystem import ReachabilitySystem
from .kore_utils import (
    free_evars_of_pattern,
    get_fresh_evars_with_sorts,
    rename_vars,
    axiom_uuid,
    axiom_label,
    extract_equalities_and_rest_from_witness,
    extract_equalities_from_witness,
    some_subpatterns_of,
)

def get_input_kore(definition_dir: Path, program: Path) -> Kore.Pattern:
    result = krun._krun(
        command=(KRUN_COMMAND),
        input_file=Path(program),
        definition_dir=definition_dir,
        output=krun.KRunOutput.KORE,
        depth=0,
        cmap={'ARGS': r'ARGS:SortList{}'},
        pmap={'ARGS': 'cat'}
    )
    krun.KRun._check_return_code(result.returncode,0)
    parser = KoreParser(result.stdout)
    res = parser.pattern()
    assert parser.eof
    return res

def compute_renaming(patt: Kore.Pattern, vars_to_avoid: List[Kore.EVar]) -> Dict[str, str]:
    vars_to_rename = list(free_evars_of_pattern(patt))
    vars_to_avoid = vars_to_rename + vars_to_avoid
    new_vars = get_fresh_evars_with_sorts(avoid=list(vars_to_avoid), sorts=list(map(lambda ev: ev.sort, vars_to_rename)))
    vars_fr : List[str] = list(map(lambda e: e.name, vars_to_rename))
    vars_to : List[str] = list(map(lambda e: e.name, new_vars))
    renaming = dict(zip(vars_fr, vars_to))
    return renaming

def compute_conjunction(rs: ReachabilitySystem, a: Kore.Pattern, b: Kore.Pattern) -> Kore.Pattern:
    return rs.kcs.client.simplify(Kore.And(rs.top_sort, a, b))

def compute_match(rs: ReachabilitySystem, patt_from: Kore.Pattern, axiom: Kore.Rewrites) -> Tuple[Kore.Pattern,Dict[str,str]]:
    vars_to_rename = list(free_evars_of_pattern(axiom.left))
    vars_to_avoid = vars_to_rename + list(free_evars_of_pattern(patt_from))
    new_vars = get_fresh_evars_with_sorts(avoid=list(vars_to_avoid), sorts=list(map(lambda ev: ev.sort, vars_to_rename)))
    vars_fr : List[str] = list(map(lambda e: e.name, vars_to_rename))
    vars_to : List[str] = list(map(lambda e: e.name, new_vars))
    renaming = dict(zip(vars_fr, vars_to))
    axiom_left = rename_vars(renaming, axiom.left)
    lhs_match = compute_conjunction(rs, patt_from, axiom_left)
    return lhs_match,renaming

def is_bottom(pattern: Kore.Pattern) -> bool:
    match pattern:
        case Kore.Bottom(_):
            return True
    return False

def may_transit(rs: ReachabilitySystem, patt_from: Kore.Pattern, axiom: Kore.Rewrites) -> bool:
    lhs_match,_ = compute_match(rs, patt_from, axiom)
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
                'pattern': self.pattern.dict,
                'original_rule_label': self.original_rule_label,
                'applicable_rules': self.applicable_rules,
            }
        
        @staticmethod
        def from_dict(dct: Dict[str, Any]):
            return SemanticsPreGraph.Node(Kore.Pattern.from_dict(dct['pattern']), dct['original_rule_label'], dct['applicable_rules'])

    
    nodes: List[Node]

    @property
    def dict(self) -> Dict[str, Any]:
        return {'nodes': [ n.dict for n in self.nodes]}

    @staticmethod
    def from_dict(dct: Dict[str, Any]):
        return SemanticsPreGraph([SemanticsPreGraph.Node.from_dict(n) for n in dct['nodes']])

def compute_semantics_pregraph(rs: ReachabilitySystem) -> SemanticsPreGraph:
    nodes: List[SemanticsPreGraph.Node] = []

    for axiom in rs.rewrite_rules:
        match axiom:
            case Kore.Axiom(_, Kore.Rewrites(_, lhs, _), _):
                pattern: Kore.Pattern = lhs
                original_rule_label: str = axiom_label(axiom)
                applicable_rules: List[str] = []
                for rule_to_apply in rs.rewrite_rules:
                    match rule_to_apply:
                        case Kore.Axiom(_, Kore.Rewrites(_, _, _) as r, _):
                            if may_transit(rs, pattern, r):
                                applicable_rule: str = axiom_label(rule_to_apply)
                                print(f"May transit from {original_rule_label} using {applicable_rule} ")
                                applicable_rules.append(applicable_rule)
                nodes.append(SemanticsPreGraph.Node(pattern, original_rule_label, applicable_rules))

    return SemanticsPreGraph(nodes)

@dataclass(frozen=True)
class Substitution:
    mapping: Mapping[Kore.EVar, Kore.Pattern]

def make_conjunction(rs: ReachabilitySystem, l: List[Kore.Pattern]) -> Kore.Pattern:
    result: Kore.Pattern = Kore.Top(rs.top_sort)
    for x in l:
        result = Kore.And(rs.top_sort, result, x)
    return result

# TODO use make_conjunction
def mapping_to_pattern(rs: ReachabilitySystem, m: Mapping[Kore.EVar, Kore.Pattern]) -> Kore.Pattern:
    result: Kore.Pattern = Kore.Top(rs.top_sort)
    for lhs,rhs in m.items():
        result = Kore.And(rs.top_sort, result, Kore.Equals(lhs.sort, rs.top_sort, lhs, rhs))
    return result


def subst_to_pattern(rs: ReachabilitySystem, subst: Substitution) -> Kore.Pattern:
    return mapping_to_pattern(rs, subst.mapping)

# The graph on which we do the analysis
class SCFG:

    @dataclass(frozen=True)
    class Node:
        pattern: Kore.Pattern
        original_rule_label: str
        applicable_rules: Tuple[str,...]
    
    @dataclass
    class NodeRuleInfo:
        substitutions: Set[Substitution]
        new_substitutions: Set[Substitution]

    rs: ReachabilitySystem
    nodes: Set[Node]    
    node_rule_info: Dict[Tuple[Node, str],NodeRuleInfo]
    #graph: nx.Graph

    def __init__(self, rs: ReachabilitySystem, spg: SemanticsPreGraph):
        self.rs = rs
        self.graph = nx.Graph()
        self.nodes = {SCFG.Node(pattern=node.pattern, original_rule_label=node.original_rule_label, applicable_rules=tuple(node.applicable_rules)) for node in spg.nodes }
        self.node_rule_info = {}
        for n in self.nodes:
            for rl in n.applicable_rules:
                self.node_rule_info[(n,rl)] = SCFG.NodeRuleInfo(set(), set())
    
    def break_pattern(self, pattern: Kore.Pattern, normalize: Callable[[Substitution],Substitution]):
        input_kore_renamed: Kore.Pattern = rename_vars(compute_renaming(pattern, list(self.rs.rules_variables)), pattern)
        #print(f"Breaking {self.rs.kprint.kore_to_pretty(input_kore_renamed)}")
        #print(f"Breaking: {input_kore_renamed.text}")
        for node in self.nodes:
            for ruleid in node.applicable_rules:
                rule: Kore.Axiom = self.rs.rule_by_id(ruleid)
                match rule:
                    case Kore.Axiom(_, Kore.Rewrites(_, lhs, _) as rewrites, _):
                        m = compute_conjunction(self.rs, input_kore_renamed, lhs)
                        if is_bottom(m):
                            continue
                        print(f"{node.original_rule_label}.{ruleid}:")
                        #print(f"Matched rule's lhs: {self.rs.kprint.kore_to_pretty(lhs)}")
                        eqs = extract_equalities_from_witness({ v.name for v in free_evars_of_pattern(rewrites)}, m)
                        #print(self.rs.kprint.kore_to_pretty(m))
                        
                        substitution = Substitution(frozendict.frozendict(eqs))
                        normalized_substitution = normalize(substitution)
                        if normalized_substitution not in self.node_rule_info[(node, ruleid)].substitutions:
                            #normalized_substitution_pretty = dict((k,self.rs.kprint.kore_to_pretty(v)) for k,v in normalized_substitution.mapping.items())
                            #print(f"New substitution: {normalized_substitution_pretty}")
                            self.node_rule_info[(node, ruleid)].substitutions.add(normalized_substitution)
                            self.node_rule_info[(node, ruleid)].new_substitutions.add(normalized_substitution)
                            #if not bool(normalized_substitution.mapping):
                                #print(f"**Empty substitution for pattern {self.rs.kprint.kore_to_pretty(input_kore_renamed)}")
                                #print(f"** Original substitution: {substitution}")
                                #print(f"** Conjunction: {self.rs.kprint.kore_to_pretty(m)}")
                        #eqs_pretty = dict((k,self.rs.kprint.kore_to_pretty(v)) for k,v in eqs.items())
                        #print(f"eqs_pretty: {eqs_pretty}")

    def choose(self) -> Optional[Tuple[Node,str,Substitution]]:
        for (node, ruleid),nri in self.node_rule_info.items():
            if list(nri.new_substitutions) != []:
                substitution = list(nri.new_substitutions)[0]
                nri.new_substitutions.remove(substitution)
                return (node, ruleid, substitution)
        return None

# TODO maybe we could allow constants of sort Bool, since there are only two of them
def is_linear_kseq_combination_of(subpatterns: List[Kore.Pattern], candidate: Kore.Pattern) -> Tuple[bool, List[Kore.Pattern]]:
    if candidate in subpatterns:
        return True,[candidate]
    
    match candidate:
        case Kore.App('dotk', _, _):
            return (True,[])
        case Kore.App('inj', _, (arg,)):
            return is_linear_kseq_combination_of(subpatterns, arg)
        case Kore.App('kseq', _, (arg1, arg2)):
            b1,u1 = is_linear_kseq_combination_of(subpatterns, arg1)
            if not b1:
                return (False,[])
            b2,u2 = is_linear_kseq_combination_of([s for s in subpatterns if s not in u1], arg2)
            if not b2:
                return (False,[])
            return (True, (u1+u2))
    return False,[]

def make_normalizer(pattern: Kore.Pattern) -> Callable[[Substitution],Substitution]:
    subpatterns = [s for s in some_subpatterns_of(pattern) if type(s) is not Kore.EVar]
    #print(subpatterns)

    def is_there(candidate: Kore.Pattern) -> bool:
        b,u = is_linear_kseq_combination_of(subpatterns, candidate)
        if b:
            return True
        print(f"Filtering out {candidate}")
        return False

    def f(s: Substitution):
        return Substitution(frozendict.frozendict({k : v for k,v in s.mapping.items() if is_there(v)}))

    return f

def perform_analysis(rs: ReachabilitySystem, spg, normalize, input_kore):
    scfg = SCFG(rs, spg)
    scfg.break_pattern(input_kore, normalize=normalize)
    while(True):
        x = scfg.choose()
        if x is None:
            return scfg
        (node,ruleid,substitution) = x
        print(f"Choosing node {node.original_rule_label}")
        sp = subst_to_pattern(rs, substitution)
        patt: Kore.Pattern = Kore.And(rs.top_sort, node.pattern, sp)
        #print(f"pattern: {patt.text}")
        exec_result = rs.kcs.client.execute(pattern=patt, max_depth=1)
        
        next_patterns: List[Kore.Pattern] = [exec_result.state.kore] if exec_result.next_states is None else [s.kore for s in exec_result.next_states]
        print(f"Has {len(next_patterns)} successors")
        for new_pattern in next_patterns:
            #print("Breaking a pattern")
            scfg.break_pattern(new_pattern, normalize=normalize)
    return scfg

def print_analyze_results(scfg: SCFG):
    print("****** ANALYSIS RESULTS *********")
    for node in scfg.nodes:
        for ruleid in node.applicable_rules:
            ri = scfg.node_rule_info[(node, ruleid)]
            print(f"{node.original_rule_label}/{ruleid}")
            for sub in ri.substitutions:
                print(f"  {sub}")
    
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
            next_patterns: List[Kore.Pattern] = [exec_result.state.kore] if exec_result.next_states is None else [s.kore for s in exec_result.next_states]    
            return next_patterns

def get_lhs(rule: Kore.Axiom) -> Kore.Pattern:
    match rule:
        case Kore.Axiom(vs, Kore.Rewrites(sort, lhs, rhs) as rewrites, _):
            return lhs
    raise RuntimeError("Not a rewrite rule")

def get_rhs(rule: Kore.Axiom) -> Kore.Pattern:
    match rule:
        case Kore.Axiom(vs, Kore.Rewrites(sort, lhs, rhs) as rewrites, _):
            return rhs
    raise RuntimeError("Not a rewrite rule")

def can_self_loop(rs: ReachabilitySystem, rule: Kore.Axiom):
    match rule:
        case Kore.Axiom(vs, Kore.Rewrites(sort, lhs, rhs) as rewrites, _):
            lhs_renamed: Kore.Pattern = rename_vars(compute_renaming(lhs, list(free_evars_of_pattern(lhs))), lhs)
            if not is_bottom(rs.kcs.client.simplify(Kore.And(rs.top_sort, rhs, lhs))):
                return True
            return False

    raise RuntimeError("Not a rewrite rule")

def to_axiom_list(rs: ReachabilitySystem, scfg: SCFG) -> List[Kore.Axiom]:
    rewrite_axioms: List[Kore.Axiom] = []
    for node in scfg.nodes:
        if (len(node.applicable_rules) != 1):
            print(f"warn: applicable rules = {node.applicable_rules} for {node.original_rule_label}")
        for rule_id in node.applicable_rules:
            rule: Kore.Axiom = rs.rule_by_id(rule_id)
            match rule:
                case Kore.Axiom(vs, Kore.Rewrites(sort, lhs, rhs) as rewrites, _):
                    ri = scfg.node_rule_info[(node, rule_id)]
                    for sub in ri.substitutions:
                        rewrite_axioms.append(Kore.Axiom(vs, Kore.Rewrites(sort, Kore.And(sort, lhs, subst_to_pattern(rs, sub)), rhs),()))
    return rewrite_axioms

def axiom_list_to_json(rewrite_axioms: List[Kore.Axiom]) -> str:
    return json.dumps([a.text for a in rewrite_axioms])

def parse_axiom(s: str) -> Kore.Axiom:
    parser = KoreParser(s)
    return parser.axiom()

def json_to_axiom_list(s: str) -> List[Kore.Axiom]:
    return [parse_axiom(a) for a in json.loads(s)]

def analyze(rs: ReachabilitySystem, args) -> int:
    with open(args['analyzer'], mode='r') as fr:
        jsa = json.load(fr)
    spg: SemanticsPreGraph = SemanticsPreGraph.from_dict(jsa)
    input_kore: Kore.Pattern = get_input_kore(Path(args['definition']), Path(args['input']))

    input_kore_simplified = rs.kcs.client.simplify(input_kore)
    normalize = make_normalizer(input_kore_simplified)
    scfg = perform_analysis(rs, spg, normalize, input_kore_simplified)
    print_analyze_results(scfg)
    axiom_list: List[Kore.Axiom] = to_axiom_list(rs, scfg)
    with open(args['output'], mode='w') as fw:
        fw.write(axiom_list_to_json(axiom_list))

    return 0

def generate_analyzer(rs: ReachabilitySystem, args) -> int:
    with open(args['analyzer'], mode="w") as fw:
        semantics_pregraph = compute_semantics_pregraph(rs)
        fw.write(json.dumps(semantics_pregraph.dict))
    return 0

def filter_out_predicates(phi: Kore.Pattern) -> Tuple[Optional[Kore.Pattern], List[Kore.Pattern]]:
    if issubclass(type(phi), Kore.MLPred):
        return None,[phi]
    match phi:
        case Kore.And(sort, left, right):
            lf,ps1 = filter_out_predicates(left)
            rf,ps2 = filter_out_predicates(right)
            if lf is None:
                return rf,(ps1+ps2)
            if rf is None:
                return lf,(ps1+ps2)
            return Kore.And(sort, lf, rf),(ps1+ps2)
        case _:
            return phi,[]

def get_predicates(phi: Kore.Pattern) -> List[Kore.Pattern]:
    _, preds = filter_out_predicates(phi)
    return preds

def cleanup_eqs(rs: ReachabilitySystem, main_part: Kore.Pattern, eqs: Dict[Kore.EVar, Kore.Pattern]) -> Kore.Pattern:
    fvs = free_evars_of_pattern(main_part)
    evs2 = {k:v for k,v in eqs.items() if (k in fvs)}
    evs2_p = mapping_to_pattern(rs, evs2)
    return evs2_p

def cleanup_pattern(rs: ReachabilitySystem, phi: Kore.Pattern) -> Kore.Pattern:
    main_part,_ = filter_out_predicates(phi)
    assert(main_part is not None)
    fvphi = free_evars_of_pattern(phi)
    eqs, rest = extract_equalities_and_rest_from_witness({v.name for v in fvphi}, phi)
    evs2_p = cleanup_eqs(rs, main_part, eqs)
    if rest is None:
        return evs2_p
    return Kore.And(rs.top_sort, rest, evs2_p)

# TODO duplication with combine_rules
def rules_can_consecute(rs: ReachabilitySystem, first_rule: Kore.Axiom, second_rule: Kore.Axiom) -> bool:
    curr_lhs = get_lhs(first_rule)
    # For some reason, we can se a non-normalized curr_lhs here.
    # Maybe we are doing something wrong in the analysis phase?
    curr_lhs = rs.kcs.client.simplify(curr_lhs)
    curr_rhs = get_rhs(first_rule)
    other_lhs = get_lhs(second_rule)
    other_renaming = compute_renaming(other_lhs, list(free_evars_of_pattern(curr_rhs)))
    other_lhs_renamed: Kore.Pattern = rename_vars(other_renaming, other_lhs)
    #simplified_conj = rs.kcs.client.simplify(Kore.And(rs.top_sort, curr_rhs, other_lhs_renamed))
    simplified_conj = rs.kcs.client.simplify(Kore.And(rs.top_sort, Kore.And(rs.top_sort, curr_rhs, make_conjunction(rs, get_predicates(curr_lhs))), other_lhs_renamed))
    return not is_bottom(simplified_conj)

def exactly_one_can_consecute(rs: ReachabilitySystem, axiom: Kore.Axiom, other: List[Kore.Axiom]) -> Optional[Kore.Axiom]:
    cnt = 0
    the_one: Optional[Kore.Axiom] = None
    for a in other:
        if rules_can_consecute(rs, axiom, a):
            cnt = cnt + 1
            if cnt >= 2:
                return None
            the_one = a
    return the_one

def combine_rules(rs: ReachabilitySystem, first_rule: Kore.Axiom, second_rule: Kore.Axiom, vars_to_avoid: Set[Kore.EVar]) -> Optional[Tuple[Kore.Axiom, Kore.Pattern]]:
    curr_lhs = get_lhs(first_rule)
    curr_lhs = rs.kcs.client.simplify(curr_lhs)
    curr_rhs = get_rhs(first_rule)
    other_lhs = get_lhs(second_rule)
    other_rhs = get_rhs(second_rule)
    vars_to_avoid = vars_to_avoid.union(free_evars_of_pattern(curr_rhs)).union(free_evars_of_pattern(curr_lhs))
    other_renaming = compute_renaming(other_lhs, list(vars_to_avoid))
    other_lhs_renamed: Kore.Pattern = rename_vars(other_renaming, other_lhs)
    other_rhs_renamed: Kore.Pattern = rename_vars(other_renaming, other_rhs)
    #simplified_conj = rs.kcs.client.simplify(Kore.And(rs.top_sort, curr_rhs, other_lhs_renamed))
    simplified_conj = rs.kcs.client.simplify(Kore.And(rs.top_sort, Kore.And(rs.top_sort, curr_rhs, make_conjunction(rs, get_predicates(curr_lhs))), other_lhs_renamed))
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
    eqs1_p = mapping_to_pattern(rs, eqs1)
    side_cond: Kore.Pattern = Kore.And(rs.top_sort, eqs1_p, preds1_conj)
    #print(f"preds1_conj: {rs.kprint.kore_to_pretty(preds1_conj)}")
    new_lhs = rs.kcs.client.simplify(Kore.And(rs.top_sort, curr_lhs, side_cond))
    if is_bottom(new_lhs):
        print(f"not bottom: {rs.kprint.kore_to_pretty(simplified_conj)}")
        print(f"Axiom1 lhs: {rs.kprint.kore_to_pretty(curr_lhs)}")
        print(f"Axiom1 rhs: {rs.kprint.kore_to_pretty(curr_rhs)}")
        print(f"Axiom2 lhs {rs.kprint.kore_to_pretty(other_lhs_renamed)}")
        print(f"Axiom2 rhs {rs.kprint.kore_to_pretty(other_rhs_renamed)}")
        raise RuntimeError("new_lhs is unexpectedly bottom.")
    #new_lhs = rs.kcs.client.simplify(Kore.And(rs.top_sort, curr_lhs, mapping_to_pattern(rs, eqs1))) # FIXME I know this is not enough
    new_rhs = rs.kcs.client.simplify(Kore.And(rs.top_sort, other_rhs_renamed, mapping_to_pattern(rs, eqs2)))
    # After the simplification, the intermediate variables (from 'other_renaming') should disappear
    #print(f"New lhs {rs.kprint.kore_to_pretty(new_lhs)}")
    #print(f"New rhs {rs.kprint.kore_to_pretty(new_rhs)}")
    new_lhs_clean = cleanup_pattern(rs, new_lhs)

    new_rhs_clean = cleanup_pattern(rs, new_rhs)
    #print(f"New lhs clean {rs.kprint.kore_to_pretty(new_lhs_clean)}")
    #print(f"New rhs clean {rs.kprint.kore_to_pretty(new_rhs_clean)}")
    rewrite = Kore.Rewrites(rs.top_sort, new_lhs_clean, new_rhs_clean)
    #print(f"rewrite: {rs.kprint.kore_to_pretty(rewrite)}")
    return Kore.Axiom((), rewrite, ()),side_cond

def choose_axiom_with_only_single_successive_axiom(rs: ReachabilitySystem, looping_axioms, non_looping_axioms):
    for axiom in non_looping_axioms:
        other_axioms = looping_axioms = [a for a in non_looping_axioms if a != axiom]
        the_one = exactly_one_can_consecute(rs, axiom, other_axioms)
        if the_one is not None:
            return axiom,the_one,other_axioms
    return None

@dataclass
class AxiomInfo:
    axiom_id: int
    is_looping: bool
    is_terminal: bool
    is_exploding: bool
    non_successors: List[Kore.Axiom]

def pick_non_looping_non_terminal_axiom(axioms: Mapping[Kore.Axiom, AxiomInfo]) -> Optional[Tuple[Kore.Axiom, AxiomInfo]]:
    non_looping = [(ax, ai) for ax,ai in axioms.items() if (not ai.is_looping) and (not ai.is_terminal) and (not ai.is_exploding)]
    if len(non_looping) >= 1:
        return non_looping[0]
    return None

@dataclass
class AxiomStats:
    total: int
    n_looping: int
    n_terminal: int
    n_exploding: int

def compute_stats(axioms: Mapping[Kore.Axiom, AxiomInfo]) -> AxiomStats:
    stats = AxiomStats(0,0,0,0)
    for _,ai in axioms.items():
        stats.total = stats.total + 1
        if ai.is_looping:
            stats.n_looping = stats.n_looping + 1
        if ai.is_terminal:
            stats.n_terminal = stats.n_terminal + 1
        if ai.is_exploding:
            stats.n_exploding = stats.n_exploding + 1
    return stats

def optimize(rs: ReachabilitySystem, rewrite_axioms: List[Kore.Axiom], treshold=2) -> List[Kore.Axiom]:
    print(f"Total axioms: {len(rewrite_axioms)} (original was: {len(rs.rewrite_rules)})")

    axiom_map = { ax: AxiomInfo(axiom_id=i, is_looping=can_self_loop(rs, ax), is_terminal=False, non_successors=[], is_exploding=False) for i,ax in enumerate(rewrite_axioms)}
    next_id = 1 + len(rewrite_axioms)

    non_edges : Set[Tuple[int,int]] = set()

    while True:
        print(f"Stats: {compute_stats(axiom_map)}")
        print(f"non-edges: {len(list(non_edges))}")
        print(f"non-edges: {non_edges}")
        choice = pick_non_looping_non_terminal_axiom(axiom_map)
        if choice is None:
            print("No reasonable candidate; finishing")
            break
        axiom,axiom_info = choice
        axiom_map.pop(axiom)
        newly_combined: List[Tuple[Kore.Axiom, AxiomInfo, AxiomInfo, Kore.Axiom, Kore.Axiom]] = []
        negated_sides: Kore.Pattern = Kore.Top(rs.top_sort)
        vars_to_avoid: Set[Kore.EVar] = set()
        some_failed: bool = False
        # For each other axiom2
        for idx,(axiom2,axiom_info2) in enumerate(axiom_map.items()):
            if (len(newly_combined) > treshold):
                break
            if axiom == axiom2:
                continue
            if axiom_info2.is_looping:
                continue
            print(f"Trying edge {(axiom_info.axiom_id,axiom_info2.axiom_id)}")
            if (axiom_info.axiom_id,axiom_info2.axiom_id) in non_edges:
                print("Skipping a non-edge")
            if axiom2 in axiom_info.non_successors:
                print("Filtering out an impossiblec combination")
                continue
            print(f"Combining with {idx}-th other")
            try:
                result = combine_rules(rs, axiom, axiom2, vars_to_avoid=vars_to_avoid)
            except pyk.kore.rpc.KoreClientError:
                print(f"Got an exception when combining axioms")
                print("Continuing as if the two axioms cannot be combined.")
                some_failed = True
                non_edges.add((axiom_info.axiom_id,axiom_info2.axiom_id))
                axiom_info.non_successors.append(axiom2)
                continue
            print(f"succeeded: {result is not None}")
            if result is None:
                some_failed = True
                non_edges.add((axiom_info.axiom_id,axiom_info2.axiom_id))
                axiom_info.non_successors.append(axiom2)
                continue
            combined,side_cond = result
            vars_to_avoid = vars_to_avoid.union(free_evars_of_pattern(side_cond))
            negated_sides = Kore.And(rs.top_sort, negated_sides, Kore.Not(rs.top_sort, side_cond))
            newly_combined.append((combined,axiom_info,axiom_info2,axiom,axiom2))

        #if not some_failed:
        #    print("A suspicuous rule can be combined with any other one")
        #    print(rs.kprint.kore_to_pretty(axiom.pattern))

        if len(newly_combined) > treshold:
            print(f"Too many ({len(newly_combined)}) combinations - marking as exploding")
            axiom_info.is_exploding = True
            axiom_map[axiom] = axiom_info
            continue

        resulting_lhs_before_simplification = Kore.And(rs.top_sort, get_lhs(axiom), negated_sides)
        #print(rs.kprint.kore_to_pretty(resulting_lhs_before_simplification))
        resulting_lhs = rs.kcs.client.simplify(resulting_lhs_before_simplification)
        if is_bottom(resulting_lhs):
            print(f"Residual lhs is bottom")
        else:
            #print(f"Residual lhs is not bottom: {rs.kprint.kore_to_pretty(resulting_lhs)}")
            print(f"Residual lhs is not bottom:")
            axiom_map[Kore.Axiom((), Kore.Rewrites(rs.top_sort, resulting_lhs, get_rhs(axiom)), ())] = AxiomInfo(
                axiom_id=next_id,
                is_looping=False,
                is_terminal=True,
                non_successors=[],
                is_exploding=False,
            )
            next_id = next_id + 1

        for combined,axiom_info1,axiom_info2,axiom1,axiom2 in newly_combined:
            combined_id = next_id
            next_id = next_id + 1
            new_ai = AxiomInfo(
                axiom_id=combined_id,
                is_looping=can_self_loop(rs, combined),
                is_terminal=axiom_info2.is_terminal,
                non_successors=axiom_info2.non_successors,
                is_exploding=axiom_info2.is_exploding,
            )
            axiom_map[combined] = new_ai
            ne1 = {(combined_id, to) for (fr, to) in non_edges if fr == axiom_info2.axiom_id}
            ne2 = {(fr, combined_id) for (fr, to) in non_edges if to == axiom_info.axiom_id}
            new_ne = ne1.union(ne2)
            print(f"Added {len(list(new_ne))} non-edges")
            print(f"Added {new_ne} non-edges")
            non_edges = non_edges.union(new_ne)

    return [ax for ax,_ in axiom_map.items()]
    # print(f"Resulting axioms: ({compute_stats(axiom_map)})")
    # for ax,ai in axiom_map.items():
    #     print(f"ai: {ai}")
    #     match ax:
    #         case Kore.Axiom(_, rewrite, _):
    #             print(rs.kprint.kore_to_pretty(rewrite))
    #return 0

def print_rewrite_axioms(rs: ReachabilitySystem, rewrite_axioms: List[Kore.Axiom]) -> None:
    for ax in rewrite_axioms:
        print(rs.kprint.kore_to_pretty(ax.pattern))

def do_optimize(rs: ReachabilitySystem, args) -> int:
    with open(args['analysis_result'], mode="r") as fr:
        with open(args['output'], mode="w") as fw:
            axiom_list : List[Kore.Axiom] = json_to_axiom_list(fr.read())
            new_axiom_list = optimize(rs, axiom_list, treshold=int(args['max_branching']))
            fw.write(axiom_list_to_json(new_axiom_list))
    return 0

def do_print(rs: ReachabilitySystem, args) -> int:
    with open(args['input'], mode="r") as fr:
        axiom_list : List[Kore.Axiom] = json_to_axiom_list(fr.read())
        print_rewrite_axioms(rs, axiom_list)
    return 0

def create_argument_parser() -> argparse.ArgumentParser:
    argument_parser = argparse.ArgumentParser(
        prog="kaipy",
        description="A K abstract interpreter"
    )
    argument_parser.add_argument('-d', '--definition', required=True)

    subparsers = argument_parser.add_subparsers(dest='command')
    
    subparser_generate_analyzer = subparsers.add_parser('generate-analyzer', help='Create an analyzer from given semantics')
    subparser_generate_analyzer.add_argument('--analyzer', required=True)

    subparser_analyze = subparsers.add_parser('analyze', help='Analyze given input program')
    subparser_analyze.add_argument('--analyzer', required=True)
    subparser_analyze.add_argument('--input', required=True)
    subparser_analyze.add_argument('--output', required=True)

    subparser_optimize = subparsers.add_parser('optimize')
    subparser_optimize.add_argument('--analysis-result', required=True)
    subparser_optimize.add_argument('--max-branching', required=True)
    subparser_optimize.add_argument('--output', required=True)

    subparser_print = subparsers.add_parser('print')
    subparser_print.add_argument('--input', required=True)

    return argument_parser


def main():
    argument_parser = create_argument_parser()
    args = vars(argument_parser.parse_args())
    #print(f"args: {args}")
    logging.basicConfig(encoding='utf-8', level=logging.DEBUG)
    logging.getLogger('pyk.kore.rpc').disabled = True
    logging.getLogger('pyk.ktool.kprint').disabled = True
    logging.getLogger('pyk.kast.inner').disabled = True 
    

    with ReachabilitySystem(
        definition_dir=Path(args['definition']), 
        kore_rpc_args=(), 
        connect_to_port=None,
        ) as rs:

        if args['command'] == 'analyze':
            retval = analyze(rs, args)
        elif args['command'] == 'generate-analyzer':
            retval = generate_analyzer(rs, args)
        elif args['command'] == 'optimize':
            retval = do_optimize(rs, args)
        elif args['command'] == 'print':
            retval = do_print(rs, args)
        else:
            retval = 1
    
    sys.exit(retval)
    
