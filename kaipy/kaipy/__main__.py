import argparse
import logging
import sys
import json
import argparse
from dataclasses import dataclass

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
)


from pyk.ktool import krun
from pyk.kore.parser import KoreParser
import pyk.kore.syntax as Kore

from .kcommands import KRUN_COMMAND
from .ReachabilitySystem import ReachabilitySystem
from .kore_utils import (
    free_evars_of_pattern,
    get_fresh_evars_with_sorts,
    rename_vars,
    axiom_uuid,
    axiom_label,
    extract_equalities_from_witness,
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

def compute_match(rs: ReachabilitySystem, patt_from: Kore.Pattern, axiom: Kore.Rewrites) -> Tuple[Kore.Pattern,Dict[str,str]]:
    vars_to_rename = list(free_evars_of_pattern(axiom.left))
    vars_to_avoid = vars_to_rename + list(free_evars_of_pattern(patt_from))
    new_vars = get_fresh_evars_with_sorts(avoid=list(vars_to_avoid), sorts=list(map(lambda ev: ev.sort, vars_to_rename)))
    vars_fr : List[str] = list(map(lambda e: e.name, vars_to_rename))
    vars_to : List[str] = list(map(lambda e: e.name, new_vars))
    renaming = dict(zip(vars_fr, vars_to))
    axiom_left = rename_vars(renaming, axiom.left)
    lhs_match = rs.kcs.client.simplify(Kore.And(rs.top_sort, patt_from, axiom_left))
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
                'pattern': self.pattern.json,
                'original_rule_label': self.original_rule_label,
                'applicable_rules': self.applicable_rules,
            }
        
        @staticmethod
        def from_dict(dct: Dict[str, Any]):
            return SemanticsPreGraph.Node(dct['pattern'], dct['original_rule_label'], dct['applicable_rules'])

    
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


@dataclass
class Substitution:
    mapping: Dict[Kore.EVar, Kore.Pattern]

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

    rs: ReachabilitySystem
    nodes: Set[Node]    
    node_rule_info: Dict[Tuple[Node, str],NodeRuleInfo]
    #graph: nx.Graph

    def __init__(self, rs: ReachabilitySystem, spg: SemanticsPreGraph):
        self.rs = rs
        self.graph = nx.Graph()
        self.nodes = {SCFG.Node(node.pattern, node.original_rule_label, tuple(node.applicable_rules)) for node in spg.nodes }
        self.node_rule_info = {}
        #for node in spg.nodes:
        #    #applicable_rules: Tuple[Kore.Axiom,...] = tuple(rs.rule_by_id(ruleid) for ruleid in node.applicable_rules)
        #    applicable_rules = node.applicable_rules
    
    def break_pattern(self, pattern: Kore.Pattern):
        for node in self.nodes:
            for ruleid in node.applicable_rules:
                rule: Kore.Axiom = self.rs.rule_by_id(ruleid)
                match rule:
                    case Kore.Axiom(_, Kore.Rewrites(_, lhs, _) as rewrites, _):
                        m,renaming = compute_match(self.rs, pattern, rewrites)
                        if is_bottom(m):
                            continue
                        # Currently we rename variables in each rule as we try to apply it.
                        # It would be much better if we instead renamed the (usually only one)
                        # free variable of the input pattern (that is, ARGS for IMP).
                        # Because the renaming we have may still cause problems, because if a rule has a variable ARGS,
                        # it may be mapped to a term containing ARGS in the substitution...
                        print(f"{node.original_rule_label}.{ruleid}: renaming {renaming}")
                        eqs = extract_equalities_from_witness(set(renaming.values()), m)
                        renaming_back = dict((v,k) for k,v in renaming.items())
                        print(self.rs.kprint.kore_to_pretty(m))
                        eqs_renamed = dict((Kore.EVar(renaming_back[renamed_var.name], renamed_var.sort), pattern) for renamed_var, pattern in eqs.items())
                        substitution = Substitution(eqs_renamed)
                        print(f"eqs: {eqs}")
                        eqs_pretty = dict((k,self.rs.kprint.kore_to_pretty(v)) for k,v in eqs_renamed.items())
                        print(f"eqs_pretty: {eqs_pretty}")
                        #self.rs.kcs.client.implies()


def analyze(rs: ReachabilitySystem, args) -> int:
    with open(args['analyzer'], mode='r') as fr:
        jsa = json.load(fr)
    spg: SemanticsPreGraph = SemanticsPreGraph.from_dict(jsa)
    input_kore: Kore.Pattern = get_input_kore(Path(args['definition']), Path(args['input']))
    #print(input_kore)
    scfg = SCFG(rs, spg)
    scfg.break_pattern(input_kore)
    print("SCFG constructed.")
    return 0

def generate_analyzer(rs: ReachabilitySystem, args) -> int:
    with open(args['analyzer'], mode="w") as fw:
        semantics_pregraph = compute_semantics_pregraph(rs)
        fw.write(json.dumps(semantics_pregraph.dict))
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

    return argument_parser


def main():
    argument_parser = create_argument_parser()
    args = vars(argument_parser.parse_args())
    print(f"args: {args}")
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
        else:
            retval = 1
    
    sys.exit(retval)
    
