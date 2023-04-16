import argparse
import logging
import sys
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
    List
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

def create_argument_parser() -> argparse.ArgumentParser:
    argument_parser = argparse.ArgumentParser(
        prog="kaipy",
        description="A K abstract interpreter"
    )
    argument_parser.add_argument('-d', '--definition', required=True)

    subparsers = argument_parser.add_subparsers(dest='command')
    
    subparser_analyze = subparsers.add_parser('analyze', help='Analyze given input program')
    subparser_analyze.add_argument('--input', required=True)
    return argument_parser

def may_transit(rs: ReachabilitySystem, patt_from: Kore.Pattern, patt_to: Kore.Pattern, axiom: Kore.Rewrites) -> bool:
    vars_to_rename = list(free_evars_of_pattern(axiom.left))
    vars_to_avoid = vars_to_rename + list(free_evars_of_pattern(patt_from))
    new_vars = get_fresh_evars_with_sorts(avoid=list(vars_to_avoid), sorts=list(map(lambda ev: ev.sort, vars_to_rename)))
    vars_fr : List[str] = list(map(lambda e: e.name, vars_to_rename))
    vars_to : List[str] = list(map(lambda e: e.name, new_vars))
    renaming = dict(zip(vars_fr, vars_to))
    axiom_left = rename_vars(renaming, axiom.left)

    lhs_match = rs.kcs.client.simplify(Kore.And(rs.top_sort, patt_from, axiom_left))
    if (Kore.Bottom == lhs_match):
        return False
    return True

class SCFG:
    rs: ReachabilitySystem
    graph: nx.Graph

    @dataclass(frozen=True)
    class Node:
        pattern: Kore.Pattern
    
    @dataclass(frozen=True)
    class Edge:
        axiom: Kore.Axiom

    def __init__(self, rs: ReachabilitySystem):
        self.rs = rs
        self.graph = nx.Graph()
        # Add nodes
        for a in rs.rewrite_rules:
            match a:
                case Kore.Axiom(_, Kore.Rewrites(_, lhs, _), _):
                    self.graph.add_node(self.Node(lhs))
        # Add edges
        for node_from in self.graph.nodes:
            for node_to in self.graph.nodes:
                for axiom in rs.rewrite_rules:
                    match axiom:
                        case Kore.Axiom(_, Kore.Rewrites(_, _, _) as r, _):
                            if may_transit(self.rs, node_from.pattern, node_to.pattern, r):
                                print(f"May transit from {node_from.pattern.text} using {axiom} ")


def analyze(rs: ReachabilitySystem, args):
    input_kore = get_input_kore(Path(args['definition']), Path(args['input']))
    #print(input_kore)
    scfg = SCFG(rs)
    return 0

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
        else:
            retval = 1
    
    sys.exit(retval)
    
