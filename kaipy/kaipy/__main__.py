import argparse
import logging
import sys
import argparse

from pathlib import Path

from pyk.ktool import krun
from pyk.kore.parser import KoreParser
import pyk.kore.syntax as Kore

from .kcommands import KRUN_COMMAND

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
        description="A Cartesian Reachability Logic tool"
    )
    argument_parser.add_argument('-d', '--definition', required=True)

    subparsers = argument_parser.add_subparsers(dest='command')
    
    subparser_analyze = subparsers.add_parser('analyze', help='Analyze given input program')
    subparser_analyze.add_argument('--input', required=True)
    return argument_parser

def analyze(args):
    input_kore = get_input_kore(Path(args['definition']), Path(args['input']))
    print(input_kore)
    return 0

def main():
    argument_parser = create_argument_parser()
    args = vars(argument_parser.parse_args())
    print(f"args: {args}")
    logging.basicConfig(encoding='utf-8', level=logging.DEBUG)
    logging.getLogger('pyk.kore.rpc').disabled = True
    logging.getLogger('pyk.ktool.kprint').disabled = True
    logging.getLogger('pyk.kast.inner').disabled = True 
    

    if args['command'] == 'analyze':
        retval = analyze(args)
    else:
        retval = 1
    
    sys.exit(retval)
    
