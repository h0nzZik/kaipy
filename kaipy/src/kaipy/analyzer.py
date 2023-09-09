import abc
import dataclasses
import itertools
import functools
import logging
import pprint
import sys
import typing as T

from immutabledict import immutabledict

import pyk.kore.prelude as KorePrelude
import pyk.kore.rpc as KoreRpc
import pyk.kore.syntax as Kore
from pyk.ktool.kprint import KPrint

import kaipy.rs_utils as RSUtils
import kaipy.kore_utils as KoreUtils

from kaipy.BroadcastChannel import BroadcastChannel
from kaipy.VariableManager import VariableManager
from kaipy.AbstractionContext import AbstractionContext
from kaipy.interfaces.IAbstractPatternDomain import IAbstractPattern, IAbstractPatternDomain
from kaipy.interfaces.IAbstractSubstitutionDomain import IAbstractSubstitution, IAbstractSubstitutionDomain
from kaipy.interfaces.IAbstractConstraintDomain import IAbstractConstraintDomain, IAbstractConstraint
from kaipy.DefaultAbstractionContext import make_ctx

from .ReachabilitySystem import ReachabilitySystem, KoreClientServer, get_global_kcs
from .KompiledDefinitionWrapper import KompiledDefinitionWrapper
from .Substitution import Substitution

_LOGGER: T.Final = logging.getLogger(__name__)


def get_successors(rs: ReachabilitySystem, cfg: Kore.Pattern) -> T.List[Kore.Pattern]:
    exec_result: KoreRpc.ExecuteResult = rs.execute_step(cfg)
    if exec_result.next_states is not None:
        successors = [s.kore for s in exec_result.next_states]
    else:
        successors = [exec_result.state.kore]
    return successors

@dataclasses.dataclass
class AnalysisResult:
    reachable_configurations: IAbstractPattern
    iterations: int

def analyze(
    rs: ReachabilitySystem,
    pattern_domain: IAbstractPatternDomain,
    initial_configuration: Kore.Pattern,
    max_depth: int|None = None
) -> AnalysisResult:
    sys.setrecursionlimit(4*10**3)
    #sys.setrecursionlimit(10**4)
    #sys.setrecursionlimit(10**7)

    cfgs_below_current: T.Dict[Kore.Pattern,T.List[Kore.Pattern]] = dict()
    ctx = make_ctx()
    initial_concrete: Kore.Pattern = KoreUtils.normalize_pattern(rs.simplify(initial_configuration))
    current_abstract: IAbstractPattern = pattern_domain.abstract(ctx, initial_concrete)
    curr_depth = 0
    while True:
        if max_depth is not None and curr_depth > max_depth:
            break
        curr_depth = curr_depth + 1
        _LOGGER.warning(f"Iteration {curr_depth}")
        _LOGGER.warning(f"current_abstract: {pattern_domain.to_str(current_abstract, indent=0)}")
        current_concretized = pattern_domain.concretize(current_abstract)
        #_LOGGER.warning(f"current_concretized: {rs.kprint.kore_to_pretty(current_concretized)}")
        current_concretized_list: T.List[Kore.Pattern] = KoreUtils.or_to_list(rs.simplify(current_concretized))
        # Should we cleanup the patterns? I do not know.
        current_concretized_list_normalized = [ KoreUtils.normalize_pattern(KoreUtils.cleanup_pattern(rs.top_sort, c)) for c in current_concretized_list ]
        #current_concretized_list_normalized = [ KoreUtils.normalize_pattern(c) for c in current_concretized_list ]
        diff = [c for c in current_concretized_list_normalized if c not in cfgs_below_current.keys()]
        if len(diff) <= 0:
            break
        _LOGGER.warning(f'diff: {rs.kprint.kore_to_pretty(RSUtils.make_disjunction(rs, diff))}')
        #_LOGGER.warning(f'diff_raw: {RSUtils.make_disjunction(rs, diff).text}')
        diff_step = { c:get_successors(rs, c) for c in diff }
        
        diff_step_norm = { c:[ KoreUtils.normalize_pattern(s) for s in succs] for c,succs in diff_step.items() }
        # Should we clean up the pattern? I am not sure.
        #diff_step_norm = { c:[ KoreUtils.normalize_pattern(RSUtils.cleanup_pattern(rs,s)) for s in succs] for c,succs in diff_step.items() }
        if len(list(set(itertools.chain(*diff_step_norm.values())))) > 1 or True:
            #_LOGGER.warning("More than 1 successor")
            #_LOGGER.warning(f'of: {rs.kprint.kore_to_pretty(RSUtils.make_disjunction(rs, diff))}')
            #_LOGGER.warning(f"succs_raw: {rs.kprint.kore_to_pretty(RSUtils.make_disjunction(rs, list(set(itertools.chain(*diff_step.values())))))}")
            _LOGGER.warning(f"succs_raw: {RSUtils.make_disjunction(rs, list(set(itertools.chain(*diff_step_norm.values())))).text}")
            _LOGGER.warning(f"succs: {rs.kprint.kore_to_pretty(RSUtils.make_disjunction(rs, list(set(itertools.chain(*diff_step_norm.values())))))}")
        unified = cfgs_below_current.copy()
        unified.update(diff_step_norm)
        # We need to make sure that variables in different components have different names
        dl = list(itertools.chain(*unified.values()))
        dl2 = [ KoreUtils.normalize_pattern(x, prefix=f"C{i}V") for i,x in enumerate(dl)]
        phi = RSUtils.make_disjunction(rs, dl2)
        new_abstract = pattern_domain.abstract(ctx, phi)
        #refined_abstract = pattern_domain.refine(ctx, new_abstract)
        current_abstract = pattern_domain.disjunction(
            ctx,
            current_abstract,
            new_abstract,
        )
        cfgs_below_current = unified
 
    return AnalysisResult(reachable_configurations=current_abstract, iterations=curr_depth)