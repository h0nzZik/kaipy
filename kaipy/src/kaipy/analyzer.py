import abc
import dataclasses
import itertools
import functools
import logging
import pprint
import typing as T

from immutabledict import immutabledict

import pyk.kore.prelude as KorePrelude
import pyk.kore.rpc as KoreRpc
import pyk.kore.syntax as Kore
from pyk.ktool.kprint import KPrint

import kaipy.rs_utils as RSUtils
import kaipy.kore_utils as KoreUtils

from kaipy.IBroadcastChannel import IBroadcastChannel
from kaipy.VariableManager import VariableManager
from kaipy.AbstractionContext import AbstractionContext
from kaipy.interfaces.IAbstractConstraintDomainBuilder import IAbstractConstraintDomainBuilder
from kaipy.interfaces.IAbstractPatternDomain import IAbstractPattern, IAbstractPatternDomain
from kaipy.interfaces.IAbstractSubstitutionDomain import IAbstractSubstitution, IAbstractSubstitutionDomain
from kaipy.interfaces.IAbstractConstraintDomain import IAbstractConstraintDomain, IAbstractConstraint
from kaipy.DefaultAbstractionContext import make_ctx

from .ReachabilitySystem import ReachabilitySystem, KoreClientServer, get_global_kcs
from .KompiledDefinitionWrapper import KompiledDefinitionWrapper
from .Substitution import Substitution

_LOGGER: T.Final = logging.getLogger(__name__)

def normalize_pattern(cfg: Kore.Pattern) -> Kore.Pattern:
    vs = KoreUtils.free_occs_det(cfg)
    # Different sorts will have different namespaces.
    # This way we avoid clashes of names like `X:SortInt` with `X:SortList`
    renaming = { v.name : (f"VAR'V{v.sort.name}'{str(i)}") for i,v in enumerate(vs)}
    return KoreUtils.rename_vars(renaming, cfg)


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
    #states: States = build_states(rs, KoreUtils.free_evars_of_pattern(initial_configuration))

    cfgs_below_current: T.Dict[Kore.Pattern,T.List[Kore.Pattern]] = dict()
    ctx = make_ctx()
    initial_concrete: Kore.Pattern = normalize_pattern(rs.simplify(initial_configuration))
    current_abstract: IAbstractPattern = pattern_domain.abstract(ctx, initial_concrete)
    curr_depth = 0
    while True:
        if max_depth is not None and curr_depth > max_depth:
            break
        curr_depth = curr_depth + 1
        _LOGGER.warning(f"Iteration {curr_depth}")
        current_concretized: T.List[Kore.Pattern] = KoreUtils.or_to_list(pattern_domain.concretize(current_abstract))
        diff = [c for c in current_concretized if c not in cfgs_below_current.keys()]
        if len(diff) <= 0:
            break
        diff_step = { c:get_successors(rs, c) for c in diff }
        diff_step_norm = { c:[ normalize_pattern(s) for s in succs] for c,succs in diff_step.items() }
        unified = cfgs_below_current.copy()
        unified.update(diff_step_norm)
        phi = RSUtils.make_disjunction(rs, list(itertools.chain(*unified.values())))
        current_abstract = pattern_domain.disjunction(
            ctx,
            current_abstract,
            pattern_domain.abstract(ctx, phi)
        )
        cfgs_below_current = unified
 
    return AnalysisResult(reachable_configurations=current_abstract, iterations=curr_depth)