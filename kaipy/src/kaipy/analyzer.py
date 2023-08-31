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

from .ReachabilitySystem import ReachabilitySystem, KoreClientServer, get_global_kcs
from .KompiledDefinitionWrapper import KompiledDefinitionWrapper
from .Substitution import Substitution

_LOGGER: T.Final = logging.getLogger(__name__)


# TODO remove
# Turns
# { x |-> {phi1, phi2}, y |-> {phi3, phi4} }
# into
# { {x |-> phi1, y |-> phi3}, {x |-> phi1, y |-> phi4}, {x |-> phi2, y |-> phi3}, {x |-> phi2, y |-> phi4}  }
def cartesian_dict(d: T.Mapping[T.Any, T.Any]) -> T.Set[T.Mapping[T.Any, T.Any]]:
    if len(list(d.keys())) == 0:
        return {immutabledict()}
    k = list(d.keys())[0]
    xs = d[k]
    d1: immutabledict[T.Any,T.Any] = immutabledict({k1:v1 for k1,v1 in d.items() if not k1 == k})
    cd = cartesian_dict(d1)
    result: T.Set[T.Any] = set()
    for di in cd:
        for x in xs:
            d2 = { k0:v0 for k0,v0 in di.items() }
            d2.update({k:x})
            result.add(immutabledict(d2))
    return result



def normalize_pattern(cfg: Kore.Pattern) -> Kore.Pattern:
    vs = KoreUtils.free_occs_det(cfg)
    renaming = { v.name : ("VAR"+str(i)) for i,v in enumerate(vs)}
    return KoreUtils.rename_vars(renaming, cfg)


def get_successors(rs: ReachabilitySystem, cfg: Kore.Pattern) -> T.List[Kore.Pattern]:
    exec_result: KoreRpc.ExecuteResult = rs.execute_step(cfg)
    if exec_result.next_states is not None:
        successors = [s.kore for s in exec_result.next_states]
    else:
        successors = [exec_result.state.kore]
    return successors

def make_ctx() -> AbstractionContext:
    class BC(IBroadcastChannel):
        def broadcast(self, m: T.List[Kore.MLPred]):
            pass
    bc = BC()
    vm = VariableManager(5) # TODO generate high-enough number
    ctx = AbstractionContext(broadcast_channel=bc, variable_manager=vm)
    return ctx

def analyze(
    rs: ReachabilitySystem,
    pattern_domain: IAbstractPatternDomain,
    initial_configuration: Kore.Pattern,
) -> IAbstractPattern:
    #states: States = build_states(rs, KoreUtils.free_evars_of_pattern(initial_configuration))

    cfgs_below_current: T.Dict[Kore.Pattern,T.List[Kore.Pattern]] = dict()

    initial_concrete: Kore.Pattern = normalize_pattern(rs.simplify(initial_configuration))
    current_abstract: IAbstractPattern = pattern_domain.abstract(make_ctx(), initial_concrete)
    while True:
        current_concretized: T.List[Kore.Pattern] = KoreUtils.or_to_list(pattern_domain.concretize(current_abstract))
        diff = [c for c in current_concretized if c not in cfgs_below_current.keys()]
        if len(diff) <= 0:
            return current_abstract
        diff_step = { c:get_successors(rs, c) for c in diff }
        diff_step_norm = { c:[ normalize_pattern(s) for s in succs] for c,succs in diff_step.items() }
        unified = cfgs_below_current.copy()
        unified.update(diff_step_norm)
        phi = RSUtils.make_disjunction(rs, list(itertools.chain(*unified.values())))
        current_abstract = pattern_domain.disjunction(
            make_ctx(),
            current_abstract,
            pattern_domain.abstract(make_ctx(), phi)
        )
 