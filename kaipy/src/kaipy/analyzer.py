import abc
import dataclasses
import itertools
import logging
import typing as T

from immutabledict import immutabledict

import pyk.kore.prelude as KorePrelude
import pyk.kore.rpc as KoreRpc
import pyk.kore.syntax as Kore

import kaipy.rs_utils as RSUtils
import kaipy.kore_utils as KoreUtils

from .ReachabilitySystem import ReachabilitySystem
from .Substitution import Substitution


class IAbstractPattern(abc.ABC):
    ...

class IAbstractPatternDomain(abc.ABC):
    @abc.abstractmethod
    def abstract(self, c: Kore.Pattern) -> IAbstractPattern:
        ...

    @abc.abstractmethod
    def concretize(self, a: IAbstractPattern) -> T.Set[Kore.Pattern]:
        ...

class IAbstractSubstitution(abc.ABC):
    ...

class IAbstractSubstitutionDomain(abc.ABC):
    @abc.abstractmethod
    def concretize(self, a: IAbstractSubstitution) -> T.Set[Substitution]:
        ...
    
    @abc.abstractmethod
    def abstract(self, subst: Substitution) -> IAbstractSubstitution:
        ...

# Turns
# { x |-> {phi1, phi2}, y |-> {phi3, phi4} }
# into
# { {x |-> phi1, y |-> phi3}, {x |-> phi1, y |-> phi4}, {x |-> phi2, y |-> phi3}, {x |-> phi2, y |-> phi4}  }
def cartesian_dict(d: T.Dict[T.Any, T.Any]) -> T.Set[T.Dict[T.Any, T.Any]]:
    if len(list(d.keys())) == 0:
        return {immutabledict()}
    k = list(d.keys())[0]
    xs = d[k]
    d1 = immutabledict({k1:v1 for k1,v1 in d.items() if not k1 == k})
    cd = cartesian_dict(d1)
    result = set()
    for di in cd:
        for x in xs:
            d2 = { k0:v0 for k0,v0 in di.items() }
            d2.update({k:x})
            result.add(immutabledict(d2))
    return result

@dataclasses.dataclass
class CartesianAbstractSubstitution(IAbstractSubstitution):
    mapping: T.Mapping[Kore.EVar, IAbstractPattern]

class CartesianAbstractSubstitutionDomain(IAbstractSubstitutionDomain):
    pattern_domain: IAbstractPatternDomain

    def __init__(self, pattern_domain: IAbstractPatternDomain):
        self.pattern_domain = pattern_domain
    
    def abstract(self, subst: Substitution) -> IAbstractSubstitution:
        return CartesianAbstractSubstitution(
            {
                v : self.pattern_domain.abstract(p)
                for (v,p) in subst.mapping.items()
            }
        )

    def concretize(self, a: IAbstractSubstitution) -> T.Set[Substitution]:
        assert type(a) is CartesianAbstractSubstitution

        concretes: T.Dict[Kore.EVar, T.Set[Kore.Pattern]] = {
            k : self.pattern_domain.concretize(v)
            for k,v in a.mapping.items()
        }
        cd = cartesian_dict(concretes)
        return {Substitution(immutabledict(d)) for d in cd}


@dataclasses.dataclass
class StateInfo:
    description: str
    substitutions: T.List[Substitution]


@dataclasses.dataclass
class States:
    states: T.Dict[Kore.Pattern, StateInfo]


def build_states(rs: ReachabilitySystem, vars_to_avoid: T.Set[Kore.EVar]) -> States:
    d : T.Dict[Kore.Pattern, StateInfo] = dict()

    for axiom in rs.kdw.rewrite_rules:
        match axiom:
            case Kore.Axiom(_, Kore.Rewrites(_, lhs, _), _):
                pattern: Kore.Pattern = lhs
                original_rule_label: str = KoreUtils.axiom_label(axiom)
                applicable_rules: T.List[str] = []
                
                vars_to_rename = [
                    ev
                    for ev in KoreUtils.free_evars_of_pattern(pattern)
                    if ev.name in vars_to_avoid
                ]
                pattern_renamed: Kore.Pattern = KoreUtils.rename_vars(
                    KoreUtils.compute_renaming0(
                        vars_to_avoid=list(vars_to_avoid),
                        vars_to_rename=vars_to_rename
                    ),
                    pattern,
                )
                d[pattern_renamed] = StateInfo(original_rule_label, [])
                print(f'renamed LHS (new state): {rs.kprint.kore_to_pretty(pattern_renamed)}')
    return States(d)


def for_each_match(rs: ReachabilitySystem, states: States, cfgs: T.List[Kore.Pattern]):
    for cfg in cfgs:
        for st in states.states:
            # project configuration `cfg` to state `st`
            conj = Kore.And(rs.top_sort, cfg, st)
            conj_simplified = rs.kcs.client.simplify(conj)[0]
            if KoreUtils.is_bottom(conj_simplified):
                continue
            eqls: T.Dict[Kore.EVar, Kore.Pattern] = KoreUtils.extract_equalities_from_witness(
                {ev.name for ev in KoreUtils.free_evars_of_pattern(st)},
                conj_simplified
            )
            new_subst = Substitution(immutabledict(eqls))
            

def analyze(rs: ReachabilitySystem, initial_configuration: Kore.Pattern) -> None:
    states: States = build_states(rs, KoreUtils.free_evars_of_pattern(initial_configuration))

    return None
