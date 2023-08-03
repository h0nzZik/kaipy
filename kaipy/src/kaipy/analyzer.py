import dataclasses
import itertools
import logging
import typing as T

import pyk.kore.prelude as KorePrelude
import pyk.kore.rpc as KoreRpc
import pyk.kore.syntax as Kore

import kaipy.rs_utils as RSUtils
import kaipy.kore_utils as KoreUtils

from .ReachabilitySystem import ReachabilitySystem
from .Substitution import Substitution

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
    return States(d)


def for_each_match(rs: ReachabilitySystem, states: States, cfgs: T.List[Kore.Pattern]):
    for cfg in cfgs:
        for st in states.states:
            # project configuration `cfg` to state `st`
            conj = Kore.And(rs.top_sort, cfg, st)
            conj_simplified = rs.kcs.client.simplify(conj)[0]
            if KoreUtils.is_bottom(conj_simplified):
                continue
            # But what to do if `cfg` and `st` share free variables?

def analyze(rs: ReachabilitySystem, initial_configuration: Kore.Pattern) -> None:
    return None
