import typing as T

import pyk.kore.syntax as Kore

import kaipy.kore_utils as KoreUtils
from kaipy.ReachabilitySystem import ReachabilitySystem
from kaipy.interfaces.IAbstractConstraintDomain import IAbstractConstraintDomain
from kaipy.domains.PatternMatchDomain import PatternMatchDomain

def build_states(rs: ReachabilitySystem) -> T.List[T.Tuple[Kore.Pattern, str]]:
    l: T.List[T.Tuple[Kore.Pattern, str]] = list()

    for axiom in rs.kdw.rewrite_rules:
        match axiom:
            case Kore.Axiom(_, Kore.Rewrites(_, lhs, _), _):
                original_rule_label: str = KoreUtils.axiom_label(axiom)
                # Ideally we would want all states to have different variables, because these states will be joined using Or.
                # But for now it is enough if same-named variables have same sorts, which is guaranteed by `normalize_pattern`.
                l.append((KoreUtils.normalize_pattern(lhs, prefix='W'), original_rule_label))
                #l.append((KoreUtils.normalize_pattern(lhs, prefix='W'), original_rule_label + ": " + rs.kprint.kore_to_pretty(lhs)))
    return l
       
def build_pattern_match_domain(
    rs: ReachabilitySystem,
    underlying_domain: IAbstractConstraintDomain
) -> PatternMatchDomain:
    states = build_states(rs)
    domain = PatternMatchDomain(rs, states, [underlying_domain for _ in states])
    return domain

