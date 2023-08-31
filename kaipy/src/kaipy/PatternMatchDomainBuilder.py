import typing as T

import pyk.kore.syntax as Kore

import kaipy.kore_utils as KoreUtils
from kaipy.ReachabilitySystem import ReachabilitySystem
from kaipy.interfaces.IAbstractConstraintDomainBuilder import IAbstractConstraintDomainBuilder
from kaipy.domains.PatternMatchDomain import PatternMatchDomain

def build_states(rs: ReachabilitySystem) -> T.List[Kore.Pattern]:
    l: T.List[Kore.Pattern] = list()

    for axiom in rs.kdw.rewrite_rules:
        match axiom:
            case Kore.Axiom(_, Kore.Rewrites(_, lhs, _), _):
                original_rule_label: str = KoreUtils.axiom_label(axiom)
                l.append(lhs)
    return l
       
def build_pattern_match_domain(
    rs: ReachabilitySystem,
    underlying_domain_builder: IAbstractConstraintDomainBuilder
) -> PatternMatchDomain:
    states = build_states(rs)
    domain = PatternMatchDomain(rs, states, underlying_domain_builder)
    return domain
