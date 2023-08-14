import typing as T

import pyk.kore.syntax as Kore

import kaipy.kore_utils as KoreUtils

from kaipy.IAbstractPatternDomain import IAbstractPattern, IAbstractPatternDomain
from kaipy.IAbstractSubstitutionDomain import IAbstractSubstitution, IAbstractSubstitutionDomain
from kaipy.BigsumPatternDomain import BigsumPattern, BigsumPatternDomain
from kaipy.FinitePatternDomain import FinitePattern, FinitePatternDomain
from kaipy.ExactPatternDomain import ExactPattern, ExactPatternDomain
from kaipy.CartesianAbstractSubstitutionDomain import CartesianAbstractSubstitution, CartesianAbstractSubstitutionDomain
from kaipy.ReachabilitySystem import ReachabilitySystem


def build_abstract_substitution_domain(
    rs: ReachabilitySystem,
    rests: T.List[Kore.Pattern],
    initial_configuration: Kore.Pattern
) -> IAbstractSubstitutionDomain:
    initial_configuration = rs.simplify(initial_configuration)
    subpatterns: T.List[Kore.Pattern] = list(KoreUtils.some_subpatterns_of(initial_configuration).keys())
    finite_set_of_patterns = rests + subpatterns
    exact_pattern_domain: IAbstractPatternDomain = ExactPatternDomain(
        rs,
        patterns=[
            p
            for p in finite_set_of_patterns
            if 0 == len(KoreUtils.free_evars_of_pattern(p))
        ],
    )
    finite_pattern_domain: IAbstractPatternDomain = FinitePatternDomain(
        pl=[
            p
            for p in finite_set_of_patterns
            if 0 < len(KoreUtils.free_evars_of_pattern(p))
        ],
        rs=rs
    )
    combined_domain: IAbstractPatternDomain = BigsumPatternDomain(rs=rs, domains=[
        exact_pattern_domain,
        finite_pattern_domain
    ])
    
    #pattern_domain: IAbstractPatternDomain = FinitePatternDomain(finite_set_of_patterns, rs)
    subst_domain: IAbstractSubstitutionDomain = CartesianAbstractSubstitutionDomain(combined_domain)
    return subst_domain