import typing as T

import pyk.kore.syntax as Kore

import kaipy.kore_utils as KoreUtils

from kaipy.interfaces.IAbstractConstraintDomain import IAbstractConstraintDomain
from kaipy.interfaces.IAbstractPatternDomain import IAbstractPatternDomain
from kaipy.interfaces.IAbstractSubstitutionDomain import IAbstractSubstitutionDomain

from kaipy.domains.SubstitutionConstraintDomain import SubstitutionConstraintDomain
from kaipy.domains.BigsumPatternDomain import BigsumPatternDomain
from kaipy.domains.FinitePatternDomain import FinitePatternDomain
from kaipy.domains.ExactPatternDomain import ExactPatternDomain
from kaipy.domains.CartesianAbstractSubstitutionDomain import CartesianAbstractSubstitutionDomain
from kaipy.domains.ProductConstraintDomain import ProductConstraintDomain
from kaipy.domains.KResultConstraintDomain import KResultConstraintDomain
from kaipy.domains.PatternMatchDomain import PatternMatchDomain
from kaipy.PatternMatchDomainBuilder import build_pattern_match_domain

from kaipy.ReachabilitySystem import ReachabilitySystem


def build_abstract_constraint_domain(
    rs: ReachabilitySystem,
    rests: T.List[Kore.Pattern],
    initial_configuration: Kore.Pattern
) -> IAbstractConstraintDomain:
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
    subst_domain_1: IAbstractConstraintDomain = SubstitutionConstraintDomain(rs=rs, nested=subst_domain)

    #return subst_domain
    #kresult_domain: IAbstractSubstitutionDomain = KResultSubstDomainWrapper(rs=rs, underlying_subst_domain=subst_domain, limit=1)
    kresult_domain: IAbstractConstraintDomain = KResultConstraintDomain(rs=rs, limit=1)
    product_domain_1 = ProductConstraintDomain(subst_domain_1, kresult_domain)

    pattern_match_domain = build_pattern_match_domain(rs)

    return product_domain_1