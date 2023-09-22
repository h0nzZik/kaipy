import typing as T

import pyk.kore.syntax as Kore
import pyk.kore.prelude as KorePrelude

import kaipy.kore_utils as KoreUtils

from kaipy.interfaces.IAbstractConstraintDomain import IAbstractConstraintDomain
from kaipy.interfaces.IAbstractPatternDomain import IAbstractPatternDomain
from kaipy.interfaces.IAbstractSubstitutionDomain import IAbstractSubstitutionDomain
from kaipy.interfaces.IAbstractSubstitutionsDomain import IAbstractSubstitutionsDomain

from kaipy.domains.CachedConstraintDomain import CachedConstraintDomain
from kaipy.domains.DisjunctiveConstraintDomain import DisjunctiveConstraintDomain
from kaipy.domains.SubstitutionListDomain import SubstitutionListDomain
from kaipy.domains.SubstitutionConstraintDomain import SubstitutionConstraintDomain
from kaipy.domains.BigsumPatternDomain import BigsumPatternDomain
from kaipy.domains.FiniteTermDomain import FiniteTermDomain
from kaipy.domains.ExactTermDomain import ExactTermDomain
from kaipy.domains.CartesianAbstractSubstitutionDomain import CartesianAbstractSubstitutionDomain
from kaipy.domains.ProductConstraintDomain import ProductConstraintDomain
from kaipy.domains.KResultConstraintDomain import KResultConstraintDomain
from kaipy.domains.PatternMatchDomain import PatternMatchDomain
from kaipy.domains.CachedPatternDomain import CachedPatternDomain
from kaipy.PatternMatchDomainBuilder import build_pattern_match_domain

from kaipy.ReachabilitySystem import ReachabilitySystem


def build_abstract_pattern_domain(
    rs: ReachabilitySystem,
    rests: T.List[Kore.Pattern],
    initial_configuration: Kore.Pattern
) -> IAbstractPatternDomain:
    initial_configuration = rs.simplify(initial_configuration)
    subpatterns: T.List[Kore.Pattern] = list(KoreUtils.some_subpatterns_of(initial_configuration).keys())
    finite_set_of_patterns = rests + subpatterns + [KorePrelude.DOTK]
    exact_pattern_domain: IAbstractPatternDomain = ExactTermDomain(
        rs,
        patterns=[
            p
            for p in finite_set_of_patterns
            if 0 == len(KoreUtils.free_evars_of_pattern(p))
        ],
    )
    finite_pattern_domain: IAbstractPatternDomain = FiniteTermDomain(
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

    cached_combined_domain: IAbstractPatternDomain = CachedPatternDomain(combined_domain)
    
    subst_domain: IAbstractSubstitutionDomain = CartesianAbstractSubstitutionDomain(cached_combined_domain)
    #subst_list_domain: IAbstractSubstitutionsDomain = SubstitutionListDomain(subst_domain)
    subst_constr_domain: IAbstractConstraintDomain = SubstitutionConstraintDomain(rs=rs, nested=subst_domain)

    # Second substitution domain - to catch stuff coming out from the first subst domain. Mainly for `.K`
    exact_pattern_domain_2: IAbstractPatternDomain = ExactTermDomain(
        rs,
        patterns=[KorePrelude.DOTK]
    )
    subst_domain_2: IAbstractSubstitutionDomain = CartesianAbstractSubstitutionDomain(exact_pattern_domain_2)
    #subst_list_domain_2: IAbstractSubstitutionsDomain = SubstitutionListDomain(subst_domain_2)
    subst_constr_domain_2: IAbstractConstraintDomain = SubstitutionConstraintDomain(rs=rs, nested=subst_domain_2)

    kresult_domain: IAbstractConstraintDomain = KResultConstraintDomain(rs=rs)
    product_domain = ProductConstraintDomain([subst_constr_domain, subst_constr_domain_2, kresult_domain])

    product_domain_disj = DisjunctiveConstraintDomain(product_domain, rs=rs)

    cached_product_domain = CachedConstraintDomain(product_domain_disj)
    pattern_match_domain = build_pattern_match_domain(rs, underlying_domain=cached_product_domain)
    return pattern_match_domain