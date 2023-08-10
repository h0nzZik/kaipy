import typing as T

import pyk.kore.syntax as Kore

import kaipy.kore_utils as KoreUtils

from kaipy.IAbstractPatternDomain import IAbstractPattern, IAbstractPatternDomain
from kaipy.IAbstractSubstitutionDomain import IAbstractSubstitution, IAbstractSubstitutionDomain
from kaipy.FinitePatternDomain import FinitePattern, FinitePatternDomain
from kaipy.CartesianAbstractSubstitutionDomain import CartesianAbstractSubstitution, CartesianAbstractSubstitutionDomain
from kaipy.ReachabilitySystem import ReachabilitySystem


def build_abstract_substitution_domain(
    rs: ReachabilitySystem,
    rests: T.List[Kore.Pattern],
    initial_configuration: Kore.Pattern
) -> IAbstractSubstitutionDomain:
    initial_configuration = rs.simplify(initial_configuration)
    finite_set_of_patterns = rests + list(KoreUtils.some_subpatterns_of(initial_configuration).keys())
    pattern_domain: IAbstractPatternDomain = FinitePatternDomain(finite_set_of_patterns, rs)
    subst_domain: IAbstractSubstitutionDomain = CartesianAbstractSubstitutionDomain(pattern_domain)
    return subst_domain