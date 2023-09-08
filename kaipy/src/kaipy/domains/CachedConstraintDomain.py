import abc
import typing as T

import pyk.kore.syntax as Kore

from kaipy.AbstractionContext import AbstractionContext
from kaipy.interfaces.IAbstractConstraintDomain import IAbstractConstraint, IAbstractConstraintDomain
from kaipy.interfaces.IAbstractConstraintDomainBuilder import IAbstractConstraintDomainBuilder


class CachedConstraintDomain(IAbstractConstraintDomain):
    cache: T.Dict[T.FrozenSet[Kore.MLPred], IAbstractConstraint]
    underlying: IAbstractConstraintDomain

    def __init__(self, underlying: IAbstractConstraintDomain):
        self.cache = dict()
        self.underlying = underlying

    def abstract(self, ctx: AbstractionContext, c: T.List[Kore.MLPred]) -> IAbstractConstraint:
        sc = frozenset(c)
        if sc in self.cache.keys():
            return self.cache[sc]
        a = self.underlying.abstract(ctx, c)
        self.cache[sc] = a
        return a
    
    def refine(self, ctx: AbstractionContext, a: IAbstractConstraint, c: T.List[Kore.MLPred]) -> IAbstractConstraint:
        return self.underlying.refine(ctx, a, c)   

    def disjunction(self, ctx: AbstractionContext, a1: IAbstractConstraint, a2: IAbstractConstraint) -> IAbstractConstraint:
        return self.underlying.disjunction(ctx, a1, a2)

    def concretize(self, a: IAbstractConstraint) -> T.List[Kore.MLPred]:
        # This is supposed to be fast, therefore I do not cache it
        return self.underlying.concretize(a)
    
    def is_top(self, a: IAbstractConstraint) -> bool:
        return self.underlying.is_top(a)

    def is_bottom(self, a: IAbstractConstraint) -> bool:
        return self.underlying.is_bottom(a)

    def subsumes(self, a1: IAbstractConstraint, a2: IAbstractConstraint) -> bool:
        return self.underlying.subsumes(a1, a2)
    
    def equals(self, a1: IAbstractConstraint, a2: IAbstractConstraint) -> bool:
        return self.underlying.equals(a1, a2)

    def to_str(self, a: IAbstractConstraint, indent: int) -> str:
        return self.underlying.to_str(a, indent)


class CachedConstraintDomainBuilder(IAbstractConstraintDomainBuilder):
    underlying: IAbstractConstraintDomainBuilder
    
    def __init__(self, underlying: IAbstractConstraintDomainBuilder):
        self.underlying = underlying
    
    def build_abstract_constraint_domain(self, over_variables: T.Set[Kore.EVar]) -> IAbstractConstraintDomain:
        underlying = self.underlying.build_abstract_constraint_domain(over_variables)
        return CachedConstraintDomain(underlying)