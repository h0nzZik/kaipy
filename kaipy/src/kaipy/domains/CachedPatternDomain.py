import abc
import typing as T

import pyk.kore.syntax as Kore

import kaipy.kore_utils as KoreUtils
from kaipy.AbstractionContext import AbstractionContext
from kaipy.interfaces.IAbstractPatternDomain import IAbstractPattern, IAbstractPatternDomain


class CachedPatternDomain(IAbstractPatternDomain):
    underlying: IAbstractPatternDomain
    # We cache only in one direction, since the other is supposed to be fast enough.
    cache: T.Dict[Kore.Pattern, IAbstractPattern]
    
    def __init__(self, underlying: IAbstractPatternDomain):
        self.underlying = underlying
        self.cache = dict()

    def abstract(self, ctx: AbstractionContext, c: Kore.Pattern) -> IAbstractPattern:
        c2 = KoreUtils.normalize_pattern(c)
        if c2 in self.cache:
            return self.cache[c2]

        a = self.underlying.abstract(ctx, c2)
        self.cache[c2] = a
        return a

    def free_variables_of(self, a: IAbstractPattern) -> T.Set[Kore.EVar]:
        return self.underlying.free_variables_of(a)

    def refine(self, ctx: AbstractionContext, a: IAbstractPattern, c: Kore.Pattern) -> IAbstractPattern:
        return self.underlying.refine(ctx, a, c)

    def disjunction(self, ctx: AbstractionContext, a1: IAbstractPattern, a2: IAbstractPattern) -> IAbstractPattern:
        return self.underlying.disjunction(ctx, a1, a2)

    def is_top(self, a: IAbstractPattern) -> bool:
        return self.underlying.is_top(a)

    def is_bottom(self, a: IAbstractPattern) -> bool:
        return self.underlying.is_bottom(a)

    def concretize(self, a: IAbstractPattern) -> Kore.Pattern:
        return self.underlying.concretize(a)

    def equals(self, a1: IAbstractPattern, a2: IAbstractPattern) -> bool:
        return self.underlying.equals(a1, a2)

    def subsumes(self, a1: IAbstractPattern, a2: IAbstractPattern) -> bool:
        return self.underlying.subsumes(a1, a2)
    
    def to_str(self, a: IAbstractPattern, indent: int) -> str:
        return self.underlying.to_str(a, indent)