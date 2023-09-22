import abc
import dataclasses
import typing as T

import pyk.kore.syntax as Kore
import pyk.kore.prelude as KorePrelude

from kaipy.ReachabilitySystem import ReachabilitySystem
from kaipy.interfaces.IAbstractPatternDomain import IAbstractPattern, IAbstractPatternDomain
from kaipy.AbstractionContext import AbstractionContext

@dataclasses.dataclass
class CastToKItemTerm(IAbstractPattern):
    # None means Top / not a cast into KItem.
    underlying: IAbstractPattern|None

class CastToKItemTermDomain(IAbstractPatternDomain):
    rs: ReachabilitySystem
    underlying: IAbstractPatternDomain

    def __init__(self, rs: ReachabilitySystem, underlying: IAbstractPatternDomain):
        self.rs = rs
        self.underlying = underlying

    def abstract(self, ctx: AbstractionContext,  c: Kore.Pattern) -> IAbstractPattern:
        match c:
            case Kore.App('inj', (_,KorePrelude.SORT_K_ITEM), (c2,)):
                return CastToKItemTerm(underlying=self.underlying.abstract(ctx, c2))
            case _:
                if self.rs.sortof(c) == KorePrelude.SORT_K_ITEM:
                    return CastToKItemTerm(underlying=self.underlying.abstract(ctx, c))
                return CastToKItemTerm(None)

    def free_variables_of(self, a: IAbstractPattern) -> T.Set[Kore.EVar]:
        assert type(a) is CastToKItemTerm
        if a.underlying is None:
            return set()
        return self.underlying.free_variables_of(a.underlying)

    def refine(self, ctx: AbstractionContext, a: IAbstractPattern, c: Kore.Pattern) -> IAbstractPattern:
        return a

    def disjunction(self, ctx: AbstractionContext, a1: IAbstractPattern, a2: IAbstractPattern) -> IAbstractPattern:
        assert type(a1) is CastToKItemTerm
        assert type(a2) is CastToKItemTerm
        if a1.underlying is None or a2.underlying is None:
            return CastToKItemTerm(None)
        return CastToKItemTerm(underlying=self.underlying.disjunction(ctx, a1.underlying, a2.underlying))

    def is_top(self, a: IAbstractPattern) -> bool:
        assert type(a) is CastToKItemTerm
        if a.underlying is None:
            return True
        return self.is_top(a.underlying)

    def is_bottom(self, a: IAbstractPattern) -> bool:
        assert type(a) is CastToKItemTerm
        if a.underlying is None:
            return False
        return self.is_bottom(a.underlying)

    def concretize(self, a: IAbstractPattern) -> Kore.Pattern:
        assert type(a) is CastToKItemTerm
        if a.underlying is None:
            return Kore.Top(KorePrelude.SORT_K_ITEM)
        c1 = self.underlying.concretize(a.underlying)
        s = self.rs.sortof(c1)
        if s == KorePrelude.SORT_K_ITEM:
            return c1
        return KorePrelude.inj(s, KorePrelude.SORT_K_ITEM, c1)

    def equals(self, a1: IAbstractPattern, a2: IAbstractPattern) -> bool:
        assert type(a1) is CastToKItemTerm
        assert type(a2) is CastToKItemTerm
        if a1.underlying is None and a2.underlying is None:
            return True
        if a1.underlying is None and a2.underlying is not None:
            return False
        if a1.underlying is not None and a2.underlying is None:
            return False
        assert a1.underlying is not None
        assert a2.underlying is not None
        return self.underlying.equals(a1.underlying, a2.underlying)

    def subsumes(self, a1: IAbstractPattern, a2: IAbstractPattern) -> bool:
        assert type(a1) is CastToKItemTerm
        assert type(a2) is CastToKItemTerm
        if a2.underlying is None:
            return True
        if a1.underlying is None:
            return False
        return self.underlying.subsumes(a1.underlying, a2.underlying)
    
    def to_str(self, a: IAbstractPattern, indent: int) -> str:
        assert type(a) is CastToKItemTerm
        s = self.underlying.to_str(a.underlying, indent=indent+1) if a.underlying is not None else "<None>"
        return (indent*' ') + "<cast-to-kitem: \n" + s + ">"
    
    def statistics(self) -> T.Dict[str, T.Any]:
        return {
            'underlying': [self.underlying.statistics()]
        }