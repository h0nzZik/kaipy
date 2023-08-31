import dataclasses
import typing as T

import pyk.kore.syntax as Kore

from kaipy.ReachabilitySystem import ReachabilitySystem
from kaipy.AbstractionContext import AbstractionContext
from kaipy.interfaces.IAbstractPatternDomain import IAbstractPattern, IAbstractPatternDomain

@dataclasses.dataclass
class BigsumPattern(IAbstractPattern):
    # -1 means Top
    idx: int
    sort: Kore.Sort
    ap: IAbstractPattern|None



class BigsumPatternDomain(IAbstractPatternDomain):
    rs: ReachabilitySystem
    domains: T.List[IAbstractPatternDomain]

    def __init__(self, rs:ReachabilitySystem, domains: T.List[IAbstractPatternDomain]):
        self.rs = rs
        self.domains = domains
    
    def abstract(self, ctx: AbstractionContext, c: Kore.Pattern) -> BigsumPattern:
        sort = self.rs.kdw.sortof(c)
        for i,d in enumerate(self.domains):
            a = d.abstract(ctx, c)
            if not d.is_top(a):
                return BigsumPattern(idx=i, sort=sort, ap=a)
        return BigsumPattern(-1, sort=sort, ap=None)            
    

    def disjunction(self, ctx: AbstractionContext, a1: IAbstractPattern, a2: IAbstractPattern) -> BigsumPattern:
        assert type(a1) is BigsumPattern
        assert type(a2) is BigsumPattern
        if a1.idx == a2.idx and a1.sort == a2.sort and a1.ap is not None and a2.ap is not None:
            return BigsumPattern(idx=a1.idx, sort=a1.sort, ap=self.domains[a1.idx].disjunction(ctx, a1.ap, a2.ap))
        return BigsumPattern(-1, sort=a1.sort, ap=None)

    def refine(self, ctx: AbstractionContext, a: IAbstractPattern, c: Kore.Pattern) -> IAbstractPattern:
        assert type(a) is BigsumPattern
        if a.idx == -1:
            return a
        if a.ap is None:
            return a
        return BigsumPattern(
            idx=a.idx,
            sort=a.sort,
            ap=self.domains[a.idx].refine(ctx, a.ap, c)
        )

    def is_top(self, a: IAbstractPattern) -> bool:
        assert type(a) is BigsumPattern
        if a.idx == -1:
            return True
        if a.ap is None:
            return True
        return self.domains[a.idx].is_top(a.ap)
    
    def is_bottom(self, a: IAbstractPattern) -> bool:
        assert type(a) is BigsumPattern
        if a.idx == -1:
            return False
        if a.ap is None:
            return False
        return self.domains[a.idx].is_bottom(a.ap)

    def concretize(self, a: IAbstractPattern) -> Kore.Pattern:
        assert type(a) is BigsumPattern
        if self.is_top(a):
            return Kore.Top(a.sort)
        assert a.idx >= 0
        assert a.ap is not None
        return self.domains[a.idx].concretize(a.ap)

    def equals(self, a1: IAbstractPattern, a2: IAbstractPattern) -> bool:
        assert type(a1) is BigsumPattern
        assert type(a2) is BigsumPattern

        if a1.idx != a2.idx:
            return False
        
        assert a1.idx == a2.idx
        if a1.idx == -1:
            return True

        assert a1.ap is not None
        assert a2.ap is not None

        return self.domains[a1.idx].equals(a1.ap, a2.ap)

    def subsumes(self, a1: IAbstractPattern, a2: IAbstractPattern) -> bool:
        assert type(a1) is BigsumPattern
        assert type(a2) is BigsumPattern

        if a1.idx != a2.idx:
            return False
        
        if a1.idx == -1:
            return True

        assert a1.ap is not None
        assert a2.ap is not None
        return self.domains[a1.idx].subsumes(a1.ap, a2.ap)
        #if a1.sort != a1.sort:
        #    return False
        #
        #p1 = self.concretize(a1)
        #p2 = self.concretize(a2)
        #return self.rs.subsumes(p1,p2)[0]

        

    def to_str(self, a: IAbstractPattern) -> str:
        assert type(a) is BigsumPattern
        if (a.idx < 0) or (a.ap is None):
            return f'<bigsum Top>'
        return f'<bigsum idx={a.idx}, a={self.domains[a.idx].to_str(a.ap)}>'