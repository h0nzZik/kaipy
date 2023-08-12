import dataclasses
import typing as T

import pyk.kore.syntax as Kore

import kaipy.kore_utils as KoreUtils
from kaipy.ReachabilitySystem import ReachabilitySystem
from kaipy.IAbstractPatternDomain import IAbstractPattern, IAbstractPatternDomain

@dataclasses.dataclass
class ExactPattern(IAbstractPattern):
    # -1 means Top
    idx: int
    sort: Kore.Sort



class ExactPatternDomain(IAbstractPatternDomain):
    pl: T.List[Kore.Pattern]
    rs: ReachabilitySystem

    def __init__(self, rs:ReachabilitySystem, patterns: T.List[Kore.Pattern]):
        for p in patterns:
            assert 0 == len(KoreUtils.free_evars_of_pattern(p))
        self.rs = rs
        self.pl = patterns 

    def abstract(self, c: Kore.Pattern) -> ExactPattern:
        sort = self.rs.kdw.sortof(c)
        for i,p in enumerate(self.pl):
            if p == c:
                return ExactPattern(idx=i, sort=sort)
        return ExactPattern(idx=-1, sort=sort)
    
    def is_top(self, a: IAbstractPattern) -> bool:
        assert type(a) is ExactPattern
        return a.idx == -1
    
    def concretize(self, a: IAbstractPattern) -> Kore.Pattern:
        assert type(a) is ExactPattern
        if self.is_top(a):
            return Kore.Top(a.sort)
        return self.pl[a.idx]

    def subsumes(self, a1: IAbstractPattern, a2: IAbstractPattern) -> bool:
        assert type(a1) is ExactPattern
        assert type(a2) is ExactPattern
        
        if a1.sort != a2.sort:
            return False

        if a2.idx == -1:
            return True

        if a1.idx == a2.idx:
            return True

        return self.rs.subsumes(self.concretize(a1), self.concretize(a2))[0]

    def print(self, a: IAbstractPattern) -> str:
        assert type(a) is ExactPattern
        return f'<idx={a.idx},sort={a.sort}>'