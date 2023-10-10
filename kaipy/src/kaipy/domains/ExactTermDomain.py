import dataclasses
import logging
import time
import typing as T

import pyk.kore.syntax as Kore

from kaipy.PerfCounter import PerfCounter
import kaipy.kore_utils as KoreUtils
from kaipy.AbstractionContext import AbstractionContext
from kaipy.ReachabilitySystem import ReachabilitySystem
from kaipy.interfaces.IAbstractPatternDomain import IAbstractPattern, IAbstractPatternDomain

_LOGGER: T.Final = logging.getLogger(__name__)

@dataclasses.dataclass(frozen=True)
class ExactTerm(IAbstractPattern):
    # -1 means Top
    idx: int
    sort: Kore.Sort



class ExactTermDomain(IAbstractPatternDomain):
    pl: T.List[Kore.Pattern]
    rs: ReachabilitySystem
    abstract_perf_counter: PerfCounter

    def __init__(self, rs:ReachabilitySystem, patterns: T.List[Kore.Pattern]):
        for p in patterns:
            assert 0 == len(KoreUtils.free_evars_of_pattern(p))
        self.rs = rs
        self.pl = patterns 
        self.abstract_perf_counter = PerfCounter()

    def abstract(self, ctx: AbstractionContext, c: Kore.Pattern) -> ExactTerm:
        old = time.perf_counter()
        a = self._abstract(ctx, c)
        new = time.perf_counter()
        self.abstract_perf_counter.add(new - old)
        return a

    def _abstract(self, ctx: AbstractionContext, c: Kore.Pattern) -> ExactTerm:
        sort = self.rs.kdw.sortof(c)
        for i,p in enumerate(self.pl):
            if p == c:
                return ExactTerm(idx=i, sort=sort)
        #_LOGGER.warning(f"Exact: not catching {c.text}")
        return ExactTerm(idx=-1, sort=sort)
    
    def free_variables_of(self, a: IAbstractPattern) -> T.Set[Kore.EVar]:
        assert type(a) is ExactTerm
        return set()

    def is_top(self, a: IAbstractPattern) -> bool:
        assert type(a) is ExactTerm
        return a.idx == -1
    
    def is_bottom(self, a: IAbstractPattern) -> bool:
        return False

    def concretize(self, a: IAbstractPattern) -> Kore.Pattern:
        assert type(a) is ExactTerm
        if self.is_top(a):
            return Kore.Top(a.sort)
        return self.pl[a.idx]

    def equals(self, a1: IAbstractPattern, a2: IAbstractPattern) -> bool:
        assert type(a1) is ExactTerm
        assert type(a2) is ExactTerm
        return a1.idx == a2.idx

    def disjunction(self, ctx: AbstractionContext, a1: IAbstractPattern, a2: IAbstractPattern) -> ExactTerm:
        assert type(a1) is ExactTerm
        assert type(a2) is ExactTerm

        if a1.idx == a2.idx and a1.sort == a2.sort:
            return a1

        return ExactTerm(idx=-1, sort=a1.sort)

    def subsumes(self, a1: IAbstractPattern, a2: IAbstractPattern) -> bool:
        assert type(a1) is ExactTerm
        assert type(a2) is ExactTerm
        
        if a1.sort != a2.sort:
            return False

        if a2.idx == -1:
            return True

        if a1.idx == a2.idx:
            return True

        return self.rs.subsumes(self.concretize(a1), self.concretize(a2))[0]

    def to_str(self, a: IAbstractPattern, indent: int) -> str:
        assert type(a) is ExactTerm
        return (indent*' ') + f'<idx={a.idx},sort={a.sort}>'

    def statistics(self) -> T.Dict[str, T.Any]:
        return {
            'name' : 'ExactTermDomain',
            'abstract' : self.abstract_perf_counter.dict,
        }