import abc
import time
import typing as T
import logging

import pyk.kore.syntax as Kore

from kaipy.AbstractionContext import AbstractionContext
from kaipy.PerfCounter import PerfCounter
from kaipy.interfaces.IAbstractConstraintDomain import IAbstractConstraint, IAbstractConstraintDomain


_LOGGER: T.Final = logging.getLogger(__name__)

class CachedConstraintDomain(IAbstractConstraintDomain):
    cache: T.Dict[T.FrozenSet[Kore.Pattern], IAbstractConstraint]
    underlying: IAbstractConstraintDomain
    abstract_perf_counter: PerfCounter

    def __init__(self, underlying: IAbstractConstraintDomain):
        self.cache = dict()
        self.underlying = underlying
        self.abstract_perf_counter = PerfCounter()

    def abstract(self, ctx: AbstractionContext, over_variables: T.Set[Kore.EVar], constraints: T.List[Kore.Pattern]) -> IAbstractConstraint:
        old = time.perf_counter()
        a = self._abstract(ctx, over_variables, constraints)
        new = time.perf_counter()
        self.abstract_perf_counter.add(new - old)
        return a

    def _abstract(self, ctx: AbstractionContext, over_variables: T.Set[Kore.EVar], constraints: T.List[Kore.Pattern]) -> IAbstractConstraint:
        sc = frozenset(constraints)
        if sc in self.cache.keys():
            return self.cache[sc]

        #_LOGGER.warning(f"**** CACHE MISS: {[x.text for x in sc]}")        
        a = self.underlying.abstract(ctx, over_variables=over_variables, constraints=constraints)
        self.cache[sc] = a
        return a

    def free_variables_of(self, a: IAbstractConstraint) -> T.Set[Kore.EVar]:
        return self.underlying.free_variables_of(a)

    def disjunction(self, ctx: AbstractionContext, a1: IAbstractConstraint, a2: IAbstractConstraint) -> IAbstractConstraint:
        return self.underlying.disjunction(ctx, a1, a2)

    def concretize(self, a: IAbstractConstraint) -> T.List[Kore.Pattern]:
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

    def statistics(self) -> T.Dict[str, T.Any]:
        return {
            'name' : 'CachedConstraintDomain',
            'abstract' : self.abstract_perf_counter.dict,
            'underlying': [self.underlying.statistics()]
        }
