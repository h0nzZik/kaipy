import abc
import dataclasses
import itertools
import time
import typing as T


import pyk.kore.syntax as Kore

import kaipy.kore_utils as KoreUtils
from kaipy.PerfCounter import PerfCounter
from kaipy.ReachabilitySystem import ReachabilitySystem
from kaipy.interfaces.IAbstractConstraintDomain import IAbstractConstraint, IAbstractConstraintDomain
from kaipy.AbstractionContext import AbstractionContext
from kaipy.cnf import to_cnf

@dataclasses.dataclass
class Disjunction(IAbstractConstraint):
    elements: T.List[IAbstractConstraint]

class DisjunctiveConstraintDomain(IAbstractConstraintDomain):
    underlying: IAbstractConstraintDomain
    rs: ReachabilitySystem
    abstract_perf_counter: PerfCounter

    def __init__(self, underlying: IAbstractConstraintDomain, rs: ReachabilitySystem):
        self.underlying = underlying
        self.rs = rs
        self.abstract_perf_counter = PerfCounter()

    def abstract(self, ctx: AbstractionContext, over_variables: T.Set[Kore.EVar], constraints: T.List[Kore.Pattern]) -> Disjunction:
        old = time.perf_counter()
        a = self._abstract(ctx, over_variables, constraints)
        new = time.perf_counter()
        self.abstract_perf_counter.add(new - old)
        return a

    def _abstract(self, ctx: AbstractionContext, over_variables: T.Set[Kore.EVar], constraints: T.List[Kore.Pattern]) -> Disjunction:
        conj = KoreUtils.make_conjunction(self.rs.top_sort, constraints)
        conj_simpl = self.rs.simplify(conj)
        disj = KoreUtils.or_to_list(conj_simpl)
        return Disjunction(
            [
                self.underlying.abstract(ctx, over_variables, KoreUtils.and_to_list(d))
                for d in disj
            ]
        )
    
    def free_variables_of(self, a: IAbstractConstraint) -> T.Set[Kore.EVar]:
        assert type(a) is Disjunction
        return set(itertools.chain(*[self.underlying.free_variables_of(e) for e in a.elements]))

    def disjunction(self, ctx: AbstractionContext, a1: IAbstractConstraint, a2: IAbstractConstraint) -> Disjunction:
        assert type(a1) is Disjunction
        assert type(a2) is Disjunction
        elements: T.List[IAbstractConstraint] = a1.elements.copy()
        for e2 in a2.elements:
            skip: bool = False
            for e1 in elements:
                if self.underlying.subsumes(e1, e2):
                    skip = True
                    break
            if not skip:
                elements.append(e2)
        return Disjunction(elements)

    def concretize(self, a: IAbstractConstraint) -> T.List[Kore.Pattern]:
        assert type(a) is Disjunction
        cs = [
            self.underlying.concretize(e)
            for e in a.elements
        ]
        csc = [
            KoreUtils.make_conjunction(self.rs.top_sort, x)
            for x in cs
            if len(x) > 0
        ]
        if len(csc) <= 0:
            return [Kore.Bottom(self.rs.top_sort)]

        disj = KoreUtils.make_disjunction(self.rs.top_sort, csc)
        cnf = to_cnf(disj, self.rs.top_sort)
        return KoreUtils.and_to_list(cnf)
    
    def is_top(self, a: IAbstractConstraint) -> bool:
        assert type(a) is Disjunction
        return any([self.underlying.is_top(e) for e in a.elements])

    def is_bottom(self, a: IAbstractConstraint) -> bool:
        assert type(a) is Disjunction
        return all([self.underlying.is_bottom(e) for e in a.elements])

    def subsumes(self, a1: IAbstractConstraint, a2: IAbstractConstraint) -> bool:
        assert type(a1) is Disjunction
        assert type(a2) is Disjunction
        for e1 in a1.elements:
            found: bool = False
            for e2 in a2.elements:
                if self.underlying.subsumes(e1, e2):
                    found = True
                    break
            if not found:
                return False
        return True
    
    def equals(self, a1: IAbstractConstraint, a2: IAbstractConstraint) -> bool:
        assert type(a1) is Disjunction
        assert type(a2) is Disjunction
        for e1 in a1.elements:
            found: bool = False
            for e2 in a2.elements:
                if self.underlying.equals(e1, e2):
                    found = True
                    break
            if not found:
                return False
        return True

    def to_str(self, a: IAbstractConstraint, indent: int) -> str:
        assert type(a) is Disjunction
        s = (indent*' ') + "<disj\n"
        for e in a.elements:
            s = s + self.underlying.to_str(e, indent=indent+1) + ",\n"
        s = s + (indent*' ') + ">"
        return s
    
    def statistics(self) -> T.Dict[str, T.Any]:
        return {
            'name' : 'DisjunctiveConstraintDomain',
            'abstract' : self.abstract_perf_counter.dict,
            'underlying' : [self.underlying.statistics()]
        }