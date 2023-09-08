import abc
import dataclasses
import typing as T

import pyk.kore.syntax as Kore

from kaipy.AbstractionContext import AbstractionContext
from kaipy.interfaces.IAbstractConstraintDomainBuilder import IAbstractConstraintDomainBuilder
from kaipy.interfaces.IAbstractConstraintDomain import IAbstractConstraint, IAbstractConstraintDomain

@dataclasses.dataclass
class KeepEverything(IAbstractConstraint):
    everything: T.List[Kore.MLPred]

class KeepEverythingConstraintDomain(IAbstractConstraintDomain):
    def abstract(self, ctx: AbstractionContext, c: T.List[Kore.MLPred]) -> IAbstractConstraint:
        return KeepEverything(everything=c)
    
    def refine(self, ctx: AbstractionContext, a: IAbstractConstraint, c: T.List[Kore.MLPred]) -> IAbstractConstraint:
        return a

    def disjunction(self, ctx: AbstractionContext, a1: IAbstractConstraint, a2: IAbstractConstraint) -> IAbstractConstraint:
        raise NotImplementedError()

    def concretize(self, a: IAbstractConstraint) -> T.List[Kore.MLPred]:
        assert type(a) is KeepEverything
        return a.everything
    
    def is_top(self, a: IAbstractConstraint) -> bool:
        assert type(a) is KeepEverything
        return len(a.everything) <= 0

    def is_bottom(self, a: IAbstractConstraint) -> bool:
        assert type(a) is KeepEverything
        return False

    def subsumes(self, a1: IAbstractConstraint, a2: IAbstractConstraint) -> bool:
        assert type(a1) is KeepEverything
        assert type(a2) is KeepEverything
        raise NotImplementedError()
    
    def equals(self, a1: IAbstractConstraint, a2: IAbstractConstraint) -> bool:
        assert type(a1) is KeepEverything
        assert type(a2) is KeepEverything
        return a1.everything == a2.everything

    def to_str(self, a: IAbstractConstraint, indent: int) -> str:
        assert type(a) is KeepEverything
        return str([x.text for x in a.everything])



class KeepEverythingConstraintDomainBuilder(IAbstractConstraintDomainBuilder):
    def build_abstract_constraint_domain(self, over_variables: T.Set[Kore.EVar]) -> IAbstractConstraintDomain:
        return KeepEverythingConstraintDomain()