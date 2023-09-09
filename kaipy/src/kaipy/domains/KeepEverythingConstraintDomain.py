import abc
import dataclasses
import itertools
import typing as T

import pyk.kore.syntax as Kore

import kaipy.kore_utils as KoreUtils
from kaipy.AbstractionContext import AbstractionContext
from kaipy.interfaces.IAbstractConstraintDomain import IAbstractConstraint, IAbstractConstraintDomain

@dataclasses.dataclass
class KeepEverything(IAbstractConstraint):
    everything: T.List[Kore.Pattern]

class KeepEverythingConstraintDomain(IAbstractConstraintDomain):
    def abstract(self, ctx: AbstractionContext, over_variables: T.Set[Kore.EVar], constraints: T.List[Kore.Pattern]) -> IAbstractConstraint:
        return KeepEverything(everything=constraints)
    
    def free_variables_of(self, a: IAbstractConstraint) -> T.Set[Kore.EVar]:
        assert type(a) is KeepEverything
        return set(*itertools.chain(*[KoreUtils.free_evars_of_pattern(p) for p in a.everything]))

    def refine(self, ctx: AbstractionContext, a: IAbstractConstraint, constraints: T.List[Kore.Pattern]) -> IAbstractConstraint:
        return a

    def disjunction(self, ctx: AbstractionContext, a1: IAbstractConstraint, a2: IAbstractConstraint) -> IAbstractConstraint:
        raise NotImplementedError()

    def concretize(self, a: IAbstractConstraint) -> T.List[Kore.Pattern]:
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
