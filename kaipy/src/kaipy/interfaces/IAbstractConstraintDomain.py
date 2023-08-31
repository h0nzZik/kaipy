import abc
import typing as T

import pyk.kore.syntax as Kore

from kaipy.AbstractionContext import AbstractionContext

class IAbstractConstraint(abc.ABC):
    ...

class IAbstractConstraintDomain(abc.ABC):
    # preds is a list of predicates
    # pre: ctx.variable_manager yields only variables not occurring in `c`
    @abc.abstractmethod
    def abstract(self, ctx: AbstractionContext, c: T.List[Kore.MLPred]) -> IAbstractConstraint:
        ...
    
    @abc.abstractmethod
    def refine(self, ctx: AbstractionContext, a: IAbstractConstraint, c: T.List[Kore.MLPred]) -> IAbstractConstraint:
        ...

    # Requirement: FV(concretize(disjunction(ctx, a1, a2))) \subseteq FV(concretize(a1)) \cup FV(concretize(a2)).
    # In other words, disjunction is not allowed to invent variables.
    # Therefore, it shall not use ctx.variable_manager to create any.
    @abc.abstractmethod
    def disjunction(self, ctx: AbstractionContext, a1: IAbstractConstraint, a2: IAbstractConstraint) -> IAbstractConstraint:
        ...

    @abc.abstractmethod
    def concretize(self, a: IAbstractConstraint) -> T.List[Kore.MLPred]:
        ...
    
    @abc.abstractmethod
    def is_top(self, a: IAbstractConstraint) -> bool:
        ...

    @abc.abstractmethod
    def is_bottom(self, a: IAbstractConstraint) -> bool:
        ...

    @abc.abstractmethod
    def subsumes(self, a1: IAbstractConstraint, a2: IAbstractConstraint) -> bool:
        ...
    
    @abc.abstractmethod
    def equals(self, a1: IAbstractConstraint, a2: IAbstractConstraint) -> bool:
        ...

    @abc.abstractmethod
    def to_str(self, a: IAbstractConstraint) -> str:
        ...