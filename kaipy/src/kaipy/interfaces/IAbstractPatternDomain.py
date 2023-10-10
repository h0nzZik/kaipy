import abc
import typing as T

import pyk.kore.syntax as Kore

from kaipy.AbstractionContext import AbstractionContext

class IAbstractPattern(abc.ABC):
    ...

class IAbstractPatternDomain(abc.ABC):
    # pre: ctx.variable_manager yields only variables not occurring in `c`
    @abc.abstractmethod
    def abstract(self, ctx: AbstractionContext,  c: Kore.Pattern) -> IAbstractPattern:
        ...

    @abc.abstractmethod
    def free_variables_of(self, a: IAbstractPattern) -> T.Set[Kore.EVar]:
        ...

    @abc.abstractmethod
    def disjunction(self, ctx: AbstractionContext, a1: IAbstractPattern, a2: IAbstractPattern) -> IAbstractPattern:
        ...


    @abc.abstractmethod
    def is_top(self, a: IAbstractPattern) -> bool:
        ...

    @abc.abstractmethod
    def is_bottom(self, a: IAbstractPattern) -> bool:
        ...

    @abc.abstractmethod
    def concretize(self, a: IAbstractPattern) -> Kore.Pattern:
        ...

    @abc.abstractmethod
    def equals(self, a1: IAbstractPattern, a2: IAbstractPattern) -> bool:
        ...

    @abc.abstractmethod
    def subsumes(self, a1: IAbstractPattern, a2: IAbstractPattern) -> bool:
        ...
    
    @abc.abstractmethod
    def to_str(self, a: IAbstractPattern, indent: int) -> str:
        ...
    
    @abc.abstractmethod
    def statistics(self) -> T.Dict[str, T.Any]:
        ...