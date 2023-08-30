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
    def refine(self, ctx: AbstractionContext, a: IAbstractPattern, c: Kore.Pattern) -> IAbstractPattern:
        ...

    @abc.abstractmethod
    def is_top(self, a: IAbstractPattern) -> bool:
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
    
    # TODO rename to `to_str`
    @abc.abstractmethod
    def print(self, a: IAbstractPattern) -> str:
        ...