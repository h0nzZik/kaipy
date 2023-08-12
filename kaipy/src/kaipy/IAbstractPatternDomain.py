import abc

import pyk.kore.syntax as Kore

class IAbstractPattern(abc.ABC):
    ...

class IAbstractPatternDomain(abc.ABC):
    @abc.abstractmethod
    def abstract(self, c: Kore.Pattern) -> IAbstractPattern:
        ...

    @abc.abstractmethod
    def is_top(self, a: IAbstractPattern) -> bool:
        ...

    @abc.abstractmethod
    def concretize(self, a: IAbstractPattern) -> Kore.Pattern:
        ...
    
    @abc.abstractmethod
    def subsumes(self, a1: IAbstractPattern, a2: IAbstractPattern) -> bool:
        ...
    
    # TODO rename to `to_str`
    @abc.abstractmethod
    def print(self, a: IAbstractPattern) -> str:
        ...