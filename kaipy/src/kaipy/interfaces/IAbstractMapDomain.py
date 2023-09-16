import abc
import dataclasses
import typing as T

import pyk.kore.syntax as Kore

import kaipy.Properties as Properties
from kaipy.AbstractionContext import AbstractionContext



class IAbstractMap(abc.ABC):
    ...

class IAbstractMapDomain(abc.ABC):

    # Ignores properties other than those inheriting from MapProperty
    @abc.abstractmethod
    def abstract(self, ctx: AbstractionContext, properties: T.List[Properties.Property]) -> IAbstractMap:
        ...
    
    @abc.abstractmethod
    def concretize(self, a: IAbstractMap) -> T.List[Properties.Property]:
        ...

    @abc.abstractmethod
    def disjunction(self, ctx: AbstractionContext, a1: IAbstractMap, a2: IAbstractMap) -> IAbstractMap:
        ...
    
    @abc.abstractmethod
    def is_top(self, a: IAbstractMap) -> bool:
        ...

    @abc.abstractmethod
    def is_bottom(self, a: IAbstractMap) -> bool:
        ...

    @abc.abstractmethod
    def subsumes(self, a1: IAbstractMap, a2: IAbstractMap) -> bool:
        ...
    
    @abc.abstractmethod
    def equals(self, a1: IAbstractMap, a2: IAbstractMap) -> bool:
        ...
    
    @abc.abstractmethod
    def to_str(self, a: IAbstractMap, indent: int) -> str:
        ...
    
    @abc.abstractmethod
    def statistics(self) -> T.Dict[str, T.Any]:
        ...
