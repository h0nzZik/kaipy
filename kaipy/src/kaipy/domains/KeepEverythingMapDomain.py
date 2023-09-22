import abc
import dataclasses
import typing as T

import pyk.kore.syntax as Kore

import kaipy.Properties as Properties
from kaipy.interfaces.IAbstractMapDomain import IAbstractMap, IAbstractMapDomain
from kaipy.AbstractionContext import AbstractionContext

@dataclasses.dataclass
class KeepEverythingMap(IAbstractMap):
    properties: T.List[Properties.Property]

class KeepEverythingMapDomain(IAbstractMapDomain):

    def abstract(self, ctx: AbstractionContext, properties: T.List[Properties.Property]) -> IAbstractMap:
        return KeepEverythingMap(properties=[p for p in properties if issubclass(type(p), Properties.MapProperty)])
    
    def concretize(self, a: IAbstractMap) -> T.List[Properties.Property]:
        assert type(a) is KeepEverythingMap
        return a.properties

    def disjunction(self, ctx: AbstractionContext, a1: IAbstractMap, a2: IAbstractMap) -> IAbstractMap:
        assert type(a1) is KeepEverythingMap
        assert type(a2) is KeepEverythingMap
        return KeepEverythingMap(properties=a1.properties+a2.properties)
    
    def is_top(self, a: IAbstractMap) -> bool:
        assert type(a) is KeepEverythingMap
        return len(a.properties) == 0

    def is_bottom(self, a: IAbstractMap) -> bool:
        return False
 
    def subsumes(self, a1: IAbstractMap, a2: IAbstractMap) -> bool:
        assert type(a1) is KeepEverythingMap
        assert type(a2) is KeepEverythingMap
        for p in a1.properties:
            if p not in a2.properties:
                return False
        return True
    
    def equals(self, a1: IAbstractMap, a2: IAbstractMap) -> bool:
        return self.subsumes(a1, a2) and self.subsumes(a2, a1)
    
    def to_str(self, a: IAbstractMap, indent: int) -> str:
        raise NotImplementedError()
    
    def statistics(self) -> T.Dict[str, T.Any]:
        return dict()
