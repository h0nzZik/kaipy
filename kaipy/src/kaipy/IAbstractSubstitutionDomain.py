import abc
import typing as T

import pyk.kore.syntax as Kore

from kaipy.Substitution import Substitution

class IAbstractSubstitution(abc.ABC):
    ...

class IAbstractSubstitutionDomain(abc.ABC):
    @abc.abstractmethod
    def concretize(self, a: IAbstractSubstitution) -> Substitution:
        ...
    
    @abc.abstractmethod
    def abstract(self, subst: Substitution) -> IAbstractSubstitution:
        ...

    @abc.abstractmethod
    def equals(self, a1: IAbstractSubstitution, a2: IAbstractSubstitution) -> bool:
        ...

    @abc.abstractmethod
    def subsumes(self, a1: IAbstractSubstitution, a2: IAbstractSubstitution) -> bool:
        ...
    
    @abc.abstractmethod
    def print(self, a: IAbstractSubstitution) -> str:
        ...
