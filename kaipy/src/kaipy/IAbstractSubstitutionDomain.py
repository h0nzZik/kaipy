import abc
import typing as T

import pyk.kore.syntax as Kore

from kaipy.Substitution import Substitution
from kaipy.AbstractionContext import AbstractionContext

class IAbstractSubstitution(abc.ABC):
    ...

class IAbstractSubstitutionDomain(abc.ABC):
    @abc.abstractmethod
    def concretize(self, a: IAbstractSubstitution) -> T.Tuple[Substitution, T.List[Kore.Pattern]]:
        ...
    
    # pre: ctx.variable_manager yields only variables not occurring in `subst`
    @abc.abstractmethod
    def abstract(self, ctx: AbstractionContext, subst: Substitution) -> IAbstractSubstitution:
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
