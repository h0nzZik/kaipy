import abc
import typing as T

import pyk.kore.syntax as Kore

from kaipy.Substitution import Substitution
from kaipy.AbstractionContext import AbstractionContext

class IAbstractSubstitution(abc.ABC):
    ...

class IAbstractSubstitutionDomain(abc.ABC):
    
    # pre: ctx.variable_manager yields only variables not occurring in `subst`
    @abc.abstractmethod
    def abstract(self, ctx: AbstractionContext, subst: Substitution) -> IAbstractSubstitution:
        ...
    
    @abc.abstractmethod
    def disjunction(self, ctx: AbstractionContext, a1: IAbstractSubstitution, a2: IAbstractSubstitution) -> IAbstractSubstitution:
        ...

    @abc.abstractmethod
    def refine(self, ctx: AbstractionContext, a: IAbstractSubstitution, c: T.List[Kore.MLPred]) -> IAbstractSubstitution:
        ...

    @abc.abstractmethod
    def concretize(self, a: IAbstractSubstitution) -> Substitution:
        ...

    @abc.abstractmethod
    def equals(self, a1: IAbstractSubstitution, a2: IAbstractSubstitution) -> bool:
        ...

    @abc.abstractmethod
    def subsumes(self, a1: IAbstractSubstitution, a2: IAbstractSubstitution) -> bool:
        ...
    
    @abc.abstractmethod
    def is_top(self, a: IAbstractSubstitution) -> bool:
        ...

    @abc.abstractmethod
    def is_bottom(self, a: IAbstractSubstitution) -> bool:
        ...

    @abc.abstractmethod
    def to_str(self, a: IAbstractSubstitution, indent: int) -> str:
        ...
