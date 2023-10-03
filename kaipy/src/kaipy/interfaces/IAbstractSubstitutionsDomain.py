import abc
import typing as T

import pyk.kore.syntax as Kore

from kaipy.Substitution import Substitution
from kaipy.AbstractionContext import AbstractionContext

class IAbstractSubstitutions(abc.ABC):
    ...

class IAbstractSubstitutionsDomain(abc.ABC):
    
    # pre: ctx.variable_manager yields only variables not occurring in `subst`
    @abc.abstractmethod
    def abstract(self, ctx: AbstractionContext, substs: T.List[Substitution]) -> IAbstractSubstitutions:
        ...
    
    @abc.abstractmethod
    def free_variables_of(self, a: IAbstractSubstitutions) -> T.Set[Kore.EVar]:
        ...

    @abc.abstractmethod
    def disjunction(self, ctx: AbstractionContext, a1: IAbstractSubstitutions, a2: IAbstractSubstitutions) -> IAbstractSubstitutions:
        ...

    @abc.abstractmethod
    def refine(self, ctx: AbstractionContext, a: IAbstractSubstitutions, constraints: T.List[Kore.Pattern]) -> IAbstractSubstitutions:
        ...

    @abc.abstractmethod
    def concretize(self, a: IAbstractSubstitutions) -> T.List[Substitution]:
        ...

    @abc.abstractmethod
    def equals(self, a1: IAbstractSubstitutions, a2: IAbstractSubstitutions) -> bool:
        ...

    @abc.abstractmethod
    def subsumes(self, a1: IAbstractSubstitutions, a2: IAbstractSubstitutions) -> bool:
        ...
    
    @abc.abstractmethod
    def is_top(self, a: IAbstractSubstitutions) -> bool:
        ...

    @abc.abstractmethod
    def is_bottom(self, a: IAbstractSubstitutions) -> bool:
        ...

    @abc.abstractmethod
    def to_str(self, a: IAbstractSubstitutions, indent: int) -> str:
        ...
    
    @abc.abstractmethod
    def statistics(self) -> T.Dict[str, T.Any]:
        ...
    
