import abc
import typing as T

import pyk.kore.syntax as Kore

from kaipy.interfaces.IAbstractConstraintDomain import IAbstractConstraintDomain

class IAbstractConstraintDomainBuilder(abc.ABC):

    @abc.abstractmethod
    def build_abstract_constraint_domain(self, over_variables: T.Set[Kore.EVar]) -> IAbstractConstraintDomain:
        ...