import abc
import typing as T

import pyk.kore.syntax as Kore

class IAbstractConstraint(abc.ABC):
    ...

class IAbstractConstraintDomain(abc.ABC):
    # preds is a list of predicates
    @abc.abstractmethod
    def abstract(preds: T.List[Kore.MLPred]) -> IAbstractConstraint:
        ...
    
    @abc.abstractmethod
    def concretize(a: IAbstractConstraint) -> T.List[Kore.MLPred]:
        ...
    
    @abc.abstractmethod
    def subsumes(a1, a2) -> bool:
        ...
    
    @abc.abstractmethod
    def to_str(a) -> str:
        ...