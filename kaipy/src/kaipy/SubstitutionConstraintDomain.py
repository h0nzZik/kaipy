import dataclasses
import typing as T

import pyk.kore.syntax as Kore

from kaipy.AbstractionContext import AbstractionContext
from kaipy.IAbstractConstraintDomain import IAbstractConstraint, IAbstractConstraintDomain
from kaipy.IAbstractSubstitutionDomain import IAbstractSubstitution, IAbstractSubstitutionDomain
from kaipy.Substitution import Substitution

@dataclasses.dataclass
class SubstitutionConstraint(IAbstractConstraint):
    nested: IAbstractSubstitution


class SubstitutionConstraintDomain(IAbstractConstraintDomain):
    nested: IAbstractSubstitutionDomain

    def __init__(self, nested: IAbstractSubstitutionDomain):
        self.nested = nested

    def abstract(self, ctx: AbstractionContext, c: T.List[Kore.MLPred]) -> IAbstractConstraint:
        eqls: T.Dict[Kore.EVar, Kore.Pattern] = dict()
        for p in c:
            match p:
                case Kore.Equals(_, _, Kore.EVar(_, _), Kore.EVar(_, _)):
                    continue
                case Kore.Equals(_, _, Kore.EVar(n, s), right):
                    dict[Kore.Evar(n,s)] = right
                    continue
                case Kore.Equals(_, _, left, Kore.EVar(n, s)):
                    dict[Kore.Evar(n,s)] = left

        subst = Substitution(immutabledict(eqls))
        a = SubstitutionConstraint(self.nested.abstract(ctx, subst))
        return a

    
    def refine(self, a: IAbstractConstraint, c: T.List[Kore.MLPred]) -> IAbstractConstraint:
        ...

    def concretize(self, a: IAbstractConstraint) -> T.List[Kore.MLPred]:
        ...

    def subsumes(self, a1: IAbstractConstraint, a2: IAbstractConstraint) -> bool:
        ...
    
    def to_str(self, a: IAbstractConstraint) -> str:
        ...
    
