import dataclasses
import typing as T
from immutabledict import immutabledict

import pyk.kore.syntax as Kore

from kaipy.ReachabilitySystem import ReachabilitySystem
from kaipy.AbstractionContext import AbstractionContext
from kaipy.IAbstractConstraintDomain import IAbstractConstraint, IAbstractConstraintDomain
from kaipy.IAbstractSubstitutionDomain import IAbstractSubstitution, IAbstractSubstitutionDomain
from kaipy.Substitution import Substitution

@dataclasses.dataclass
class SubstitutionConstraint(IAbstractConstraint):
    nested: IAbstractSubstitution


class SubstitutionConstraintDomain(IAbstractConstraintDomain):
    nested: IAbstractSubstitutionDomain
    rs: ReachabilitySystem

    def __init__(self, rs: ReachabilitySystem, nested: IAbstractSubstitutionDomain):
        self.nested = nested
        self.rs = rs

    def abstract(self, ctx: AbstractionContext, c: T.List[Kore.MLPred]) -> IAbstractConstraint:
        eqls: T.Dict[Kore.EVar, Kore.Pattern] = dict()
        for p in c:
            match p:
                case Kore.Equals(_, _, Kore.EVar(_, _), Kore.EVar(_, _)):
                    continue
                case Kore.Equals(_, _, Kore.EVar(n, s), right):
                    eqls[Kore.EVar(n,s)] = right
                    continue
                case Kore.Equals(_, _, left, Kore.EVar(n, s)):
                    eqls[Kore.EVar(n,s)] = left

        subst = Substitution(immutabledict(eqls))
        a = SubstitutionConstraint(self.nested.abstract(ctx, subst))
        return a

    
    def refine(self, a: IAbstractConstraint, c: T.List[Kore.MLPred]) -> IAbstractConstraint:
        assert type(a) is SubstitutionConstraint
        new_nested = self.nested.refine(a.nested, c)
        new_a = SubstitutionConstraint(new_nested)
        return new_a

    def concretize(self, a: IAbstractConstraint) -> T.List[Kore.MLPred]:
        assert type(a) is SubstitutionConstraint
        concrete_subst = self.nested.concretize(a.nested)
        return [ Kore.Equals(k.sort, self.rs.top_sort, k, v) for k,v in concrete_subst.mapping.items()]

    def subsumes(self, a1: IAbstractConstraint, a2: IAbstractConstraint) -> bool:
        assert type(a1) is SubstitutionConstraint
        assert type(a2) is SubstitutionConstraint
        return self.nested.subsumes(a1.nested, a2.nested)
    
    def to_str(self, a: IAbstractConstraint) -> str:
        assert type(a) is SubstitutionConstraint
        return f'<sc: {self.nested.print(a.nested)}>'
    
