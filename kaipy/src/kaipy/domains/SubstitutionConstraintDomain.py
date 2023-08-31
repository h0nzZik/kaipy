import dataclasses
import typing as T
from immutabledict import immutabledict

import pyk.kore.syntax as Kore

from kaipy.ReachabilitySystem import ReachabilitySystem
from kaipy.AbstractionContext import AbstractionContext
from kaipy.interfaces.IAbstractConstraintDomain import IAbstractConstraint, IAbstractConstraintDomain
from kaipy.interfaces.IAbstractSubstitutionDomain import IAbstractSubstitution, IAbstractSubstitutionDomain
from kaipy.interfaces.IAbstractConstraintDomainBuilder import IAbstractConstraintDomainBuilder
from kaipy.Substitution import Substitution

@dataclasses.dataclass
class SubstitutionConstraint(IAbstractConstraint):
    nested: IAbstractSubstitution


class SubstitutionConstraintDomain(IAbstractConstraintDomain):
    nested: IAbstractSubstitutionDomain
    rs: ReachabilitySystem
    evars: T.Set[Kore.EVar]

    def __init__(
        self,
        rs: ReachabilitySystem,
        nested: IAbstractSubstitutionDomain,
        evars: T.Set[Kore.EVar],
    ):
        self.nested = nested
        self.rs = rs
        self.evars = evars

    def abstract(self, ctx: AbstractionContext, c: T.List[Kore.MLPred]) -> IAbstractConstraint:
        eqls: T.Dict[Kore.EVar, Kore.Pattern] = dict()
        for p in c:
            match p:
                case Kore.Equals(_, _, Kore.EVar(_, _), Kore.EVar(_, _)):
                    continue
                case Kore.Equals(_, _, Kore.EVar(n, s), right):
                    if Kore.EVar(n,s) in self.evars:
                        eqls[Kore.EVar(n,s)] = right
                case Kore.Equals(_, _, left, Kore.EVar(n, s)):
                    if Kore.EVar(n,s) in self.evars:
                        eqls[Kore.EVar(n,s)] = left

        subst = Substitution(immutabledict(eqls))
        a = SubstitutionConstraint(self.nested.abstract(ctx, subst))
        return a

    
    def refine(self, ctx: AbstractionContext, a: IAbstractConstraint, c: T.List[Kore.MLPred]) -> SubstitutionConstraint:
        assert type(a) is SubstitutionConstraint
        new_nested = self.nested.refine(ctx, a.nested, c)
        new_a = SubstitutionConstraint(new_nested)
        return new_a

    def disjunction(self, ctx: AbstractionContext, a1: IAbstractConstraint, a2: IAbstractConstraint) -> SubstitutionConstraint:
        assert type(a1) is SubstitutionConstraint
        assert type(a2) is SubstitutionConstraint
        return SubstitutionConstraint(self.nested.disjunction(ctx, a1.nested, a2.nested))

    def concretize(self, a: IAbstractConstraint) -> T.List[Kore.MLPred]:
        assert type(a) is SubstitutionConstraint
        concrete_subst = self.nested.concretize(a.nested)
        return [ Kore.Equals(k.sort, self.rs.top_sort, k, v) for k,v in concrete_subst.mapping.items()]

    def subsumes(self, a1: IAbstractConstraint, a2: IAbstractConstraint) -> bool:
        assert type(a1) is SubstitutionConstraint
        assert type(a2) is SubstitutionConstraint
        return self.nested.subsumes(a1.nested, a2.nested)
    
    def equals(self, a1: IAbstractConstraint, a2: IAbstractConstraint) -> bool:
        assert type(a1) is SubstitutionConstraint
        assert type(a2) is SubstitutionConstraint
        return self.nested.equals(a1.nested, a2.nested)

    def is_top(self, a: IAbstractConstraint) -> bool:
        assert type(a) is SubstitutionConstraint
        return self.nested.is_top(a.nested)

    def is_bottom(self, a: IAbstractConstraint) -> bool:
        assert type(a) is SubstitutionConstraint
        return self.nested.is_bottom(a.nested)
    
    def to_str(self, a: IAbstractConstraint) -> str:
        assert type(a) is SubstitutionConstraint
        return f'<sc: {self.nested.to_str(a.nested)}>'
    


class SubstitutionConstraintDomainBuilder(IAbstractConstraintDomainBuilder):
    nested: IAbstractSubstitutionDomain
    rs: ReachabilitySystem

    def __init__(self, nested: IAbstractSubstitutionDomain, rs: ReachabilitySystem):
        self.nested = nested
        self.rs = rs
    
    def build_abstract_constraint_domain(self, over_variables: T.Set[Kore.EVar]) -> SubstitutionConstraintDomain:
        return SubstitutionConstraintDomain(
            rs=self.rs,
            nested=self.nested,
            evars=over_variables,
        )