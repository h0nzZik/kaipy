import dataclasses
import typing as T
import logging
from immutabledict import immutabledict

import pyk.kore.syntax as Kore

import kaipy.kore_utils as KoreUtils
import kaipy.rs_utils as RSUtils
from kaipy.ReachabilitySystem import ReachabilitySystem
from kaipy.AbstractionContext import AbstractionContext
from kaipy.interfaces.IAbstractConstraintDomain import IAbstractConstraint, IAbstractConstraintDomain
from kaipy.interfaces.IAbstractSubstitutionsDomain import IAbstractSubstitutions, IAbstractSubstitutionsDomain
from kaipy.interfaces.IAbstractConstraintDomainBuilder import IAbstractConstraintDomainBuilder
from kaipy.Substitution import Substitution
from kaipy.cnf import to_cnf


_LOGGER: T.Final = logging.getLogger(__name__)

@dataclasses.dataclass
class SubstitutionsConstraint(IAbstractConstraint):
    nested: IAbstractSubstitutions


class SubstitutionsConstraintDomain(IAbstractConstraintDomain):
    nested: IAbstractSubstitutionsDomain
    rs: ReachabilitySystem
    evars: T.Set[Kore.EVar]

    def __init__(
        self,
        rs: ReachabilitySystem,
        nested: IAbstractSubstitutionsDomain,
        evars: T.Set[Kore.EVar],
    ):
        self.nested = nested
        self.rs = rs
        self.evars = evars
        #_LOGGER.warning(f"SCD evars: {self.evars}")


    def abstract(self, ctx: AbstractionContext, c: T.List[Kore.MLPred]) -> IAbstractConstraint:
        eqls: T.Dict[Kore.EVar, Kore.Pattern] = dict()
        for p in c:
            match p:
                case Kore.Equals(_, _, Kore.EVar(_, _), Kore.EVar(_, _)):
                    continue
                case Kore.Equals(_, _, Kore.EVar(n, s), right):
                    if Kore.EVar(n,s) in self.evars:
                        eqls[Kore.EVar(n,s)] = right
                    else:
                        _LOGGER.warning(f"Unknown variable {n}:{s}")
                case Kore.Equals(_, _, left, Kore.EVar(n, s)):
                    if Kore.EVar(n,s) in self.evars:
                        eqls[Kore.EVar(n,s)] = left
                    else:
                        _LOGGER.warning(f"Unknown variable {n}:{s}")

        subst = Substitution(immutabledict(eqls))
        a = SubstitutionsConstraint(self.nested.abstract(ctx, [subst]))
        return a

    
    def refine(self, ctx: AbstractionContext, a: IAbstractConstraint, c: T.List[Kore.MLPred]) -> SubstitutionsConstraint:
        assert type(a) is SubstitutionsConstraint
        new_nested = self.nested.refine(ctx, a.nested, c)
        new_a = SubstitutionsConstraint(new_nested)
        return new_a

    def disjunction(self, ctx: AbstractionContext, a1: IAbstractConstraint, a2: IAbstractConstraint) -> SubstitutionsConstraint:
        assert type(a1) is SubstitutionsConstraint
        assert type(a2) is SubstitutionsConstraint
        return SubstitutionsConstraint(self.nested.disjunction(ctx, a1.nested, a2.nested))

    def concretize(self, a: IAbstractConstraint) -> T.List[Kore.MLPred]:
        assert type(a) is SubstitutionsConstraint
        concrete_substs = self.nested.concretize(a.nested)
        atoms = [ [Kore.Equals(k.sort, self.rs.top_sort, k, v) for k,v in s.mapping.items()] for s in concrete_substs]
        dnf = KoreUtils.make_disjunction(self.rs.top_sort, [ KoreUtils.make_conjunction(self.rs.top_sort, dclause) for dclause in atoms])
        cnf = to_cnf(dnf, sort=self.rs.top_sort)
        preds = KoreUtils.and_to_list(cnf)
        return preds # type: ignore

    def subsumes(self, a1: IAbstractConstraint, a2: IAbstractConstraint) -> bool:
        assert type(a1) is SubstitutionsConstraint
        assert type(a2) is SubstitutionsConstraint
        return self.nested.subsumes(a1.nested, a2.nested)
    
    def equals(self, a1: IAbstractConstraint, a2: IAbstractConstraint) -> bool:
        assert type(a1) is SubstitutionsConstraint
        assert type(a2) is SubstitutionsConstraint
        return self.nested.equals(a1.nested, a2.nested)

    def is_top(self, a: IAbstractConstraint) -> bool:
        assert type(a) is SubstitutionsConstraint
        return self.nested.is_top(a.nested)

    def is_bottom(self, a: IAbstractConstraint) -> bool:
        assert type(a) is SubstitutionsConstraint
        return self.nested.is_bottom(a.nested)
    
    def to_str(self, a: IAbstractConstraint) -> str:
        assert type(a) is SubstitutionsConstraint
        return f'<sc: {self.nested.to_str(a.nested)}>'
    


class SubstitutionsConstraintDomainBuilder(IAbstractConstraintDomainBuilder):
    nested: IAbstractSubstitutionsDomain
    rs: ReachabilitySystem

    def __init__(self, nested: IAbstractSubstitutionsDomain, rs: ReachabilitySystem):
        self.nested = nested
        self.rs = rs
    
    def build_abstract_constraint_domain(self, over_variables: T.Set[Kore.EVar]) -> SubstitutionsConstraintDomain:
        return SubstitutionsConstraintDomain(
            rs=self.rs,
            nested=self.nested,
            evars=over_variables,
        )