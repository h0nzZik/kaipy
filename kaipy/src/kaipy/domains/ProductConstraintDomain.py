import dataclasses
import itertools
import typing as T

import pyk.kore.syntax as Kore

from kaipy.AbstractionContext import AbstractionContext
from kaipy.interfaces.IAbstractConstraintDomain import IAbstractConstraint, IAbstractConstraintDomain

@dataclasses.dataclass
class ProductConstraint(IAbstractConstraint):
    underlying: T.List[IAbstractConstraint]

class ProductConstraintDomain(IAbstractConstraintDomain):
    underlying_domains: T.List[IAbstractConstraintDomain]

    def __init__(self, underlying_domains: T.List[IAbstractConstraintDomain]):
        self.underlying_domains = underlying_domains

    def abstract(self, ctx: AbstractionContext, over_variables: T.Set[Kore.EVar], constraints: T.List[Kore.Pattern]) -> ProductConstraint:
        ovs = over_variables.copy()
        underlying: T.List[IAbstractConstraint] = list()
        for ud in self.underlying_domains:
            a = ud.abstract(ctx, over_variables=ovs, constraints=constraints)
            ovs.update(ud.free_variables_of(a))
            underlying.append(a)
        
        return ProductConstraint(underlying=underlying)
    
    def free_variables_of(self, a: IAbstractConstraint) -> T.Set[Kore.EVar]:
        assert type(a) is ProductConstraint
        return set(*itertools.chain(ud.free_variables_of(ua) for ud,ua in zip(self.underlying_domains, a.underlying)))
    
    def refine(self, ctx: AbstractionContext, a: IAbstractConstraint, constraints: T.List[Kore.Pattern]) -> IAbstractConstraint:
        assert type(a) is ProductConstraint
        return ProductConstraint(underlying=[
            ud.refine(ctx, ua, constraints)
            for ud,ua in zip(self.underlying_domains, a.underlying)
        ])

    def disjunction(self, ctx: AbstractionContext, a1: IAbstractConstraint, a2: IAbstractConstraint) -> ProductConstraint:
        assert type(a1) is ProductConstraint
        assert type(a2) is ProductConstraint
        return ProductConstraint(underlying=[
            ud.disjunction(ctx, ua1, ua2)
            for ud,ua1,ua2 in zip(self.underlying_domains, a1.underlying, a2.underlying)
        ])

    def is_top(self, a: IAbstractConstraint) -> bool:
        assert type(a) is ProductConstraint
        return all([ud.is_top(ua) for ud,ua in zip(self.underlying_domains, a.underlying)])

    def is_bottom(self, a: IAbstractConstraint) -> bool:
        assert type(a) is ProductConstraint
        return any([ud.is_bottom(ua) for ud,ua in zip(self.underlying_domains, a.underlying)])

    def concretize(self, a: IAbstractConstraint) -> T.List[Kore.Pattern]:
        assert type(a) is ProductConstraint
        return list(*itertools.chain(ud.concretize(ua) for ud,ua in zip(self.underlying_domains, a.underlying)))

    def subsumes(self, a1: IAbstractConstraint, a2: IAbstractConstraint) -> bool:
        assert type(a1) is ProductConstraint
        assert type(a2) is ProductConstraint
        return all([ud.subsumes(ua1, ua2) for ud,ua1,ua2 in zip(self.underlying_domains, a1.underlying, a2.underlying)])
    
    def equals(self, a1: IAbstractConstraint, a2: IAbstractConstraint) -> bool:
        assert type(a1) is ProductConstraint
        assert type(a2) is ProductConstraint
        return all([ud.equals(ua1, ua2) for ud,ua1,ua2 in zip(self.underlying_domains, a1.underlying, a2.underlying)])

    def to_str(self, a: IAbstractConstraint, indent: int) -> str:
        assert type(a) is ProductConstraint
        s = (indent*' ') + '<prod\n'
        for ud,ua in zip(self.underlying_domains, a.underlying):
            s = s + ud.to_str(ua, indent=indent+1) + ",\n"
        s = s + (indent*' ') + ">"
        return s
