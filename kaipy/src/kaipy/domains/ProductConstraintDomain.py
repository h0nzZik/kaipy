import dataclasses
import typing as T

import pyk.kore.syntax as Kore

from kaipy.AbstractionContext import AbstractionContext
from kaipy.interfaces.IAbstractConstraintDomain import IAbstractConstraint, IAbstractConstraintDomain

@dataclasses.dataclass
class ProductConstraint(IAbstractConstraint):
    left : IAbstractConstraint
    right: IAbstractConstraint

class ProductConstraintDomain(IAbstractConstraintDomain):
    left_domain: IAbstractConstraintDomain
    right_domain: IAbstractConstraintDomain

    def __init__(self, left_domain: IAbstractConstraintDomain, right_domain: IAbstractConstraintDomain):
        self.left_domain = left_domain
        self.right_domain = right_domain

    def abstract(self, ctx: AbstractionContext, c: T.List[Kore.MLPred]) -> ProductConstraint:
        left = self.left_domain.abstract(ctx, c)
        right = self.right_domain.abstract(ctx, c)
        return ProductConstraint(left=left, right=right)
    
    def refine(self, ctx: AbstractionContext, a: IAbstractConstraint, c: T.List[Kore.MLPred]) -> IAbstractConstraint:
        assert type(a) is ProductConstraint
        left = self.left_domain.refine(ctx, a.left, c)
        right = self.right_domain.refine(ctx, a.right, c)
        return ProductConstraint(left=left, right=right)

    def concretize(self, a: IAbstractConstraint) -> T.List[Kore.MLPred]:
        assert type(a) is ProductConstraint
        c_left = self.left_domain.concretize(a.left)
        c_right = self.right_domain.concretize(a.right)
        return c_left + c_right

    def subsumes(self, a1: IAbstractConstraint, a2: IAbstractConstraint) -> bool:
        assert type(a1) is ProductConstraint
        assert type(a2) is ProductConstraint
        return self.left_domain.subsumes(a1.left, a2.left) and self.right_domain.subsumes(a1.right, a2.right)
    
    def to_str(self, a: IAbstractConstraint) -> str:
        assert type(a) is ProductConstraint
        return f'<prod {self.left_domain.to_str(a.left)}, {self.right_domain.to_str(a.right)}>'