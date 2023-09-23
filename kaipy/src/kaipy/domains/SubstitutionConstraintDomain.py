import dataclasses
import time
import typing as T
import logging
from immutabledict import immutabledict

import pyk.kore.syntax as Kore

import kaipy.kore_utils as KoreUtils
import kaipy.rs_utils as RSUtils
from kaipy.PerfCounter import PerfCounter
from kaipy.ReachabilitySystem import ReachabilitySystem
from kaipy.AbstractionContext import AbstractionContext
from kaipy.interfaces.IAbstractConstraintDomain import IAbstractConstraint, IAbstractConstraintDomain
from kaipy.interfaces.IAbstractSubstitutionDomain import IAbstractSubstitution, IAbstractSubstitutionDomain
from kaipy.Substitution import Substitution
from kaipy.cnf import to_cnf


_LOGGER: T.Final = logging.getLogger(__name__)

@dataclasses.dataclass
class SubstitutionConstraint(IAbstractConstraint):
    nested: IAbstractSubstitution|None


class SubstitutionConstraintDomain(IAbstractConstraintDomain):
    nested: IAbstractSubstitutionDomain
    rs: ReachabilitySystem
    catch_all: bool
    abstract_perf_counter: PerfCounter

    def __init__(
        self,
        rs: ReachabilitySystem,
        nested: IAbstractSubstitutionDomain,
        catch_all: bool = False,
    ):
        self.nested = nested
        self.rs = rs
        self.catch_all = catch_all
        self.abstract_perf_counter = PerfCounter()

    def abstract(self, ctx: AbstractionContext, over_variables: T.Set[Kore.EVar], constraints: T.List[Kore.Pattern]) -> IAbstractConstraint:
        old = time.perf_counter()
        a = self._abstract(ctx, over_variables, constraints)
        new = time.perf_counter()
        self.abstract_perf_counter.add(new - old)
        return a

    def _abstract(self, ctx: AbstractionContext, over_variables: T.Set[Kore.EVar], constraints: T.List[Kore.Pattern]) -> IAbstractConstraint:
        if KoreUtils.any_is_bottom(constraints):
            return SubstitutionConstraint(None)
        
        #_LOGGER.warning(f"over_variables: {over_variables}")
        #_LOGGER.warning(f"len(constraints): {len(constraints)}")
        
        eqls: T.Dict[Kore.EVar, Kore.Pattern] = dict()
        for p in constraints:
            match p:
                case Kore.Equals(_, _, Kore.EVar(_, _), Kore.EVar(_, _)):
                    continue
                case Kore.Equals(_, _, Kore.EVar(n, s), right):
                    if Kore.EVar(n,s) in over_variables or self.catch_all:
                        eqls[Kore.EVar(n,s)] = right
                    else:
                        _LOGGER.warning(f"Unknown variable {n}:{s}")
                case Kore.Equals(_, _, left, Kore.EVar(n, s)):
                    if Kore.EVar(n,s) in over_variables or self.catch_all:
                        eqls[Kore.EVar(n,s)] = left
                    else:
                        _LOGGER.warning(f"Unknown variable {n}:{s}")

        subst = Substitution(immutabledict(eqls))
        a = SubstitutionConstraint(self.nested.abstract(ctx, subst))
        return a


    def free_variables_of(self, a: IAbstractConstraint) -> T.Set[Kore.EVar]:
        assert type(a) is SubstitutionConstraint
        if a.nested is None:
            return set()
        return self.nested.free_variables_of(a.nested)
    
    def refine(self, ctx: AbstractionContext, a: IAbstractConstraint, constraints: T.List[Kore.Pattern]) -> SubstitutionConstraint:
        assert type(a) is SubstitutionConstraint
        if a.nested is None:
            return a
        
        new_nested = self.nested.refine(ctx, a.nested, constraints)
        new_a = SubstitutionConstraint(new_nested)
        return new_a

    def disjunction(self, ctx: AbstractionContext, a1: IAbstractConstraint, a2: IAbstractConstraint) -> SubstitutionConstraint:
        assert type(a1) is SubstitutionConstraint
        assert type(a2) is SubstitutionConstraint
        if a1.nested is None:
            return a2
        if a2.nested is None:
            return a1
        return SubstitutionConstraint(self.nested.disjunction(ctx, a1.nested, a2.nested))

    def concretize(self, a: IAbstractConstraint) -> T.List[Kore.Pattern]:
        assert type(a) is SubstitutionConstraint
        if a.nested is None:
            return [Kore.Bottom(self.rs.top_sort)]
        concrete_subst = self.nested.concretize(a.nested)
        atoms: T.List[Kore.Pattern] = [Kore.Equals(k.sort, self.rs.top_sort, k, v) for k,v in concrete_subst.mapping.items()]
        return atoms

    def subsumes(self, a1: IAbstractConstraint, a2: IAbstractConstraint) -> bool:
        assert type(a1) is SubstitutionConstraint
        assert type(a2) is SubstitutionConstraint
        if a1.nested is None:
            return True
        if a2.nested is None:
            return False
        return self.nested.subsumes(a1.nested, a2.nested)
    
    def equals(self, a1: IAbstractConstraint, a2: IAbstractConstraint) -> bool:
        assert type(a1) is SubstitutionConstraint
        assert type(a2) is SubstitutionConstraint
        if a1.nested is None:
            return a2.nested is None
        if a2.nested is None:
            return False
        return self.nested.equals(a1.nested, a2.nested)

    def is_top(self, a: IAbstractConstraint) -> bool:
        assert type(a) is SubstitutionConstraint
        if a.nested is None:
            return False
        return self.nested.is_top(a.nested)

    def is_bottom(self, a: IAbstractConstraint) -> bool:
        assert type(a) is SubstitutionConstraint
        if a.nested is None:
            return True
        return self.nested.is_bottom(a.nested)
    
    def to_str(self, a: IAbstractConstraint, indent: int) -> str:
        assert type(a) is SubstitutionConstraint
        if a.nested is None:
            return indent*' ' + '<Bot>'
        s = (indent*' ') + "<sc\n"
        s = s + self.nested.to_str(a.nested, indent=indent+1) + '\n'
        s = s + (indent*' ') + ">"
        return s
    
    def statistics(self) -> T.Dict[str, T.Any]:
        return {
            'abstract' : self.abstract_perf_counter.dict,
            'underlying' : [self.nested.statistics()]
        }