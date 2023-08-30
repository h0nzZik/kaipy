import dataclasses
import typing as T
import logging

import pyk.kore.syntax as Kore
import pyk.kore.prelude as KorePrelude

from kaipy.interfaces.IAbstractConstraintDomain import IAbstractConstraint, IAbstractConstraintDomain
from kaipy.AbstractionContext import AbstractionContext
from kaipy.ReachabilitySystem import ReachabilitySystem

_LOGGER: T.Final = logging.getLogger(__name__)

@dataclasses.dataclass
class KResultConstraint(IAbstractConstraint):
    monitored_evars: T.List[Kore.EVar]
    not_necessary_kresults: T.List[Kore.EVar]

class KResultConstraintDomain(IAbstractConstraintDomain):
    rs: ReachabilitySystem
    limit: int

    def __init__(
        self,
        rs: ReachabilitySystem,
        limit: int,
    ):
        self.rs = rs
        self.limit = limit
    
    def _mk_isKResult_pattern(self, e: Kore.EVar) -> Kore.MLPred:
        pe = Kore.App('kseq', (), (
                KorePrelude.inj(e.sort, KorePrelude.SORT_K_ITEM, e),
                KorePrelude.DOTK,
        ))
        iskr = Kore.App('LblisKResult', (), (pe,))
        iskr_true = Kore.Equals(KorePrelude.BOOL, self.rs.top_sort, iskr, KorePrelude.TRUE)
        return iskr_true

    def abstract(self, ctx: AbstractionContext, c: T.List[Kore.MLPred]) -> KResultConstraint:
        a = KResultConstraint(monitored_evars=[], not_necessary_kresults=[])
        return self.refine(ctx, a, c)
    
    def _kresults_of(self, a: KResultConstraint):
        return [e for e in a.monitored_evars if e not in a.not_necessary_kresults]

    def is_top(self, a: IAbstractConstraint) -> bool:
        assert type(a) is KResultConstraint
        return len(self._kresults_of(a)) == 0

    def _test_necessary_kresult(self, e: Kore.EVar, phi: Kore.MLPred) -> bool:
        iskr_true = self._mk_isKResult_pattern(e)
        not_iskr_true = Kore.Not(e.sort, iskr_true)
        conj0 = Kore.And(sort=e.sort, left=e, right=not_iskr_true)
        conj = Kore.And(sort=e.sort, left=conj0, right=phi)
        conj_simp = self.rs.simplify(conj)
        return KoreUtils.is_bottom(conj_simp)

    def refine(self, ctx: AbstractionContext, a: IAbstractConstraint, c: T.List[Kore.MLPred]) -> KResultConstraint:
        assert type(a) is KResultConstraint
        monitored_evars: T.List[Kore.EVar] = a.monitored_evars.copy()
        not_necessary_kresults: T.List[Kore.EVar] = a.not_necessary_kresults.copy()
        for p in c:
            match p:
                case Kore.Equals(_, _, Kore.EVar(_, _), Kore.EVar(_, _)):
                case Kore.Equals(_, _, Kore.EVar(n, s), right):
                    monitored_evars.append(Kore.EVar(n, s))
                    if not self._test_necessary_kresult(e=Kore.EVar(n, s), phi=p):
                        not_necessary_kresults.append(Kore.EVar(n, s))
                case Kore.Equals(_, _, left, Kore.EVar(n, s)):
                    monitored_evars.append(Kore.EVar(n, s))
                    if not self._test_necessary_kresult(e=Kore.EVar(n, s), phi=p):
                        not_necessary_kresults.append(Kore.EVar(n, s))
        
        if len(not_necessary_kresults) > self.limit:
            _LOGGER.warning(f"Limit ({self.limit}) reached.")
            not_necessary_kresults = not_necessary_kresults[0:self.limit]

        return KResultConstraint(
            monitored_evars=monitored_evars,
            not_necessary_kresults=not_necessary_kresults,
        )
    
    def concretize(self, a: IAbstractConstraint) -> T.List[Kore.MLPred]:
        assert type(a) is KResultConstraint
        return [
            self._mk_isKResult_pattern(e)
            for ev in self._kresults_of(a)
        ]

    def disjunction(self, ctx: AbstractionContext, a1: IAbstractConstraint, a2: IAbstractConstraint) -> KResultConstraint:
        assert type(a1) is KResultConstraint
        assert type(a2) is KResultConstraint

        not_necessary_kresults = list(set(a1.not_necessary_kresults).union(set(a2.not_necessary_kresults)))
        if len(not_necessary_kresults) > self.limit:
            not_necessary_kresults = not_necessary_kresults[0:self.limit]
        
        return KResultConstraint(
            monitored_evars=list(set(a1.monitored_evars).union(set(a2.monitored_evars))), 
            not_necessary_kresults=not_necessary_kresults,
        )


    def equals(self, a1: IAbstractSubstitution, a2: IAbstractSubstitution) -> bool:
        assert type(a1) is KResultConstraint
        assert type(a2) is KResultConstraint
        return set(self._kresults_of(a1)) == set(self._kresults_of(a2))

    def subsumes(self, a1: IAbstractSubstitution, a2: IAbstractSubstitution) -> bool:
        assert type(a1) is KResultConstraint
        assert type(a2) is KResultConstraint
        return set(self._kresults_of(a1)) >= set(self._kresults_of(a2))
    
    def to_str(self, a: IAbstractConstraint) -> str:
        assert type(a) is KResultConstraint
        return str(self._kresults_of(a))

