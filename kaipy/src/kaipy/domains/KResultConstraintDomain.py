import dataclasses
import typing as T
import logging
import itertools

import pyk.kore.syntax as Kore
import pyk.kore.prelude as KorePrelude

import kaipy.kore_utils as KoreUtils
from kaipy.interfaces.IAbstractConstraintDomain import IAbstractConstraint, IAbstractConstraintDomain
from kaipy.interfaces.IAbstractConstraintDomainBuilder import IAbstractConstraintDomainBuilder
from kaipy.AbstractionContext import AbstractionContext
from kaipy.ReachabilitySystem import ReachabilitySystem

_LOGGER: T.Final = logging.getLogger(__name__)

@dataclasses.dataclass
class KResultConstraint(IAbstractConstraint):
    kresult_vars: T.List[Kore.EVar]

class KResultConstraintDomain(IAbstractConstraintDomain):
    rs: ReachabilitySystem
    over_variables: T.Set[Kore.EVar]

    def __init__(
        self,
        rs: ReachabilitySystem,
        over_variables: T.Set[Kore.EVar],
    ):
        self.rs = rs
        self.over_variables = over_variables
    
    def _mk_isKResult_pattern(self, e: Kore.EVar, sort: Kore.Sort) -> Kore.MLPred:
        pe = Kore.App('kseq', (), (
                KorePrelude.inj(e.sort, KorePrelude.SORT_K_ITEM, e),
                KorePrelude.DOTK,
        ))
        iskr = Kore.App('LblisKResult', (), (pe,))
        iskr_true = Kore.Equals(KorePrelude.BOOL, sort, iskr, KorePrelude.TRUE)
        return iskr_true

    def abstract(self, ctx: AbstractionContext, c: T.List[Kore.MLPred]) -> KResultConstraint:
        a = KResultConstraint(kresult_vars=[])
        if len(c) <= 0:
            return a
        p = KoreUtils.make_conjunction(self.rs.sortof(c[0]), c)
        monitored_evars: T.Dict[Kore.EVar, Kore.Pattern] = dict()
        for x in c:
            for e in KoreUtils.free_evars_of_pattern(x):
                # If we monitor only 'over_variables' - that is, variables that belong to the particular rule LHS,
                # we will lose information about all other variables. For example, consider the rule LHS
                # <k> X = I:Int ; ~> _DotVar2 ~> . </k>
                # (corresponding to the `IMP.assignment` rule).
                # What if there is an equality `_DotVar2 = #somefreezer(S:Stmt)` ?
                # We want to track the KResult information about S.
                # (We also want to track the equality itself, but that is the business of another component.)
                # The ideal solution would be to track only `over_variables` plus whatever variables has been created dynamically.
                if e in self.over_variables or True:
                    monitored_evars[e] = p
        #_LOGGER.warning(f"Monitoring: {[e.text for e in monitored_evars.keys()]}")
        a2 = self._refine_monitored(ctx, a, monitored_evars=monitored_evars)
        if len(a2.kresult_vars) > 0 or True:
            _LOGGER.warning(f"Abstracted {[x.text for x in c]} into {self.to_str(a2, indent=0)}")
        return a2

    def is_top(self, a: IAbstractConstraint) -> bool:
        assert type(a) is KResultConstraint
        return len(a.kresult_vars) == 0

    def is_bottom(self, a: IAbstractConstraint) -> bool:
        assert type(a) is KResultConstraint
        return False

    def _monitor_evar(self, e: Kore.EVar):
        if e.sort.name == 'SortK':
            return False
        if e.sort.name not in self.rs.kdw.declared_sorts:
            return False
        return True

    def _test_necessary_kresult(self, e: Kore.EVar, phi: Kore.Pattern) -> bool:
        assert issubclass(type(phi), Kore.WithSort)
        iskr_true = self._mk_isKResult_pattern(e, sort=e.sort)
        not_iskr_true = Kore.Not(e.sort, iskr_true)
        #conj0 = Kore.And(sort=e.sort, left=e, right=not_iskr_true)
        #conj = Kore.And(sort=e.sort, left=conj0, right=KoreUtils.let_sort_rec(sort=e.sort, phi=phi)) 
        conj = Kore.And(sort=e.sort, left=not_iskr_true, right=KoreUtils.let_sort_rec(sort=e.sort, phi=phi)) 
        conj_simp = self.rs.simplify(conj)
        return KoreUtils.is_bottom(conj_simp)

    def refine(self, ctx: AbstractionContext, a: IAbstractConstraint, c: T.List[Kore.MLPred]) -> KResultConstraint:
        assert type(a) is KResultConstraint

        monitored_evars: T.Dict[Kore.EVar, Kore.MLPred] = dict()
        equality_pairs: T.List[T.Tuple[Kore.EVar, Kore.EVar]] = list()
        for p in c:
            match p:
                case Kore.Equals(_, _, Kore.EVar(n1, s1), Kore.EVar(n2, s2)):
                    equality_pairs.append((Kore.EVar(n1, s1), Kore.EVar(n2, s2)))
                    #monitored_evars[Kore.EVar(n1, s1)] = p
                    #monitored_evars[Kore.EVar(n2, s2)] = p
                    continue
                case Kore.Equals(_, _, Kore.EVar(n, s), right):
                    monitored_evars[Kore.EVar(n, s)] = p
                case Kore.Equals(_, _, left, Kore.EVar(n, s)):
                    monitored_evars[Kore.EVar(n, s)] = p

        _LOGGER.warning(f"refine: equality_pars: {equality_pairs}, a: {self.to_str(a, indent=0)}")
        a2 = self._refine_monitored(ctx, a, monitored_evars)
        a3 = self._refine_by_equalities(a2, equality_pairs)
        #_LOGGER.warning(f"refined {self.to_str(a2)}")
        return a3

    def _refine_by_equalities(self, a: KResultConstraint, equality_pairs: T.List[T.Tuple[Kore.EVar, Kore.EVar]]) -> KResultConstraint:
        # We ignore transitivity of equality for now, because
        # the only known client (FinitePatternDomain) produces singleton lists only.
        kresult_vars = a.kresult_vars.copy()
        _LOGGER.warning(f"_rbe: kresult_vars = {kresult_vars}")
        for (e1,e2) in equality_pairs:
            if e1 in kresult_vars and e2 not in kresult_vars:
                _LOGGER.warning(f"Adding {e2}")
                kresult_vars.append(e2)
                continue
            if e2 in kresult_vars and e1 not in kresult_vars:
                _LOGGER.warning(f"Adding {e1}")
                kresult_vars.append(e1)
                continue

        return KResultConstraint(kresult_vars=kresult_vars)

    def _refine_monitored(self, ctx: AbstractionContext, a: KResultConstraint, monitored_evars: T.Mapping[Kore.EVar, Kore.Pattern]) -> KResultConstraint:
        #_LOGGER.warning(f"refining with monitored {monitored_evars}")
        kresult_vars: T.List[Kore.EVar] = list() # (a.kresult_vars or list()).copy()
        for e,phi in monitored_evars.items():
            if not self._monitor_evar(e):
                continue
            # This way we can have some duplicated variables... but maybe better than losing information?
            #if self._equals_to_some(kresult_vars, e):
            #    continue
            #_LOGGER.warning(f'testing {e.text} with {phi.text}')
            if self._test_necessary_kresult(e=e, phi=phi):
                kresult_vars.append(e)
                #_LOGGER.warning(f'appending {e} because of {phi.text}')

        if len(kresult_vars) <= 0:
            return a
        
        return KResultConstraint(kresult_vars=(kresult_vars+(a.kresult_vars or list())))
    
    def concretize(self, a: IAbstractConstraint) -> T.List[Kore.MLPred]:
        assert type(a) is KResultConstraint

        #_LOGGER.warning(f"Concretizing {self.to_str(a)}")

        return [
            self._mk_isKResult_pattern(ev, self.rs.top_sort)
            for ev in a.kresult_vars
        ]

    def disjunction(self, ctx: AbstractionContext, a1: IAbstractConstraint, a2: IAbstractConstraint) -> KResultConstraint:
        assert type(a1) is KResultConstraint
        assert type(a2) is KResultConstraint
        #_LOGGER.warning(f"Disjuncting {self.to_str(a1)} and {self.to_str(a2)}")
        #assert (len(a1.kresult_vars) == 0) == (len(a2.kresult_vars) == 0)
        a = KResultConstraint(kresult_vars=list(set(a1.kresult_vars).intersection(set(a2.kresult_vars))))
        return a
        #return KResultConstraint(kresult_vars=list(set(a1.kresult_vars).union(set(a2.kresult_vars))))

    def equals(self, a1: IAbstractConstraint, a2: IAbstractConstraint) -> bool:
        assert type(a1) is KResultConstraint
        assert type(a2) is KResultConstraint
        return set(a1.kresult_vars) == set(a2.kresult_vars)

    def subsumes(self, a1: IAbstractConstraint, a2: IAbstractConstraint) -> bool:
        assert type(a1) is KResultConstraint
        assert type(a2) is KResultConstraint
        return set(a1.kresult_vars) <= set(a2.kresult_vars)
    
    def to_str(self, a: IAbstractConstraint, indent: int) -> str:
        assert type(a) is KResultConstraint
        return (indent*' ') + f"<kresults {str([x.text for x in a.kresult_vars])}>"


class KResultConstraintDomainBuilder(IAbstractConstraintDomainBuilder):
    rs: ReachabilitySystem

    def __init__(self, rs: ReachabilitySystem):
        self.rs = rs
    
    def build_abstract_constraint_domain(self, over_variables: T.Set[Kore.EVar]) -> KResultConstraintDomain:
        # ignore over_variables
        return KResultConstraintDomain(self.rs, over_variables=over_variables)