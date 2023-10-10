import dataclasses
from enum import Enum
import time
import typing as T
import logging
import itertools

import pyk.kore.syntax as Kore
import pyk.kore.prelude as KorePrelude

import kaipy.kore_utils as KoreUtils
from kaipy.PerfCounter import PerfCounter
from kaipy.interfaces.IAbstractConstraintDomain import IAbstractConstraint, IAbstractConstraintDomain
from kaipy.AbstractionContext import AbstractionContext
from kaipy.ReachabilitySystem import ReachabilitySystem

_LOGGER: T.Final = logging.getLogger(__name__)

@dataclasses.dataclass
class KResultConstraint(IAbstractConstraint):
    kresult_vars: T.List[Kore.EVar]

SortIsKResult = Enum('SortIsKResult', ['Allways', 'Never', 'Sometimes'])


class KResultConstraintDomain(IAbstractConstraintDomain):
    rs: ReachabilitySystem
    abstract_perf_counter: PerfCounter
    sort_is_kresult: T.Mapping[str, SortIsKResult]
    aggressive: bool

    def __init__(
        self,
        rs: ReachabilitySystem,
        aggressive: bool = False,
    ):
        self.rs = rs
        self.aggressive = aggressive
        self.abstract_perf_counter = PerfCounter()
        
        sorts = self.rs.kdw.user_declared_sorts
        sort_never_kresults_queries: T.List[Kore.Pattern] = [
            self._mk_isKResult_pattern(Kore.EVar('X', Kore.SortApp(s, ())), sort=Kore.SortApp(s, ()))
            for s in sorts
        ]
        sort_always_kresults_queries: T.List[Kore.Pattern] = [
            Kore.Not(Kore.SortApp(s, ()), self._mk_isKResult_pattern(Kore.EVar('X', Kore.SortApp(s, ())), sort=Kore.SortApp(s, ())))
            for s in sorts
        ]
        sort_always_kresults_answers = self.rs.map_simplify(sort_always_kresults_queries)
        sort_never_kresults_answers = self.rs.map_simplify(sort_never_kresults_queries)
        
        sort_is_kresult: T.Dict[str, SortIsKResult] = {}
        for (i,s) in enumerate(sorts):
            if KoreUtils.is_bottom(sort_always_kresults_answers[i]):
                sort_is_kresult[s] = SortIsKResult.Allways
            elif KoreUtils.is_bottom(sort_never_kresults_answers[i]):
                sort_is_kresult[s] = SortIsKResult.Never
            else:
                sort_is_kresult[s] = SortIsKResult.Sometimes
        _LOGGER.warning(f"sort_is_kresult: {sort_is_kresult}")
        self.sort_is_kresult = sort_is_kresult
        
    
    def _mk_isKResult_pattern(self, e: Kore.EVar, sort: Kore.Sort) -> Kore.MLPred:
        pe = Kore.App('kseq', (), (
                KorePrelude.inj(e.sort, KorePrelude.SORT_K_ITEM, e) if sort != KorePrelude.SORT_K_ITEM else e,
                KorePrelude.DOTK,
        ))
        iskr = Kore.App('LblisKResult', (), (pe,))
        iskr_true = Kore.Equals(KorePrelude.BOOL, sort, iskr, KorePrelude.TRUE)
        return iskr_true
    
    def _swap_equals(self, phi: Kore.Pattern) -> Kore.Pattern:
        match phi:
            case Kore.Equals(s1, s2, l, r):
                return Kore.Equals(s1, s2, r, l)
            case _:
                assert False

    def free_variables_of(self, a: IAbstractConstraint) -> T.Set[Kore.EVar]:
        assert type(a) is KResultConstraint
        return set(a.kresult_vars)


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

    def _strip_equals_to(self, e: Kore.EVar, one_phi: Kore.Pattern) -> Kore.Pattern|None:
        match one_phi:
            case Kore.Equals(_, _, x1, x2):
                if x1 == e:
                    return x2
                if x2 == e:
                    return x1
        return None
    
    def _get_direct_equalities(self, e: Kore.EVar, phis: T.List[Kore.Pattern]) -> T.List[Kore.Pattern]:
        tmp = [self._strip_equals_to(e, one_phi) for one_phi in phis]
        return [x for x in tmp if x is not None]

    def _get_inj_equalities_sorts(self, e: Kore.EVar, phis: T.List[Kore.Pattern]) -> T.List[Kore.Sort]:
        sorts: T.List[Kore.Sort] = list()
        tmp = self._get_direct_equalities(e, phis)
        for phi2 in tmp:
            match phi2:
                case Kore.App('inj', (fr, to), _):
                    sorts.append(fr)
        return sorts

    def _really_really_test_necessary_kresult(self, e: Kore.EVar, phi: Kore.Pattern) -> bool:
        assert issubclass(type(phi), Kore.WithSort)
        iskr_true = self._mk_isKResult_pattern(e, sort=e.sort)
        #phil = KoreUtils.and_to_list(phi)
        #_LOGGER.warning(f"e: {e.text}, phil: {[p.text for p in phil]}")
        #if iskr_true in phil or self._swap_equals(iskr_true) in phil:
        #    _LOGGER.warning("FOUND")
        #    return True
        not_iskr_true = Kore.Not(e.sort, iskr_true)
        conj = Kore.And(sort=e.sort, left=not_iskr_true, right=KoreUtils.let_sort_rec(sort=e.sort, phi=phi)) 
        # TODO this can be parallelized
        conj_simp = self.rs.simplify(conj)
        return KoreUtils.is_bottom(conj_simp)

    def _really_test_necessary_kresult(self, e: Kore.EVar, phi: Kore.Pattern) -> bool:
        phil = KoreUtils.and_to_list(phi)
        sorts = self._get_inj_equalities_sorts(e, phil)
        _LOGGER.warning(f"Sorts: {[s.text for s in sorts]}")
        for s in sorts:
            if s.name not in self.sort_is_kresult:
                continue
            match self.sort_is_kresult[s.name]:
                case SortIsKResult.Allways:
                    return True
                case SortIsKResult.Never:
                    return False

        if self.aggressive:
            return self._really_really_test_necessary_kresult(e, phi)

        _LOGGER.warning("Non-aggressive fallback to False")        
        return False
    
    def _test_necessary_kresult(self, e: Kore.EVar, phi: Kore.Pattern) -> bool:
        s = e.sort.name
        if s not in self.sort_is_kresult:
            return self._really_test_necessary_kresult(e, phi)
        
        match self.sort_is_kresult[s]:
            case SortIsKResult.Allways:
                return True
            case SortIsKResult.Never:
                return False
            case _:
                return self._really_test_necessary_kresult(e, phi)

    def abstract(self, ctx: AbstractionContext, over_variables: T.Set[Kore.EVar], constraints: T.List[Kore.Pattern]) -> KResultConstraint:
        old = time.perf_counter()
        a = self._abstract(ctx, over_variables, constraints)
        new = time.perf_counter()
        self.abstract_perf_counter.add(new - old)
        return a

    def _abstract(self, ctx: AbstractionContext, over_variables: T.Set[Kore.EVar], constraints: T.List[Kore.Pattern]) -> KResultConstraint:
        a = KResultConstraint(kresult_vars=[])
        if len(constraints) <= 0:
            return a
        #return self.do_refine(ctx, a, constraints)
        p = KoreUtils.make_conjunction(self.rs.sortof(constraints[0]), constraints)
        monitored_evars: T.Dict[Kore.EVar, Kore.Pattern] = dict()
        for x in constraints:
            for e in KoreUtils.free_evars_of_pattern(x):
                if e in over_variables: # or e in ctx.variable_manager.generated or True:
                    monitored_evars[e] = p
        #_LOGGER.warning(f"Monitoring: {[e.text for e in monitored_evars.keys()]}")
        a2 = self._refine_monitored(ctx, a, monitored_evars=monitored_evars)
        #if len(a2.kresult_vars) > 0 or True:
        #    _LOGGER.warning(f"Abstracted {[x.text for x in constraints]} into {self.to_str(a2, indent=0)}")
        return a2


    def _refine_monitored(self, ctx: AbstractionContext, a: KResultConstraint, monitored_evars: T.Mapping[Kore.EVar, Kore.Pattern]) -> KResultConstraint:
        #_LOGGER.warning(f"refining with monitored {monitored_evars}")
        kresult_vars: T.List[Kore.EVar] = list() # (a.kresult_vars or list()).copy()
        for e,phi in monitored_evars.items():
            if not self._monitor_evar(e):
                continue
            # This way we can have some duplicated variables... but maybe better than losing information?
            #if self._equals_to_some(kresult_vars, e):
            #    continue
            #_LOGGER.warning(f'testing {e.text} with {self.rs.kprint.kore_to_pretty(phi)}')
            if self._test_necessary_kresult(e=e, phi=phi):
                kresult_vars.append(e)
                #_LOGGER.warning(f'appending {e} because of {phi.text}')

        if len(kresult_vars) <= 0:
            return a
        
        return KResultConstraint(kresult_vars=(kresult_vars+(a.kresult_vars or list())))
    
    def concretize(self, a: IAbstractConstraint) -> T.List[Kore.Pattern]:
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


    def statistics(self) -> T.Dict[str, T.Any]:
        return {
            'name' : 'KResultConstraintDomain',
            'abstract' : self.abstract_perf_counter.dict,
        }