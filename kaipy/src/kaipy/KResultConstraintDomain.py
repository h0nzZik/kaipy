import dataclasses
import typing as T

import pyk.kore.syntax as Kore

import kaipy.IAbstractConstraintDomain

@dataclasses.dataclass
class KResultConstraint(IAbstractConstraint):
    # None means 'overflow'
    not_necessary_kresults: T.List[Kore.EVar] | None

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
    
    def mk_isKResult_pattern(self, e: Kore.EVar) -> Kore.Pattern:
        pe = Kore.App('kseq', (), (
                KorePrelude.inj(e.sort, KorePrelude.SORT_K_ITEM, e),
                KorePrelude.DOTK,
        ))
        iskr = Kore.App('LblisKResult', (), (pe,))
        iskr_true = Kore.Equals(KorePrelude.BOOL, self.rs.top_sort, iskr, KorePrelude.TRUE)
        return iskr_true

    def abstract(self, c: T.List[Kore.MLPred]) -> KResultConstraint:
        a_s : IAbstractSubstitution = self.underlying_subst_domain.abstract(subst, preds)
        c_s,_ = self.underlying_subst_domain.concretize(a_s)
        # One problem is that the rhss o c_s and subst may have different free variables.
        # 
        # We look for element variables of the concretized substitution,
        # not of the original one - there might be more variables,
        # as some terms are abstracted away.
        # However, I am not sure how to deal with the following:
        # say, voidVal() gets abstracted as a variable,
        # but how do we recover that it is a KResult?
        # I guess that voidVal() will be only abstracted when
        # applying a cooling rule to it, which check whether it is a KResultx...
        evars1 = list(itertools.chain(*[
                    KoreUtils.free_evars_of_pattern(v)
                    for k,v in c_s.mapping.items()
                ]))
        evars2 = [k for k in subst.mapping.keys() if k not in c_s.mapping.keys()]
        assert len(evars2) == 0
        evars = evars1 + evars2
        monitored_evars = [e for e in evars if e.sort.name in self.rs.kdw.user_declared_sorts]
        _LOGGER.warning(f"abstract(): monitored_evars={monitored_evars}")

        not_necessary_kresults: T.List[Kore.EVar] = []
        for e in monitored_evars:
            iskr_true = self.mk_isKResult_pattern(e)
            not_iskr_true = Kore.Not(self.rs.top_sort, iskr_true)
            new_preds: T.List[Kore.Pattern] = preds + [not_iskr_true]
            top_pat: Kore.Pattern = Kore.Top(self.rs.top_sort)
            conj = functools.reduce(
                lambda p, eq: Kore.And(self.rs.top_sort, eq, p),
                new_preds,
                top_pat
            )
            conj_simp = self.rs.simplify(conj)
            _LOGGER.warning(f"{e}: {self.rs.kprint.kore_to_pretty(conj_simp)}")
            if not KoreUtils.is_bottom(conj_simp):
                if len(not_necessary_kresults) >= self.limit:
                    _LOGGER.warning(f"Limit ({self.limit}) reached.")
                    return KResultSubstDomainWrapperElement(
                        underlying=a_s,
                        not_necessary_kresults=None,
                        monitored_evars=monitored_evars,
                    )
                not_necessary_kresults.append(e)

        return KResultSubstDomainWrapperElement(
            underlying=a_s,
            not_necessary_kresults=not_necessary_kresults,
            monitored_evars=monitored_evars,
        )
    
    def concretize(self, a: IAbstractSubstitution) -> T.Tuple[Substitution, T.List[Kore.Pattern]]:
        assert type(a) is KResultSubstDomainWrapperElement

        (concrete_subst,constraints) = self.underlying_subst_domain.concretize(a.underlying)
        if a.not_necessary_kresults is None:
            _LOGGER.warning(f'Concretize: no additional constraints')
            return (concrete_subst,constraints)

        #evars = list(itertools.chain(*[
        #            KoreUtils.free_evars_of_pattern(v)
        #            for k,v in concrete_subst.mapping.items()
        #        ]))
        #_LOGGER.warning(f'Concretize: evars={evars}')
        #monitored_evars = [e for e in evars if e.sort.name in self.rs.kdw.user_declared_sorts]
        monitored_evars = a.monitored_evars
        _LOGGER.warning(f'Concretize: monitored_evars={monitored_evars}')
        new_constraints: T.List[Kore.Pattern] = []
        for ev in monitored_evars:
            if ev in a.not_necessary_kresults:
                continue
            new_constraints.append(self.mk_isKResult_pattern(ev))
        
        _LOGGER.warning(f'Concretize: some ({len(new_constraints)}) additional constraints')
        return (concrete_subst, constraints + new_constraints)


    def equals(self, a1: IAbstractSubstitution, a2: IAbstractSubstitution) -> bool:
        # Not implemented yet, not needed yet
        return False

    def subsumes(self, a1: IAbstractSubstitution, a2: IAbstractSubstitution) -> bool:
        assert type(a1) is KResultSubstDomainWrapperElement
        assert type(a2) is KResultSubstDomainWrapperElement

        # TODO implement properly!
        return self.underlying_subst_domain.subsumes(a1.underlying, a2.underlying)
    
    def print(self, a: IAbstractSubstitution) -> str:
        assert type(a) is KResultSubstDomainWrapperElement
        v = len(a.not_necessary_kresults) if a.not_necessary_kresults is not None else -1
        return f'<kr {v}, {self.underlying_subst_domain.print(a.underlying)}  >'
