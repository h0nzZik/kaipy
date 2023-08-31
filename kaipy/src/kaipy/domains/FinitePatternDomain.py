import dataclasses
import logging
import functools
import typing as T

import pyk.kore.syntax as Kore

import kaipy.kore_utils as KoreUtils
from kaipy.AbstractionContext import AbstractionContext
from kaipy.VariableManager import VariableManager
from kaipy.ParallelMatcher import parallel_match, MatchResult
from kaipy.ReachabilitySystem import ReachabilitySystem, KoreClientServer, get_global_kcs
from kaipy.interfaces.IAbstractPatternDomain import IAbstractPattern, IAbstractPatternDomain
from kaipy.IBroadcastChannel import IBroadcastChannel
from kaipy.VariableManager import VariableManager

_LOGGER: T.Final = logging.getLogger(__name__)

@dataclasses.dataclass
class FinitePattern(IAbstractPattern):
    # -1 means Top
    idx: int
    sort: Kore.Sort
    renaming: T.Mapping[str,str] | None

# class Subsumer:
#     c: Kore.Pattern
#     rs: ReachabilitySystem

#     def __init__(self, c: Kore.Pattern, rs: ReachabilitySystem):
#         self.c = c
#         self.rs = rs
    
#     @functools.cached_property
#     def c_sort(self) -> Kore.Sort:
#         return self.rs.kdw.sortof(self.c)

#     def __call__(self, p: Kore.Pattern) -> T.Tuple[bool, T.Dict[str,str] | None]:
#         kcs: KoreClientServer|None = get_global_kcs()
#         # This means we are not running in a worker process
#         # but in the main one.
#         if kcs is None:
#             kcs = self.rs.kcs

#         p_sort = self.rs.kdw.sortof(p)
#         if self.c_sort != p_sort:
#             return False,{}
        
#         ant: Kore.Pattern = self.c
#         con: Kore.Pattern = p

#         renaming = KoreUtils.compute_renaming0(
#             vars_to_avoid=list(KoreUtils.free_evars_of_pattern(ant)),
#             vars_to_rename=list(KoreUtils.free_evars_of_pattern(con))
#         )
#         con_renamed: Kore.Pattern = KoreUtils.rename_vars(
#             renaming,
#             con,
#         )
#         con_eqa = KoreUtils.existentially_quantify_free_variables(self.c_sort, con_renamed)
#         ir = kcs.client.implies(ant, con_eqa)
#         return ir.satisfiable, (renaming if ir.satisfiable else None)



class FinitePatternDomain(IAbstractPatternDomain):
    pl : T.List[Kore.Pattern] # list of terms with free variables
    rs : ReachabilitySystem
    subsumption_matrix: T.Set[T.Tuple[int,int]]

    # pl - list of patterns potentially containing free variables
    def __init__(self, pl: T.List[Kore.Pattern], rs: ReachabilitySystem):
        self.pl = pl
        self.rs = rs

        self.subsumption_matrix = set()
        for i,p in enumerate(pl):
            for j,q in enumerate(pl):
                # make it irreflexive
                if i == j:
                    continue
                if self.rs.sortof(p) != self.rs.sortof(q):
                    continue
                if self.rs.subsumes(p, q)[0]:
                    # `q` is more general
                    self.subsumption_matrix.add((i,j))
        _LOGGER.warning(f'Computed subsumption matrix (size {len(self.subsumption_matrix)})')
        #_LOGGER.warning(f'{self.subsumption_matrix}')
    
    def abstract(self, ctx: AbstractionContext, c: Kore.Pattern) -> FinitePattern:
        csort = self.rs.sortof(c)
        mrs: T.List[MatchResult] = parallel_match(rs=self.rs, cfg=c, states=[(s if self.rs.sortof(s) == csort else Kore.Bottom(csort)) for s in self.pl])

        fpl: T.List[FinitePattern] = list()
        for i,mr in enumerate(mrs):
            if len(mr.constraints) == 1 and KoreUtils.is_bottom(mr.constraints[0]):
                continue
            fp = FinitePattern(i, csort, mr.renaming or dict())
            fpl.append(fp)
        if len(fpl) == 0:
            #_LOGGER.warning(f'no nice pattern found for {self.rs.kprint.kore_to_pretty(c)}')
            return FinitePattern(-1, csort, None)
        if len(fpl) == 1:
            #_LOGGER.warning(f'unique nice pattern found')
            return fpl[0]
        _LOGGER.warning(f'NO unique nice pattern found - multiple found. Candidates:')
        #for fp in fpl:
        #    _LOGGER.warning(f'  have {fp} as:')
        #    _LOGGER.warning(f'  {self.rs.kprint.kore_to_pretty(self.concretize(fp))}')
        
        fp1 = fpl[0]
        for fp2 in fpl[1:]:
            if not (fp1.idx,fp2.idx) in self.subsumption_matrix:
                #_LOGGER.warning(f'Replacing with other (NOT more general)')
                fp1 = fp2
        _LOGGER.warning(f"Choosing {fp1.idx}")

        renaming_2: T.Mapping[str, str] = {
            v: ctx.variable_manager.get_fresh_evar_name() for k,v in (fp1.renaming or dict()).items()
        }

        constraints_renamed: T.List[Kore.MLPred] = [
            KoreUtils.rename_vars(renaming_2, c) for c in mrs[fp1.idx].constraints # type: ignore
        ]

        # TODO emit the constraints through the channel
        for c in constraints_renamed:
            _LOGGER.warning(f'TODO emit: {self.rs.kprint.kore_to_pretty(c)}')

        renaming_composed: T.Mapping[str, str] = {
            k:renaming_2[v] for k,v in (fp1.renaming or dict()).items()
        }

        return FinitePattern(
            idx=fp1.idx,
            sort=fp1.sort,
            renaming=dict(renaming_composed)
        )
    
    def refine(self, ctx: AbstractionContext, a: IAbstractPattern, c: Kore.Pattern) -> FinitePattern:
        assert type(a) is FinitePattern
        return a

    def is_top(self, a: IAbstractPattern) -> bool:
        assert type(a) is FinitePattern
        return a.idx == -1

    def is_bottom(self, a: IAbstractPattern) -> bool:
        assert type(a) is FinitePattern
        return False

    def concretize(self, a: IAbstractPattern) -> Kore.Pattern:
        assert type(a) is FinitePattern
        if self.is_top(a):
            return Kore.Top(a.sort)
        return KoreUtils.rename_vars(dict(a.renaming) if a.renaming else dict(), self.pl[a.idx])

    def equals(self, a1: IAbstractPattern, a2: IAbstractPattern) -> bool:
        assert type(a1) is FinitePattern
        assert type(a2) is FinitePattern

        return a1.idx == a2.idx

    def disjunction(self, ctx: AbstractionContext, a1: IAbstractPattern, a2: IAbstractPattern) -> FinitePattern:
        assert type(a1) is FinitePattern
        assert type(a2) is FinitePattern
        if (a1.idx == a2.idx) and (a1.sort == a2.sort) and (a1.renaming == a2.renaming):
            return a1
        return FinitePattern(idx=-1, sort=a1.sort, renaming=dict())

    def subsumes(self, a1: IAbstractPattern, a2: IAbstractPattern) -> bool:
        assert type(a1) is FinitePattern
        assert type(a2) is FinitePattern

        if a1.sort != a2.sort:
            return False

        if a2.idx == -1:
            return True

        # In this case, self.concretize(a1) and self.concretize(a2)
        # differe only in naming of variables, and therefore the subsumption
        # holds.
        if a1.idx == a2.idx:
            return True

        if self.is_top(a2):
            return True
        
        if self.is_top(a1):
            return False
        
        return False
        #return self.rs.subsumes(self.concretize(a1), self.concretize(a2))[0]

    def to_str(self, a: IAbstractPattern) -> str:
        c = self.concretize(a)
        #assert not KoreUtils.is_top(c) ?????
        return self.rs.kprint.kore_to_pretty(c)
