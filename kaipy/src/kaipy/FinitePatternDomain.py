import dataclasses
import logging
import functools
import typing as T

import pyk.kore.syntax as Kore

import kaipy.kore_utils as KoreUtils
from kaipy.ReachabilitySystem import ReachabilitySystem, KoreClientServer, get_global_kcs
from kaipy.IAbstractPatternDomain import IAbstractPattern, IAbstractPatternDomain

_LOGGER: T.Final = logging.getLogger(__name__)

@dataclasses.dataclass
class FinitePattern(IAbstractPattern):
    # -1 means Top
    idx: int
    sort: Kore.Sort
    renaming: T.Dict[str,str] | None

class Subsumer:
    c: Kore.Pattern
    rs: ReachabilitySystem

    def __init__(self, c: Kore.Pattern, rs: ReachabilitySystem):
        self.c = c
        self.rs = rs
    
    @functools.cached_property
    def c_sort(self) -> Kore.Sort:
        return self.rs.kdw.sortof(self.c)

    def __call__(self, p: Kore.Pattern) -> T.Tuple[bool, T.Dict[str,str] | None]:
        kcs: KoreClientServer|None = get_global_kcs()
        # This means we are not running in a worker process
        # but in the main one.
        if kcs is None:
            kcs = self.rs.kcs

        p_sort = self.rs.kdw.sortof(p)
        if self.c_sort != p_sort:
            return False,{}
        
        ant: Kore.Pattern = self.c
        con: Kore.Pattern = p

        renaming = KoreUtils.compute_renaming0(
            vars_to_avoid=list(KoreUtils.free_evars_of_pattern(ant)),
            vars_to_rename=list(KoreUtils.free_evars_of_pattern(con))
        )
        con_renamed: Kore.Pattern = KoreUtils.rename_vars(
            renaming,
            con,
        )
        con_eqa = KoreUtils.existentially_quantify_free_variables(self.c_sort, con_renamed)
        ir = kcs.client.implies(ant, con_eqa)
        return ir.satisfiable, (renaming if ir.satisfiable else None)



class FinitePatternDomain(IAbstractPatternDomain):
    pl : T.List[Kore.Pattern]
    rs : ReachabilitySystem
    closed_patterns: T.List[T.Tuple[Kore.Pattern, int]]
    open_patterns: T.List[T.Tuple[Kore.Pattern, int]]

    def __init__(self, pl: T.List[Kore.Pattern], rs: ReachabilitySystem):
        self.pl = pl
        self.rs = rs

        self.closed_patterns = []
        self.open_patterns = []
        for i,p in enumerate(self.pl):
            _LOGGER.warning(f"FPD {i}: {self.rs.kprint.kore_to_pretty(p)}")
            if len(KoreUtils.free_evars_of_pattern(p)) == 0:
                self.closed_patterns.append((p, i))
            else:
                self.open_patterns.append((p, i))
        _LOGGER.warning(f'Finite domain: {len(self.closed_patterns)} closed, {len(self.open_patterns)} open')
        #print("Finite domain:")
        #for i, a_rest in enumerate(pl):
        #    print(f"{i}: {rs.kprint.kore_to_pretty(a_rest)}")
    
    def abstract(self, c: Kore.Pattern) -> FinitePattern:
        csort = self.rs.sortof(c)
        #_LOGGER.warning(f'abstracting {c.text}')
        # Optimization
        match c:
            case Kore.EVar(_, _):
                # TODO generalize this to `inj(EVar)``
                #_LOGGER.warning(f'Fast -1')
                return FinitePattern(-1, csort, None)
        
        # another optimization: for terms without free variables
        # it is enough to check for an equality with patterns without free variables.
        # This assumes functionality of both patterns.
        # For terms with free variables it is necessary to check for subsumtion/implication
        # but it is enough to consider patterns *with* free variables.
        if len(KoreUtils.free_evars_of_pattern(c)) == 0:
            for p,i in self.closed_patterns:
                if p == c:
                    #_LOGGER.warning(f'Fast no-vars')
                    return FinitePattern(i, csort, {})

            _LOGGER.warning(f"** Abstraction closed pattern {self.rs.kprint.kore_to_pretty(c)} as Top")
            return FinitePattern(-1, csort, None)

        
        #pls: T.List[T.Tuple[int, Kore.Pattern]] = list(enumerate(self.pl))
        subsumer: T.Callable[[Kore.Pattern], T.Tuple[bool, T.Dict[str,str] | None]] = Subsumer(c=c, rs=self.rs)
        #holds: T.List[T.Tuple[bool, T.Dict[str,str] | None]] = [(False, {})]
        #holds = self.rs.kcspool.pool.map(subsumer, [p for p,i in self.open_patterns])
        # Lazy map, not parallel
        holds = map(subsumer, [p for p,i in self.open_patterns])
        for i,(h,renaming) in enumerate(holds):
            if not h:
                continue
            reversed_renaming = { v:k for k,v in (renaming or dict()).items() }
            #_LOGGER.warning(f'(found something)')
            return FinitePattern(self.open_patterns[i][1], csort, reversed_renaming)
        #_LOGGER.warning(f'(no nice pattern found)')
        return FinitePattern(-1, csort, None)
    
    def is_top(self, a: IAbstractPattern) -> bool:
        assert type(a) is FinitePattern
        return a.idx == -1

    def concretize(self, a: IAbstractPattern) -> Kore.Pattern:
        assert type(a) is FinitePattern
        if self.is_top(a):
            return Kore.Top(a.sort)
        return KoreUtils.rename_vars(a.renaming or dict(), self.pl[a.idx])
    
    def subsumes(self, a1: IAbstractPattern, a2: IAbstractPattern) -> bool:
        assert type(a1) is FinitePattern
        assert type(a2) is FinitePattern

        if a1.sort != a2.sort:
            return False

        if a2.idx == -1:
            return True
        ## I am not sure if this is a valid optimization. It would be nice
        # if a1.idx == a2.idx:
        #     return True

        if self.is_top(a2):
            return True
        
        if self.is_top(a1):
            return False
        
        return self.rs.subsumes(self.concretize(a1), self.concretize(a2))[0]

    def print(self, a: IAbstractPattern) -> str:
        c = self.concretize(a)
        assert not KoreUtils.is_top(c)
        return self.rs.kprint.kore_to_pretty(c)
