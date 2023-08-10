import abc
import dataclasses
import itertools
import functools
import logging
import typing as T

from immutabledict import immutabledict

import pyk.kore.prelude as KorePrelude
import pyk.kore.rpc as KoreRpc
import pyk.kore.syntax as Kore

import kaipy.rs_utils as RSUtils
import kaipy.kore_utils as KoreUtils

from .ReachabilitySystem import ReachabilitySystem, KoreClientServer, get_global_kcs
from .KompiledDefinitionWrapper import KompiledDefinitionWrapper
from .Substitution import Substitution

_LOGGER: T.Final = logging.getLogger(__name__)

class IAbstractPattern(abc.ABC):
    ...

class IAbstractPatternDomain(abc.ABC):
    @abc.abstractmethod
    def abstract(self, c: Kore.Pattern) -> IAbstractPattern:
        ...

    @abc.abstractmethod
    def is_top(self, a: IAbstractPattern) -> bool:
        ...

    @abc.abstractmethod
    def concretize(self, a: IAbstractPattern) -> Kore.Pattern:
        ...
    
    @abc.abstractmethod
    def subsumes(self, a1: IAbstractPattern, a2: IAbstractPattern) -> bool:
        ...
    
    @abc.abstractmethod
    def print(self, a: IAbstractPattern) -> str:
        ...


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
        _LOGGER.warning(f'abstracting {c.text}')
        # Optimization
        match c:
            case Kore.EVar(_, _):
                # TODO generalize this to `inj(EVar)``
                _LOGGER.warning(f'Fast -1')
                return FinitePattern(-1, csort, None)
        
        # another optimization: for terms without free variables
        # it is enough to check for an equality with patterns without free variables.
        # This assumes functionality of both patterns.
        # For terms with free variables it is necessary to check for subsumtion/implication
        # but it is enough to consider patterns *with* free variables.
        if len(KoreUtils.free_evars_of_pattern(c)) == 0:
            for p,i in self.closed_patterns:
                if p == c:
                    _LOGGER.warning(f'Fast no-vars')
                    return FinitePattern(i, csort, {})
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
            _LOGGER.warning(f'(found something)')
            return FinitePattern(self.open_patterns[i][1], csort, reversed_renaming)
        _LOGGER.warning(f'(no nice pattern found)')
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
        return self.rs.kprint.kore_to_pretty(self.concretize(a))


class IAbstractSubstitution(abc.ABC):
    ...

class IAbstractSubstitutionDomain(abc.ABC):
    @abc.abstractmethod
    def concretize(self, a: IAbstractSubstitution) -> T.Set[Substitution]:
        ...
    
    @abc.abstractmethod
    def abstract(self, subst: Substitution) -> IAbstractSubstitution:
        ...


    @abc.abstractmethod
    def subsumes(self, a1: IAbstractSubstitution, a2: IAbstractSubstitution) -> bool:
        ...
    
    @abc.abstractmethod
    def print(self, a: IAbstractSubstitution) -> str:
        ...

# Turns
# { x |-> {phi1, phi2}, y |-> {phi3, phi4} }
# into
# { {x |-> phi1, y |-> phi3}, {x |-> phi1, y |-> phi4}, {x |-> phi2, y |-> phi3}, {x |-> phi2, y |-> phi4}  }
def cartesian_dict(d: T.Mapping[T.Any, T.Any]) -> T.Set[T.Mapping[T.Any, T.Any]]:
    if len(list(d.keys())) == 0:
        return {immutabledict()}
    k = list(d.keys())[0]
    xs = d[k]
    d1: immutabledict[T.Any,T.Any] = immutabledict({k1:v1 for k1,v1 in d.items() if not k1 == k})
    cd = cartesian_dict(d1)
    result: T.Set[T.Any] = set()
    for di in cd:
        for x in xs:
            d2 = { k0:v0 for k0,v0 in di.items() }
            d2.update({k:x})
            result.add(immutabledict(d2))
    return result

@dataclasses.dataclass
class CartesianAbstractSubstitution(IAbstractSubstitution):
    mapping: T.Mapping[Kore.EVar, IAbstractPattern]

class CartesianAbstractSubstitutionDomain(IAbstractSubstitutionDomain):
    pattern_domain: IAbstractPatternDomain

    def __init__(self, pattern_domain: IAbstractPatternDomain):
        self.pattern_domain = pattern_domain
    
    def abstract(self, subst: Substitution) -> IAbstractSubstitution:
        return CartesianAbstractSubstitution(
            {
                v : self.pattern_domain.abstract(p)
                for (v,p) in subst.mapping.items()
            }
        )

    def concretize(self, a: IAbstractSubstitution) -> T.Set[Substitution]:
        assert type(a) is CartesianAbstractSubstitution

        # If `v` is top, we do not want to concretize it,
        # because the resulting constraint would be something like
        # `X = Top()`. But such substitution is useless.
        concretes: T.Dict[Kore.EVar, Kore.Pattern] = {
            k : self.pattern_domain.concretize(v)
            for k,v in a.mapping.items()
            if not self.pattern_domain.is_top(v)
        }
        return {Substitution(immutabledict(concretes))}
    
    def subsumes(self, a1: IAbstractSubstitution, a2: IAbstractSubstitution) -> bool:
        assert type(a1) is CartesianAbstractSubstitution
        assert type(a2) is CartesianAbstractSubstitution
        # If there is some key `k` in `a2` which is not in `a1`,
        # it means that `a2` restricts the state more than `a1`;
        # in that case, `a1` is not subsumed by `a2`.
        if not set(a1.mapping.keys()).issuperset(a2.mapping.keys()):
            return False
        # `a1` contains more keys; these are not restricted by `a2`.
        # It is enough to check for the keys of `a2`
        return all(
            [
                self.pattern_domain.subsumes(a1.mapping[k], a2.mapping[k])
                for k in a2.mapping.keys()
            ]
        )

    def print(self, a: IAbstractSubstitution) -> str:
        assert type(a) is CartesianAbstractSubstitution
        return str({ k: self.pattern_domain.print(v) for k,v in a.mapping.items() })


@dataclasses.dataclass
class StateInfo:
    description: str
    substitutions: T.List[IAbstractSubstitution]
    
    def insert(
        self,
        abstract_domain: IAbstractSubstitutionDomain,
        abstract_subst: IAbstractSubstitution,
    ) -> bool:
        for sub in self.substitutions:
            if abstract_domain.subsumes(abstract_subst, sub):
                return False

        self.substitutions.append(abstract_subst)        
        return True


@dataclasses.dataclass
class States:
    states: T.Dict[Kore.Pattern, StateInfo]

def print_states(
    states: States,
    rs: ReachabilitySystem,
    subst_domain: IAbstractSubstitutionDomain
) -> None:
    print("****STATES****")
    for i,st in enumerate(states.states):
        print(f'state: {rs.kprint.kore_to_pretty(st)}')
        print(f'info:')
        for subst in states.states[st].substitutions:
            print(f'{subst_domain.print(subst)}')


def build_states(rs: ReachabilitySystem, vars_to_avoid: T.Set[Kore.EVar]) -> States:
    d : T.Dict[Kore.Pattern, StateInfo] = dict()

    for axiom in rs.kdw.rewrite_rules:
        match axiom:
            case Kore.Axiom(_, Kore.Rewrites(_, lhs, _), _):
                pattern: Kore.Pattern = lhs
                original_rule_label: str = KoreUtils.axiom_label(axiom)
                applicable_rules: T.List[str] = []
                
                vars_to_rename = [
                    ev
                    for ev in KoreUtils.free_evars_of_pattern(pattern)
                    if ev.name in vars_to_avoid
                ]
                pattern_renamed: Kore.Pattern = KoreUtils.rename_vars(
                    KoreUtils.compute_renaming0(
                        vars_to_avoid=list(vars_to_avoid),
                        vars_to_rename=vars_to_rename
                    ),
                    pattern,
                )
                d[pattern_renamed] = StateInfo(original_rule_label, [])
                #print(f'renamed LHS (new state): {rs.kprint.kore_to_pretty(pattern_renamed)}')
    return States(d)


def conj_with_subst(
    rs: ReachabilitySystem,
    p: Kore.Pattern,
    renaming: T.Dict[str, str],
    s: Substitution
) -> Kore.Pattern:
    sort = rs.sortof(p)
    p_renamed_back = KoreUtils.rename_vars(reverse_renaming(renaming), p)
    # Safety check: all variables of the substitution have to be in the main body
    evs = KoreUtils.free_evars_of_pattern(p_renamed_back)
    for ev in s.mapping.keys():
        if ev not in evs:
            _LOGGER.error(f'Variable {ev} of substitution is not in renamed-back pattern')
            _LOGGER.error(f'Subst: {s}')
            _LOGGER.error(f'pattern: {rs.kprint.kore_to_pretty(p_renamed_back)}')
            assert(False)

    return Kore.And(sort, p_renamed_back, s.kore(sort))
    
    #renaming = KoreUtils.compute_renaming0(
    #    vars_to_avoid=list(KoreUtils.free_evars_of_pattern(p)),
    #    vars_to_rename=list(itertools.chain(*[list(KoreUtils.free_evars_of_pattern(v)) for k,v in s.mapping.items()]))
    #)
    #s2 = Substitution({k : KoreUtils.rename_vars(renaming, v) for k,v in s.mapping.items()})
    #s_p = s2.kore(sort)
    #return Kore.And(sort, p, s_p)

def get_abstract_subst_of_state(
    rs: ReachabilitySystem,
    subst_domain: IAbstractSubstitutionDomain,
    conj_simplified : Kore.Pattern,
    fvs: T.Set[Kore.EVar],
) -> IAbstractSubstitution | None:
    if KoreUtils.is_bottom(conj_simplified):
        return None
    eqls: T.Dict[Kore.EVar, Kore.Pattern] = KoreUtils.extract_equalities_from_witness(
        {ev.name for ev in fvs},
        conj_simplified
    )
    new_subst = Substitution(immutabledict(eqls))
    abstract_subst: IAbstractSubstitution = subst_domain.abstract(new_subst)
    return abstract_subst

def rename_to_avoid(
    pattern_to_rename: Kore.Pattern,
    pattern_to_avoid: Kore.Pattern
) -> T.Tuple[Kore.Pattern, T.Dict[str, str]]:
    renaming = KoreUtils.compute_renaming0(
        vars_to_avoid=list(KoreUtils.free_evars_of_pattern(pattern_to_avoid)),
        vars_to_rename=list(KoreUtils.free_evars_of_pattern(pattern_to_rename))
    )
    st_renamed = KoreUtils.rename_vars(
        renaming,
        pattern_to_rename
    )
    return st_renamed,renaming

def reverse_renaming(renaming: T.Dict[str, str]) -> T.Dict[str, str]:
    return {v:k for k,v in renaming.items()}

@dataclasses.dataclass(frozen=True)
class RawPatternProjection:
    conj: Kore.Pattern
    info: StateInfo
    st_renamed: Kore.Pattern
    renaming: T.Dict[str, str]

    def with_conj(self, new_conj: Kore.Pattern) -> "RawPatternProjection":
        return RawPatternProjection(
            conj=new_conj,
            info=self.info,
            st_renamed=self.st_renamed,
            renaming=self.renaming
        )

def compute_raw_pattern_projection(
    rs: ReachabilitySystem,
    what: Kore.Pattern,
    to: Kore.Pattern,
    info: StateInfo
) -> RawPatternProjection:
    to_renamed,renaming = rename_to_avoid(to, what)
    conj = Kore.And(rs.top_sort, what, to_renamed)
    return RawPatternProjection(
        conj=conj,
        info=info,
        st_renamed=to_renamed,
        renaming=renaming,
    )

def compute_list_of_raw_pattern_projections(
    rs: ReachabilitySystem,
    states: States,
    cfgs: T.List[Kore.Pattern],
) -> T.List[RawPatternProjection]:
    conjinfos: T.List[RawPatternProjection] = list()
    for cfg in cfgs:
        for st,info in states.states.items():
            conjinfos.append(
                compute_raw_pattern_projection(
                    rs,
                    cfg,
                    st,
                    info
                )
            )
    return conjinfos

def compute_raw_concretizations(
    rs: ReachabilitySystem,
    subst_domain: IAbstractSubstitutionDomain,
    conjinfos2: T.List[RawPatternProjection]
) -> T.List[Kore.Pattern]:
    new_ps_raw : T.List[Kore.Pattern] = list()
    for ci2 in conjinfos2:
            evars = KoreUtils.free_evars_of_pattern(ci2.st_renamed)
            abstract_subst: IAbstractSubstitution | None = get_abstract_subst_of_state(
                rs=rs,
                subst_domain=subst_domain,
                conj_simplified=ci2.conj,
                fvs=evars,
            )
            if abstract_subst is None:
                continue
            is_new: bool = ci2.info.insert(subst_domain, abstract_subst)
            if is_new:
                for concretized_subst in subst_domain.concretize(abstract_subst):
                    #print(f'st vars: {KoreUtils.free_evars_of_pattern(ci2.st_renamed)}')
                    #print(f'concretized subst vars: {set(concretized_subst.mapping.keys())}')
                    p0 = conj_with_subst(
                        rs,
                        ci2.st_renamed,
                        ci2.renaming,
                        concretized_subst
                    )
                    _LOGGER.warning(f'New concretized projection: {rs.kprint.kore_to_pretty(p0)}')
                    new_ps_raw.append(p0)
    return new_ps_raw

def for_each_match(
    rs: ReachabilitySystem,
    states: States,
    cfgs: T.List[Kore.Pattern],
    subst_domain: IAbstractSubstitutionDomain,
) -> T.List[Kore.Pattern]:
    conjinfos: T.List[RawPatternProjection] = compute_list_of_raw_pattern_projections(rs, states, cfgs)
    _LOGGER.warning(f'Simplifying {len(conjinfos)} items at once')
    conjs_simplified = rs.map_simplify([ci.conj for ci in conjinfos])
    _LOGGER.warning(f'done.')
    conjinfos2: T.List[RawPatternProjection] = [ci.with_conj(conj2) for ci,conj2 in zip(conjinfos, conjs_simplified)]

    new_ps_raw : T.List[Kore.Pattern] = compute_raw_concretizations(rs, subst_domain, conjinfos2)

    _LOGGER.warning(f'Simplifying {len(new_ps_raw)} items at once (second)')
    #for pr in new_ps_raw:
    #    _LOGGER.warning(f'Item: {rs.kprint.kore_to_pretty(pr)}')
    new_ps_0 = rs.map_simplify(new_ps_raw)
    _LOGGER.warning(f'(done)')
    new_ps: T.List[Kore.Pattern] = list()
    for p in new_ps_0:
        #print(f'Cleaning up')
        p2 = RSUtils.cleanup_pattern(rs, p)
        new_ps.append(p2)
    return new_ps
            

def normalize_pattern(cfg: Kore.Pattern) -> Kore.Pattern:
    vs = KoreUtils.free_occs_det(cfg)
    renaming = { v.name : ("VAR"+str(i)) for i,v in enumerate(vs)}
    return KoreUtils.rename_vars(renaming, cfg)

def build_abstract_substitution_domain(
    rs: ReachabilitySystem,
    rests: T.List[Kore.Pattern],
    initial_configuration: Kore.Pattern
) -> IAbstractSubstitutionDomain:
    initial_configuration = rs.simplify(initial_configuration)
    finite_set_of_patterns = rests + list(KoreUtils.some_subpatterns_of(initial_configuration).keys())
    pattern_domain: IAbstractPatternDomain = FinitePatternDomain(finite_set_of_patterns, rs)
    subst_domain: IAbstractSubstitutionDomain = CartesianAbstractSubstitutionDomain(pattern_domain)
    return subst_domain

def get_successors(rs: ReachabilitySystem, cfg: Kore.Pattern) -> T.List[Kore.Pattern]:
    exec_result: KoreRpc.ExecuteResult = rs.execute_step(cfg)
    if exec_result.next_states is not None:
        successors = [s.kore for s in exec_result.next_states]
    else:
        successors = [exec_result.state.kore]
    return successors

def analyze(
    rs: ReachabilitySystem,
    subst_domain: IAbstractSubstitutionDomain,
    initial_configuration: Kore.Pattern,
) -> States:
    states: States = build_states(rs, KoreUtils.free_evars_of_pattern(initial_configuration))
    #print(f'initial: {rs.kprint.kore_to_pretty(initial_configuration)}')
    cfgs = [normalize_pattern(initial_configuration)]
    current_ps = for_each_match(rs, states, cfgs, subst_domain)
    while len(current_ps) > 0:
        _LOGGER.warning(f'remaining {len(current_ps)} states')
        cfg = current_ps.pop()
        #cfg = normalize_pattern(cfg)
        #_LOGGER.warning(f'cfg {rs.kprint.kore_to_pretty(cfg)}')
        successors = [normalize_pattern(s) for s in get_successors(rs, cfg)]
        _LOGGER.warning(f'Has {len(successors)} successors')
        new_ps: T.List[Kore.Pattern] = for_each_match(rs, states, successors, subst_domain)
        _LOGGER.warning(f'After processing: {len(new_ps)} states')
        current_ps.extend(new_ps)


    return states
