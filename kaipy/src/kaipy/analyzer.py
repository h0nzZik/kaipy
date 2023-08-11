import abc
import dataclasses
import itertools
import functools
import logging
import pprint
import typing as T

from immutabledict import immutabledict

import pyk.kore.prelude as KorePrelude
import pyk.kore.rpc as KoreRpc
import pyk.kore.syntax as Kore
from pyk.ktool.kprint import KPrint

import kaipy.rs_utils as RSUtils
import kaipy.kore_utils as KoreUtils

from kaipy.IAbstractPatternDomain import IAbstractPattern, IAbstractPatternDomain
from kaipy.IAbstractSubstitutionDomain import IAbstractSubstitution, IAbstractSubstitutionDomain

from .ReachabilitySystem import ReachabilitySystem, KoreClientServer, get_global_kcs
from .KompiledDefinitionWrapper import KompiledDefinitionWrapper
from .Substitution import Substitution

_LOGGER: T.Final = logging.getLogger(__name__)



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
class StateInfo:
    pattern: Kore.Pattern
    description: str
    substitutions: T.List[IAbstractSubstitution]
    
    def insert(
        self,
        abstract_domain: IAbstractSubstitutionDomain,
        abstract_subst: IAbstractSubstitution,
    ) -> bool:
        if self.description == 'IMP.assignment':
            _LOGGER.warning(f'inserting {pprint.pformat(abstract_domain.print(abstract_subst))}')
        for sub in self.substitutions:
            if abstract_domain.subsumes(abstract_subst, sub):
                if self.description == 'IMP.assignment':
                    _LOGGER.warning(f'(subsumed)')
                return False

        self.substitutions.append(abstract_subst)
        if self.description == 'IMP.assignment':        
            _LOGGER.warning(f'(new)')
        return True


    def print(self, kprint: KPrint, subst_domain: IAbstractSubstitutionDomain):
        print(f'state {self.description}')
        print(f'{kprint.kore_to_pretty(self.pattern)}')
        print(f'info:')
        for subst in self.substitutions:
            print(f'{subst_domain.print(subst)}')


@dataclasses.dataclass
class States:
    states_by_pattern: T.Dict[Kore.Pattern, StateInfo]
    states_by_id: T.Dict[str, StateInfo]

    def info_by_id(self, id: str) -> StateInfo:
        return self.states_by_id[id]
    
    def info_by_pattern(self, pattern: Kore.Pattern):
        return self.states_by_pattern[pattern]

    def print(
        self,
        kprint: KPrint,
        subst_domain: IAbstractSubstitutionDomain
    ) -> None:
        print("****STATES****")
        for st in self.states_by_pattern:
            self.states_by_pattern[st].print(kprint, subst_domain)


def build_states(rs: ReachabilitySystem, vars_to_avoid: T.Set[Kore.EVar]) -> States:
    d : T.Dict[Kore.Pattern, StateInfo] = dict()
    d2: T.Dict[str, StateInfo] = dict()

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
                info = StateInfo(pattern=pattern_renamed, description=original_rule_label, substitutions=[])
                d[pattern_renamed] = info
                d2[original_rule_label] = info
                #print(f'renamed LHS (new state): {rs.kprint.kore_to_pretty(pattern_renamed)}')
    return States(states_by_pattern=d, states_by_id=d2)


def get_abstract_subst_of_state(
    rs: ReachabilitySystem,
    subst_domain: IAbstractSubstitutionDomain,
    conj_simplified : Kore.Pattern,
    fvs: T.Set[Kore.EVar],
    renaming: T.Dict[str,str]
) -> T.Tuple[IAbstractSubstitution,Substitution] | None:
    if KoreUtils.is_bottom(conj_simplified):
        return None
    eqls: T.Dict[Kore.EVar, Kore.Pattern] = KoreUtils.extract_equalities_from_witness(
        {ev.name for ev in fvs},
        conj_simplified
    )
    eqls_filtered = {k:v for k,v in eqls.items() if not KoreUtils.is_top(v)}
    renaming_back = reverse_renaming(renaming)
    eqls_filtered_renamed = { Kore.EVar(name=renaming_back[k.name], sort=k.sort):v for k,v in eqls_filtered.items()}
    new_subst = Substitution(immutabledict(eqls_filtered_renamed))
    abstract_subst: IAbstractSubstitution = subst_domain.abstract(new_subst)
    return abstract_subst,new_subst

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
    st: Kore.Pattern
    st_renamed: Kore.Pattern
    renaming: T.Dict[str, str]

    def with_conj(self, new_conj: Kore.Pattern) -> "RawPatternProjection":
        return RawPatternProjection(
            conj=new_conj,
            info=self.info,
            st=self.st,
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
        st=to,
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
        for st,info in states.states_by_pattern.items():
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
            #_LOGGER.warning(f'crawcon: st_renamed = {rs.kprint.kore_to_pretty(ci2.st_renamed)}')
            #_LOGGER.warning(f'crawcon: renaming = {ci2.renaming}')
            evars = KoreUtils.free_evars_of_pattern(ci2.st_renamed)
            ac_subst: T.Tuple[IAbstractSubstitution,Substitution] | None = get_abstract_subst_of_state(
                rs=rs,
                subst_domain=subst_domain,
                conj_simplified=ci2.conj,
                fvs=evars,
                renaming=ci2.renaming,
            )
            if ac_subst is None:
                continue
            abstract_subst,concrete_subst = ac_subst
            if ci2.info.description == 'IMP.assignment':
                _LOGGER.warning(f'Concrete subst: {concrete_subst}')
                _LOGGER.warning(f'Abstract subst: {abstract_subst}')
                
            #_LOGGER.warning(f'Abstract subst: {abstract_subst}')
            is_new: bool = ci2.info.insert(subst_domain, abstract_subst)
            if is_new:
                for concretized_subst in subst_domain.concretize(abstract_subst):
                    #print(f'st vars: {KoreUtils.free_evars_of_pattern(ci2.st_renamed)}')
                    #print(f'concretized subst vars: {set(concretized_subst.mapping.keys())}')
                    #sort = rs.kdw.sortof(ci2.st_renamed)
                    #p0 = Kore.And(sort, ci2.st_renamed, concretized_subst.kore(sort))
                    #p1 = KoreUtils.rename_vars(ci2.renaming, p0)
                    #_LOGGER.warning(f'New concretized projection: {rs.kprint.kore_to_pretty(p1)}')
                    #new_ps_raw.append(p1)
                    sort = rs.kdw.sortof(ci2.st)
                    p0 = Kore.And(sort, ci2.st, concretized_subst.kore(sort))
                    #_LOGGER.warning(f'New concretized projection: {rs.kprint.kore_to_pretty(p0)}')
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
    conjinfos2: T.List[RawPatternProjection] = [ci.with_conj(conj2) for ci,conj2 in zip(conjinfos, conjs_simplified) if not KoreUtils.is_bottom(conj2)]
    _LOGGER.warning(f'Non-bottoms: {len(conjinfos2)}')

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
    cfgs = [normalize_pattern(rs.simplify(initial_configuration))]
    #_LOGGER.warning(f'initial: {rs.kprint.kore_to_pretty(cfgs[0])}')
    current_ps = for_each_match(rs, states, cfgs, subst_domain)
    while len(current_ps) > 0:
        _LOGGER.warning(f'remaining {len(current_ps)} states')
        cfg = current_ps.pop()
        #cfg = normalize_pattern(cfg)
        #_LOGGER.warning(f'cfg {rs.kprint.kore_to_pretty(cfg)}')
        successors = [normalize_pattern(s) for s in get_successors(rs, cfg)]
        _LOGGER.warning(f'Has {len(successors)} successors')
        #for succ in successors:
        #    _LOGGER.warning(f'succ: {rs.kprint.kore_to_pretty(succ)}')
        new_ps: T.List[Kore.Pattern] = for_each_match(rs, states, successors, subst_domain)
        _LOGGER.warning(f'After processing: {len(new_ps)} states')
        current_ps.extend(new_ps)


    return states
