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

from kaipy.IBroadcastChannel import IBroadcastChannel
from kaipy.VariableManager import VariableManager
from kaipy.AbstractionContext import AbstractionContext
from kaipy.IAbstractPatternDomain import IAbstractPattern, IAbstractPatternDomain
from kaipy.IAbstractSubstitutionDomain import IAbstractSubstitution, IAbstractSubstitutionDomain
from kaipy.IAbstractConstraintDomain import IAbstractConstraintDomain, IAbstractConstraint

from .ReachabilitySystem import ReachabilitySystem, KoreClientServer, get_global_kcs
from .KompiledDefinitionWrapper import KompiledDefinitionWrapper
from .Substitution import Substitution

_LOGGER: T.Final = logging.getLogger(__name__)


# TODO remove
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
    # In general, we do not know here how IAbstractSubstitution is implemented;
    # it does not need to have keys and values.
    # The only thing we know that its concretization will be a Substitution.
    # and that it will have the keys that the original substitution had.
    # Therefore, we need to store the mapping from which the original substitution was created,
    # so that we can apply it reversely on concretized substitutions.
    #substitutions: T.List[T.Tuple[IAbstractSubstitution, T.Mapping[str,str]]]
    specializations: T.List[IAbstractConstraint]
    
    def insert(
        self,
        abstract_domain: IAbstractConstraintDomain,
        abstract_constraint: IAbstractConstraint,
    ) -> bool:
        #if self.description == 'IMP.assignment':
        #    _LOGGER.warning(f'inserting {abstract_domain.print(abstract_subst)}')
        for spec in self.specializations:
            # TODO maybe we should only check for equality
            # (using the abstract domain)
            #if abstract_domain.equals(abstract_subst, sub):
            if abstract_domain.subsumes(abstract_constraint, spec):
               #if self.description == 'IMP.assignment':
                #    _LOGGER.warning(f'(subsumed)')
                return False

        # TODO: We might also want to go through the all abstract substitutions
        # that are subsumed by the new one, and remove them.
        # I do not know yet whether we want that behavior.
        self.specializations.append(abstract_constraint)
        #if self.description == 'IMP.assignment':        
        #    _LOGGER.warning(f'(new)')
        return True

    def concrete_specializations(self, constraint_domain: IAbstractConstraintDomain) -> T.Iterable[T.List[Kore.MLPred]]:
        for spec in self.specializations:
            concrete_constraints = constraint_domain.concretize(spec)
            yield concrete_constraints

    def print(self, kprint: KPrint, constraint_domain: IAbstractConstraintDomain):
        print(f'state {self.description}')
        print(f'{kprint.kore_to_pretty(self.pattern)}')
        print(f'info:')
        for i,constraints in enumerate(self.concrete_specializations(constraint_domain)):
            print(f' {i}')
            for con in constraints:
                print(f'  {kprint.kore_to_pretty(con)}')

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
        constraint_domain: IAbstractConstraintDomain
    ) -> None:
        print("****STATES****")
        for st in self.states_by_pattern:
            self.states_by_pattern[st].print(kprint, constraint_domain)


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
                pattern_clean = RSUtils.cleanup_pattern(rs, rs.simplify(pattern_renamed))
                info = StateInfo(pattern=pattern_clean, description=original_rule_label, specializations=[])
                d[pattern_clean] = info
                d2[original_rule_label] = info
                #print(f'renamed LHS (new state): {rs.kprint.kore_to_pretty(pattern_renamed)}')
    return States(states_by_pattern=d, states_by_id=d2)

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

def reverse_renaming(renaming: T.Mapping[str, str]) -> T.Dict[str, str]:
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

# What is going on with the renamings?
# 1. we have a state pattern `st` with set of free variables `vs1`.
# 2. we renamed it into `st_renamed` with set of free variables `vs2`, using a renaming `vs_to_vs2`
#    in order to avoid collisions with a pattern `c`.
# 3. we compute concrete_subst and abstract_subst from a subset of `vs2` into some patterns over `vs3`.
# 4. we concretize `abstract_subst` into `concretized_subst`
# 5. Since `vs3` may overlap with `vs2` and `vs1`, we compute some set `vs4` and a renaming `vs3_to_vs4`.
# 6. We rename RHSs of `concretized_subst` using `vs3_to_vs4`, creating `concretized_subst_renamed`.
# 7. apply `concretized_subst_renamed` to `st_renamed`, creating `concretized_pattern_renamed`
# 8. `concretized_pattern_renamed` my contain some free variables of `vs2` (the ones that were not substituted).
#    We have to rename it back using the reverse of `vs1_to_vs2`.

def compute_raw_concretizations(
    ctx: AbstractionContext,
    rs: ReachabilitySystem,
    constraint_domain: IAbstractConstraintDomain,
    conjinfos2: T.List[RawPatternProjection]
) -> T.List[Kore.Pattern]:
    new_ps_raw : T.List[Kore.Pattern] = list()
    for ci2 in conjinfos2:
            #_LOGGER.warning(f'crawcon: renaming = {ci2.renaming}')
            if KoreUtils.is_bottom(ci2.conj):
                continue
            _LOGGER.warning(f'st_renamed ({ci2.info.description}) = {rs.kprint.kore_to_pretty(ci2.st_renamed)}')
            evars = KoreUtils.free_evars_of_pattern(ci2.st_renamed)
            #_LOGGER.warning(f'EVARS: {evars}')
            #_LOGGER.warning(f'conj_simplified: {rs.kprint.kore_to_pretty(conj_simplified)}')
            # A problem occurring here is that `conj_simplified` is too simplified:
            # it does not contain predicates that the backend is able to deduce are always true.
            # For example, we might have a state:
            # `</k> someValue() ~> #freezer() ...</k>`
            # and a cooling rule
            # ```
            # <k> (X:Stmt ~> #freezer()) => something(...) ...</k>
            # \and true = isKResult(X ~> .)
            # ```
            # , which yields a match `X \equiv someValue()`
            # but the fact that `isKResult(X ~> .)` is forgotten.
            # Therefore, we have to read the predicates of the state
            # and add them to the list of predicates derived from the conjunction.
            #_LOGGER.warning('eqls:')
            #for k,v in eqls.items():
            #    _LOGGER.warning(f"  {k} : {rs.kprint.kore_to_pretty(v)}")    
            st_predicates = KoreUtils.get_predicates(ci2.st_renamed)
            remainders = KoreUtils.get_predicates(ci2.conj)
            all_predicates = remainders + st_predicates

            abstract_constraint = constraint_domain.abstract(ctx, [p for p in all_predicates])

            is_new: bool = ci2.info.insert(constraint_domain, abstract_constraint)
            if is_new:
                constraints = constraint_domain.concretize(abstract_constraint)
                new_constraint: Kore.Pattern = RSUtils.make_conjunction(rs, [p for p in constraints])
                _LOGGER.warning(f'new_constraint (without any renaming): {rs.kprint.kore_to_pretty(new_constraint)}')
                # # It might happen that some RHS of the substitution contains a free variable
                # # that also occurs in ci2.st and is not simultaneously mapped to something else.
                # # For example, we might have:
                # #   `ci2.st = <k> X ~> Y ~> .K </k>`
                # #   `subst = { X : foo(Y) }`
                # # And that would be a problem.
                # vars_to_avoid = list(
                #     KoreUtils.free_evars_of_pattern(ci2.st_renamed)
                #     .union(KoreUtils.free_evars_of_pattern(ci2.st))
                # )
                # vars_to_rename = list(itertools.chain(*[
                #     KoreUtils.free_evars_of_pattern(p)
                #     for p in concretized_subst.mapping.values()
                # ]))
                # renaming = KoreUtils.compute_renaming0(
                #     vars_to_avoid,
                #     vars_to_rename
                # )
                # concretized_subst_renamed = Substitution(
                #     {k:KoreUtils.rename_vars(renaming, v)
                #     for k,v in concretized_subst.mapping.items()}
                # )
                # new_constraint_renamed: Kore.Pattern = KoreUtils.rename_vars(
                #     renaming,
                #     new_constraint
                # )
                # _LOGGER.warning(f'new_constraint_renamed: {rs.kprint.kore_to_pretty(new_constraint_renamed)}')
                # concretized_pattern_renamed: Kore.Pattern = KoreUtils.apply_subst(
                #     concretized_subst_renamed.mapping,
                #     ci2.st_renamed
                # )
                # concretized_pattern: Kore.Pattern = KoreUtils.rename_vars(
                #     reverse_renaming(ci2.renaming),
                #     concretized_pattern_renamed
                # )
                new_constraint_rback: Kore.Pattern = KoreUtils.rename_vars(
                    reverse_renaming(ci2.renaming),
                    new_constraint
                )
                _LOGGER.warning(f'new_constraint_rback: {rs.kprint.kore_to_pretty(new_constraint_rback)}')
                #_LOGGER.warning(f'Concretized (back with original variables): {rs.kprint.kore_to_pretty(concretized_pattern)}')
                #new_ps_raw.append(concretized_pattern)
                #conj = Kore.And(rs.sortof(concretized_pattern), concretized_pattern, new_constraint_rback)
                new_ps_raw.append(new_constraint_rback)
                #ci2_st_renamed = KoreUtils.rename_vars(renaming, ci2.st_renamed)
                #_LOGGER.warning(f'ci2_st_renamed: {rs.kprint.kore_to_pretty(ci2_st_renamed)}')
                #p0 = KoreUtils.apply_subst(concretized_subst.mapping, ci2_st_renamed)
                #_LOGGER.warning(f'Concretized (still renamed): {rs.kprint.kore_to_pretty(p0)}')
                #p1 = KoreUtils.rename_vars(reverse_renaming(ci2.renaming), p0)
                #_LOGGER.warning(f'Concretized (back with original variables): {rs.kprint.kore_to_pretty(p1)}')
                #new_ps_raw.append(p0)
    return new_ps_raw

def for_each_match(
    rs: ReachabilitySystem,
    states: States,
    cfgs: T.List[Kore.Pattern],
    constraint_domain: IAbstractConstraintDomain,
    ctx: AbstractionContext,
) -> T.List[Kore.Pattern]:
    # list of conjunctions of `cfgs` and renamed `states`
    conjinfos: T.List[RawPatternProjection] = compute_list_of_raw_pattern_projections(rs, states, cfgs)
    #_LOGGER.warning(f'Simplifying {len(conjinfos)} items at once')
    conjs_simplified = rs.map_simplify([ci.conj for ci in conjinfos])
    #_LOGGER.warning(f'done.')
    conjinfos2: T.List[RawPatternProjection] = [ci.with_conj(conj2) for ci,conj2 in zip(conjinfos, conjs_simplified) if not KoreUtils.is_bottom(conj2)]
    # We cannot cleanup the pattern, because then it would not contain the desired equalities, but only the term common to the two conjuncts.
    #conjinfos2: T.List[RawPatternProjection] = [ci.with_conj(RSUtils.cleanup_pattern(rs, conj2)) for ci,conj2 in zip(conjinfos, conjs_simplified) if not KoreUtils.is_bottom(conj2)]
    _LOGGER.warning(f'Non-bottoms: {len(conjinfos2)}')
    #for ci in conjinfos2:
    #    _LOGGER.warning(f'conj: {rs.kprint.kore_to_pretty(ci.conj)}')

    new_ps_raw : T.List[Kore.Pattern] = compute_raw_concretizations(ctx=ctx, rs=rs, constraint_domain=constraint_domain, conjinfos2=conjinfos2)
    #_LOGGER.warning(f'new_ps_raw: {len(new_ps_raw)}')
    # We do not need to simplify anymore
    #_LOGGER.warning(f'Simplifying {len(new_ps_raw)} items at once (second)')
    #for pr in new_ps_raw:
    #    _LOGGER.warning(f'Item: {rs.kprint.kore_to_pretty(pr)}')
    #new_ps_0 = rs.map_simplify(new_ps_raw)
    new_ps_0 = new_ps_raw
    #_LOGGER.warning(f'(done)')
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
    constraint_domain: IAbstractConstraintDomain,
    initial_configuration: Kore.Pattern,
) -> States:
    states: States = build_states(rs, KoreUtils.free_evars_of_pattern(initial_configuration))
    class BC(IBroadcastChannel):
        def broadcast(self, m: T.List[Kore.MLPred]):
            pass
    bc = BC()
    vm = VariableManager(5) # TODO generate high-enough number
    ctx = AbstractionContext(broadcast_channel=bc, variable_manager=vm)

    cfgs = [normalize_pattern(rs.simplify(initial_configuration))]
    current_ps = for_each_match(ctx=ctx, rs=rs, states=states, cfgs=cfgs, constraint_domain=constraint_domain)
    while len(current_ps) > 0:
        _LOGGER.warning(f'remaining {len(current_ps)} states')
        cfg = current_ps.pop()
        _LOGGER.warning(f'cfg {rs.kprint.kore_to_pretty(cfg)}')
        successors = [normalize_pattern(s) for s in get_successors(rs, cfg)]
        _LOGGER.warning(f'Has {len(successors)} successors')
        for succ in successors:
            _LOGGER.warning(f'succ: {rs.kprint.kore_to_pretty(succ)}')
        new_ps: T.List[Kore.Pattern] = for_each_match(rs, states, successors, constraint_domain, ctx=ctx)
        _LOGGER.warning(f'After processing: {len(new_ps)} states')
        current_ps.extend(new_ps)


    return states
