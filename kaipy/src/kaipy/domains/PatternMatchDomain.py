import abc
import collections
import dataclasses
import functools as F
import itertools
import time
import typing as T
import logging

import pyk.kore.syntax as Kore

import kaipy.kore_utils as KoreUtils
import kaipy.rs_utils as RSUtils
from kaipy.PerfCounter import PerfCounter
from kaipy.BroadcastChannel import BroadcastChannel
from kaipy.VariableManager import VariableManager
from kaipy.AbstractionContext import AbstractionContext
from kaipy.ReachabilitySystem import ReachabilitySystem
from kaipy.interfaces.IAbstractConstraintDomain import IAbstractConstraint, IAbstractConstraintDomain
from kaipy.interfaces.IAbstractPatternDomain import IAbstractPattern, IAbstractPatternDomain
from kaipy.ParallelMatcher import parallel_match, MatchResult

_LOGGER: T.Final = logging.getLogger(__name__)

@dataclasses.dataclass
class PatternMatchDomainElement(IAbstractPattern):
    constraint_per_state: T.List[IAbstractConstraint|None] # The None is here because not every abstract domain can effectively abstract Bottom
    #renaming: T.Mapping[str, str]

class PatternMatchDomain(IAbstractPatternDomain):
    rs: ReachabilitySystem
    states: T.List[Kore.Pattern]
    state_vars: T.List[T.Set[Kore.EVar]]
    comments: T.Mapping[Kore.Pattern, str]
    underlying_domain: IAbstractConstraintDomain
    abstract_perf_counter: PerfCounter
    concretize_perf_counter: PerfCounter

    # maybe?
    # precondition: `states` must cover all possible configurations; that is, a big disjunction over `states` is Top.
    def __init__(self,
        rs: ReachabilitySystem,
        states: T.List[T.Tuple[Kore.Pattern, str]],
        underlying_domain: IAbstractConstraintDomain,
    ):
        self.rs = rs
        # We need all states to use different variables.
        states2 = [(KoreUtils.normalize_pattern(x, prefix=f"St{i}V"), y) for i,(x, y) in enumerate(states)]
        self.states = [x for (x, y) in states2]
        self.comments = {x:y for (x,y) in states2}
        self.state_vars = [KoreUtils.free_evars_of_pattern(st) for st in self.states]
        #_LOGGER.warning(f"States: {len(states)}")
        self.underlying_domain = underlying_domain
        self.abstract_perf_counter = PerfCounter()
        self.concretize_perf_counter = PerfCounter()

    @F.cached_property
    def _top_sort(self):
        if len(self.states) <= 0:
            return self.rs.top_sort
        return self.rs.sortof(self.states[0])

    @F.cached_property
    def _all_state_evars(self) -> T.Set[Kore.EVar]:
        evs: T.Set[Kore.EVar] = set()
        for st in self.states:
            evs.update(KoreUtils.free_evars_of_pattern(st))
        return evs

    def abstract(self, ctx: AbstractionContext, c: Kore.Pattern) -> PatternMatchDomainElement:
        old = time.perf_counter()
        a = self._abstract(ctx, c)
        new = time.perf_counter()
        self.abstract_perf_counter.add(new - old)
        return a

    def _abstract(self, ctx: AbstractionContext, c: Kore.Pattern) -> PatternMatchDomainElement:
        #_LOGGER.warning(f"c: {c.text}")
        c_simpl = self.rs.simplify(c)
        #_LOGGER.warning(f"c_simpl: {c_simpl.text}")
        c_simpl_list = KoreUtils.or_to_list(c_simpl)
        #_LOGGER.warning(f"c_simpl: {[x.text for x in c_simpl_list]}")
        c_simpl_list_norm = [KoreUtils.normalize_pattern(x) for x in c_simpl_list]

        # We cannot compute one single 'global' renaming, beause then the names of the new variables
        # for a particular pattern from the disjunction depend on all the other patterns that are in the disjunction.
        #renaming = KoreUtils.compute_renaming0(
        #    vars_to_avoid=list(self._all_state_evars),
        #    vars_to_rename=list(itertools.chain(*[KoreUtils.free_evars_of_pattern(x) for x in c_simpl_list_norm])),
        #)
        renamings = [
            KoreUtils.compute_renaming0(
                vars_to_avoid=list(self._all_state_evars),
                vars_to_rename=list(KoreUtils.free_evars_of_pattern(x)),
            )
            for x in c_simpl_list_norm
        ]

        cpsl: T.List[T.List[IAbstractConstraint|None]] = list()
        broadcast_channels = [BroadcastChannel() for _ in self.states]
        for idx,q in enumerate(c_simpl_list_norm):
            #_LOGGER.warning(f"q: {q}")
            mrs: T.List[MatchResult] = parallel_match(rs=self.rs, cfg=q, states=self.states, renaming=renamings[idx])
            constraintss: T.List[T.List[Kore.Pattern]] = [
                mr.constraints
                for mr in mrs
            ]
            cps: T.List[IAbstractConstraint|None] = list()

            for i,constraints in enumerate(constraintss):
                #_LOGGER.warning(f"{i}: {constraints}")
                if KoreUtils.any_is_bottom(constraints):
                    #_LOGGER.warning(f"Skipping bottom at {i}")
                    cps.append(None)
                    continue
                ctx.broadcast_channel = broadcast_channels[i]
                #ctx.broadcast_channel.reset()
                d = self.underlying_domain
                a1 = d.abstract(
                    ctx=ctx,
                    # This has to be constant, otherwise there might be infinitely many abstract substitutions, as the number of variables of a term grows during execution
                    over_variables=self.state_vars[i], #.union({Kore.EVar(renamings[idx][v.name], v.sort) for v in KoreUtils.free_evars_of_pattern(q)}),
                    constraints=constraints,
                )
                cps.append(a1)
                #if len(ctx.broadcast_channel.constraints) == 0:
                #    cps.append(a1)
                #else:
                #    a2: IAbstractConstraint = d.refine(ctx=ctx, a=a1, constraints=ctx.broadcast_channel.constraints)
                #    ctx.broadcast_channel.reset()
                #    cps.append(a2)
            cpsl.append(cps)
        
        # Now compute all the disjunctions
        final_cps: T.List[IAbstractConstraint|None] = [None for _ in self.states]
        for i in range(len(cps)):
            for current_cps in cpsl:
                if final_cps[i] is None:
                    final_cps[i] = current_cps[i]
                    continue
                cci = current_cps[i]
                if cci is None:
                    continue
                fci = final_cps[i]
                assert fci is not None
                final_cps[i] = self.underlying_domain.disjunction(ctx, fci, cci)
        return PatternMatchDomainElement(constraint_per_state=final_cps)#, renaming= KoreUtils.reverse_renaming(renaming))

    def refine(self, ctx: AbstractionContext, a: IAbstractPattern, c: Kore.Pattern) -> PatternMatchDomainElement:
        assert type(a) is PatternMatchDomainElement
        # no-op so far
        return a

    def disjunction(self, ctx: AbstractionContext, a1: IAbstractPattern, a2: IAbstractPattern) -> IAbstractPattern:
        assert type(a1) is PatternMatchDomainElement
        assert type(a2) is PatternMatchDomainElement
        cps = [ 
            self.underlying_domain.disjunction(ctx, b1, b2) if (b1 is not None and b2 is not None) else (b1 if b2 is None else b2)
            for b1,b2 in zip(a1.constraint_per_state,a2.constraint_per_state)
        ]
        # Here we assume that all states have different variables.
        #renaming = dict(a1.renaming)
        #renaming.update(a2.renaming)
        return PatternMatchDomainElement(
            constraint_per_state=cps,
        #    renaming=renaming,
        )

    def is_top(self, a: IAbstractPattern) -> bool:
        assert type(a) is PatternMatchDomainElement
        return all([self.underlying_domain.is_top(b) if b is not None else False for b in a.constraint_per_state])

    def is_bottom(self, a: IAbstractPattern) -> bool:
        assert type(a) is PatternMatchDomainElement
        return all([self.underlying_domain.is_bottom(b) if b is not None else True for b in a.constraint_per_state])

    def concretize(self, a: IAbstractPattern) -> Kore.Pattern:
        old = time.perf_counter()
        c = self._concretize(a)
        new = time.perf_counter()
        self.concretize_perf_counter.add(new - old)
        return c
    
    def _concretize(self, a: IAbstractPattern) -> Kore.Pattern:
        assert type(a) is PatternMatchDomainElement
        bot : Kore.Pattern = Kore.Bottom(self._top_sort)
        concretized_constraints: T.List[T.List[Kore.Pattern]] = [
            (self.underlying_domain.concretize(b) if b is not None else [bot])
            for b in a.constraint_per_state
        ]

        ccr_conjs = [
            #self.rsd.simplify(
                KoreUtils.make_conjunction(self._top_sort, ccr)
            #)
            for ccr in concretized_constraints
        ]

        #_LOGGER.warning(f'ccr_conjs: {ccr_conjs}')

        # We normalize such that different states in the disjunction have different variables
        constrained_states: T.List[Kore.Pattern] = [
            KoreUtils.normalize_pattern(
                KoreUtils.cleanup_pattern_new(
                    self.rs.simplify(
                        Kore.And(
                            self.rs.sortof(state),
                            state,
                            ccr_conj, #KoreUtils.rename_vars(a.renaming, ccr_conj)
                        )
                    )
                ), prefix=f"Z{i}"
            ) 
            for i,(state,ccr_conj) in enumerate(zip(self.states, ccr_conjs))
        ]
        result = KoreUtils.make_disjunction(self._top_sort, constrained_states)
        #_LOGGER.warning(f'BEFORE= {self.rs.kprint.kore_to_pretty(result)}')
        #.warning(f'BEFORE= {result.text}')

        result = self.rs.simplify(result)
        #_LOGGER.warning(f'AFTER= {self.rs.kprint.kore_to_pretty(result)}')
        return result

    def free_variables_of(self, a: IAbstractPattern) -> T.Set[Kore.EVar]:
        return KoreUtils.free_evars_of_pattern(self.concretize(a))

    def equals(self, a1: IAbstractPattern, a2: IAbstractPattern) -> bool:
        assert type(a1) is PatternMatchDomainElement
        assert type(a2) is PatternMatchDomainElement
        return all([
            (self.underlying_domain.equals(b1, b2) if (b1 is not None and b2 is not None) else ((b1 is None) == (b2 is None)))
            for b1,b2 in zip(a1.constraint_per_state, a2.constraint_per_state)
        ])

    def subsumes(self, a1: IAbstractPattern, a2: IAbstractPattern) -> bool:
        assert type(a1) is PatternMatchDomainElement
        assert type(a2) is PatternMatchDomainElement
        return all([
            (self.underlying_domain.subsumes(b1, b2) if (b1 is not None and b2 is not None) else ((b1 is None) >= (b2 is None)))
            for b1,b2 in zip(a1.constraint_per_state, a2.constraint_per_state)
        ])

    def to_str(self, a: IAbstractPattern, indent: int) -> str:
        assert type(a) is PatternMatchDomainElement
        s: str = (indent*' ') + "pmd[\n"
        for i,b in enumerate(a.constraint_per_state):
            if b is None:
                continue
            if self.underlying_domain.is_bottom(b):
                continue
            s = s + (indent+1)*' ' + f'{i} ({self.comments[self.states[i]]}) => \n'
            s = s + f'{self.underlying_domain.to_str(b, indent=indent+2)}\n'
        s = s + (indent*' ') + "]"
        return s

    def statistics(self) -> T.Dict[str, T.Any]:
        return {
            'abstract' : self.abstract_perf_counter.dict,
            'concretize' : self.concretize_perf_counter.dict,
            'underlying' : [self.underlying_domain.statistics()]
        }