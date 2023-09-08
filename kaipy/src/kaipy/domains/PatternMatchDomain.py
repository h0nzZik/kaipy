import abc
import collections
import dataclasses
import typing as T
import logging

import pyk.kore.syntax as Kore

import kaipy.kore_utils as KoreUtils
import kaipy.rs_utils as RSUtils
from kaipy.VariableManager import VariableManager
from kaipy.AbstractionContext import AbstractionContext
from kaipy.ReachabilitySystem import ReachabilitySystem
from kaipy.interfaces.IAbstractConstraintDomainBuilder import IAbstractConstraintDomainBuilder
from kaipy.interfaces.IAbstractConstraintDomain import IAbstractConstraint, IAbstractConstraintDomain
from kaipy.interfaces.IAbstractPatternDomain import IAbstractPattern, IAbstractPatternDomain
from kaipy.ParallelMatcher import parallel_match, MatchResult

_LOGGER: T.Final = logging.getLogger(__name__)

@dataclasses.dataclass
class PatternMatchDomainElement(IAbstractPattern):
    constraint_per_state: T.List[IAbstractConstraint|None] # The None is here because not every abstract domain can effectively abstract Bottom

class PatternMatchDomain(IAbstractPatternDomain):
    rs: ReachabilitySystem
    states: T.List[Kore.Pattern]
    comments: T.Mapping[Kore.Pattern, str]
    underlying_domains: T.List[IAbstractConstraintDomain]
    # invariant: len(states) == len(underlying_domains)

    # maybe?
    # precondition: `states` must cover all possible configurations; that is, a big disjunction over `states` is Top.
    def __init__(self,
        rs: ReachabilitySystem,
        states: T.List[T.Tuple[Kore.Pattern, str]],
        underlying_domain_builder: IAbstractConstraintDomainBuilder
    ):
        self.rs = rs
        self.states = [x for (x, y) in states]
        self.comments = {x:y for (x,y) in states}
        #_LOGGER.warning(f"States: {len(states)}")
        self.underlying_domains = [
            underlying_domain_builder.build_abstract_constraint_domain(KoreUtils.free_evars_of_pattern(st))
            for st in self.states
        ]

    def abstract(self, ctx: AbstractionContext, c: Kore.Pattern) -> PatternMatchDomainElement:
        cpsl: T.List[T.List[IAbstractConstraint|None]] = list()
        for q0 in KoreUtils.or_to_list(self.rs.simplify(c)):
            q = KoreUtils.normalize_pattern(q0)
            #q = q0
            # Suppose states=[foo(A)] and c=foo(bar(A)). 
            mrs: T.List[MatchResult] = parallel_match(rs=self.rs, cfg=q, states=self.states)
            constraintss: T.List[T.List[Kore.MLPred]] = [
                mr.constraints # type: ignore
                for mr in mrs
            ]
            cps: T.List[IAbstractConstraint|None] = list()

            for i,constraints in enumerate(constraintss):
                if KoreUtils.any_is_bottom(constraints):
                    #_LOGGER.warning(f"Skipping bottom at {i}")
                    cps.append(None)
                    continue
                ctx.broadcast_channel.reset()
                d = self.underlying_domains[i]
                a1 = d.abstract(
                    ctx=ctx,
                    c=constraints,
                )
                if len(ctx.broadcast_channel.constraints) == 0:
                    cps.append(a1)
                else:
                    a2: IAbstractConstraint = d.refine(ctx=ctx, a=a1, c=ctx.broadcast_channel.constraints)
                    ctx.broadcast_channel.reset()
                    cps.append(a2)
            cpsl.append(cps)
        
        # Now compute all the disjunctions
        final_cps: T.List[IAbstractConstraint|None] = [None for _ in self.underlying_domains]
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
                final_cps[i] = self.underlying_domains[i].disjunction(ctx, fci, cci)
        return PatternMatchDomainElement(constraint_per_state=final_cps)

    def refine(self, ctx: AbstractionContext, a: IAbstractPattern, c: Kore.Pattern) -> PatternMatchDomainElement:
        assert type(a) is PatternMatchDomainElement
        # no-op so far
        return a

    def disjunction(self, ctx: AbstractionContext, a1: IAbstractPattern, a2: IAbstractPattern) -> IAbstractPattern:
        assert type(a1) is PatternMatchDomainElement
        assert type(a2) is PatternMatchDomainElement
        cps = [ 
            ud.disjunction(ctx, b1, b2) if (b1 is not None and b2 is not None) else (b1 if b2 is None else b2)
            for ud,b1,b2 in zip(self.underlying_domains, a1.constraint_per_state,a2.constraint_per_state)
        ]
        return PatternMatchDomainElement(
            constraint_per_state=cps,
        )

    def is_top(self, a: IAbstractPattern) -> bool:
        assert type(a) is PatternMatchDomainElement
        return all([ud.is_top(b) if b is not None else False for ud,b in zip(self.underlying_domains, a.constraint_per_state)])

    def is_bottom(self, a: IAbstractPattern) -> bool:
        assert type(a) is PatternMatchDomainElement
        return all([ud.is_bottom(b) if b is not None else True for ud,b in zip(self.underlying_domains, a.constraint_per_state)])

    def concretize(self, a: IAbstractPattern) -> Kore.Pattern:
        assert type(a) is PatternMatchDomainElement
        bot : Kore.MLPred = Kore.Bottom(self.rs.top_sort) # type: ignore
        concretized_constraints: T.List[T.List[Kore.MLPred]] = [
            (ud.concretize(b) if b is not None else [bot])
            for ud,b in zip(self.underlying_domains, a.constraint_per_state)
        ]

        ccr_conjs = [
            self.rs.simplify(RSUtils.make_conjunction(self.rs, ccr))
            for ccr in concretized_constraints
        ]

        #_LOGGER.warning(f'ccr_conjs: {ccr_conjs}')

        # We normalize such that different states in the disjunction have different variables
        constrained_states: T.List[Kore.Pattern] = [
            # The simplification here is mainly for debugging purposes
            KoreUtils.normalize_pattern(RSUtils.cleanup_pattern(self.rs, self.rs.simplify(Kore.And(self.rs.sortof(state), state, ccr_conj))), prefix=f"Z{i}") 
            for i,(state,ccr_conj) in enumerate(zip(self.states, ccr_conjs))
        ]
        result = RSUtils.make_disjunction(self.rs, constrained_states)
        #_LOGGER.warning(f'BEFORE= {self.rs.kprint.kore_to_pretty(result)}')
        #.warning(f'BEFORE= {result.text}')

        result = self.rs.simplify(result)
        #_LOGGER.warning(f'AFTER= {self.rs.kprint.kore_to_pretty(result)}')
        return result

    def equals(self, a1: IAbstractPattern, a2: IAbstractPattern) -> bool:
        assert type(a1) is PatternMatchDomainElement
        assert type(a2) is PatternMatchDomainElement
        return all([
            (ud.equals(b1, b2) if (b1 is not None and b2 is not None) else ((b1 is None) == (b2 is None)))
            for ud,b1,b2 in zip(self.underlying_domains, a1.constraint_per_state, a2.constraint_per_state)
        ])

    def subsumes(self, a1: IAbstractPattern, a2: IAbstractPattern) -> bool:
        assert type(a1) is PatternMatchDomainElement
        assert type(a2) is PatternMatchDomainElement
        return all([
            (ud.subsumes(b1, b2) if (b1 is not None and b2 is not None) else ((b1 is None) >= (b2 is None)))
            for ud,b1,b2 in zip(self.underlying_domains, a1.constraint_per_state, a2.constraint_per_state)
        ])

    def to_str(self, a: IAbstractPattern, indent: int) -> str:
        assert type(a) is PatternMatchDomainElement
        s: str = (indent*' ') + "pmd[\n"
        for i,(ud,b) in enumerate(zip(self.underlying_domains, a.constraint_per_state)):
            if b is None:
                continue
            if ud.is_bottom(b):
                continue
            s = s + (indent+1)*' ' + f'{i} ({self.comments[self.states[i]]}) => \n'
            s = s + f'{ud.to_str(b, indent=indent+2)}\n'
        s = s + (indent*' ') + "]"
        return s