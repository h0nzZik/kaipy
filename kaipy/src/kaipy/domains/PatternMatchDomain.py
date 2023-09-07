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
    reversed_renaming: T.Mapping[str, str]

class PatternMatchDomain(IAbstractPatternDomain):
    rs: ReachabilitySystem
    states: T.List[Kore.Pattern]
    underlying_domains: T.List[IAbstractConstraintDomain]
    # invariant: len(states) == len(underlying_domains)

    # maybe?
    # precondition: `states` must cover all possible configurations; that is, a big disjunction over `states` is Top.
    def __init__(self,
        rs: ReachabilitySystem,
        states: T.List[Kore.Pattern],
        underlying_domain_builder: IAbstractConstraintDomainBuilder
    ):
        self.rs = rs
        self.states = states
        #_LOGGER.warning(f"States: {len(states)}")
        self.underlying_domains = [
            underlying_domain_builder.build_abstract_constraint_domain(KoreUtils.free_evars_of_pattern(st))
            for st in states
        ]

    def abstract(self, ctx: AbstractionContext, c: Kore.Pattern) -> PatternMatchDomainElement:
        cpsl: T.List[T.List[IAbstractConstraint|None]] = list()
        for q in KoreUtils.or_to_list(self.rs.simplify(c)):
            # Suppose states=[foo(A)] and c=foo(bar(A)). 
            mrs: T.List[MatchResult] = parallel_match(rs=self.rs, cfg=q, states=self.states)
            # We get [{constraints: A = bar(A'), renaming: {A: A'}}]
            # We need to rename all free variables in the `constraints` of the parallel match
            # to some globally recognized variables. We need to do that anyway,
            # but one special reason for that is that we want different calls of `abstract`
            # to result in patterns with different variables being fed to the underlying domains.
            # Then, when we have concretized two abstract values through an underlying domain,
            # they will have different variables, and therefore we can simply join the two reversed renamings.
            renamings_2: T.List[T.Mapping[str, str]] = [
                { v: ctx.variable_manager.get_fresh_evar_name() for k,v in mr.renaming.items() }
                for mr in mrs
            ]

            # Well, I am only measuring the length of the list of bools here
            #_LOGGER.warning(f"bottoms: {len([KoreUtils.any_is_bottom(mr.constraints) for mr in mrs])}")

            # Now, `renamings_2` will be [{A': SV1}]
            constraints_renamed: T.List[T.List[Kore.MLPred]] = [
                [ KoreUtils.rename_vars(r2, c) for c in mr.constraints ] # type: ignore
                for mr,r2 in zip(mrs, renamings_2)
            ]
            # Now, constraints_renamed will refer to SV1, SV2 and SV3.
            # We need to create a renaming that does both the old and new renamings in one step.
            renamings_composed: T.List[T.Mapping[str, str]] = [
                { k:r2[v] for k,v in mr.renaming.items()}
                for mr,r2 in zip(mrs, renamings_2)
            ]
            # Now, renamings_composed is `[{A: SV1}].`
            # We need to create a way back SV1 to A.
            renamings_reversed = [KoreUtils.reverse_renaming(r) for r in renamings_composed]
            # TODO we should assert that ChainMap didn't lose / shadow anything.
            renamings_joined = dict(collections.ChainMap(*renamings_reversed))
            # Now renamings_joined is `{SV1: A}`
            cps: T.List[IAbstractConstraint|None] = list()

            for i,constraints in enumerate(constraints_renamed):
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
        return PatternMatchDomainElement(constraint_per_state=final_cps, reversed_renaming=renamings_joined)

    def refine(self, ctx: AbstractionContext, a: IAbstractPattern, c: Kore.Pattern) -> PatternMatchDomainElement:
        assert type(a) is PatternMatchDomainElement
        # no-op so far
        return a

    def disjunction(self, ctx: AbstractionContext, a1: IAbstractPattern, a2: IAbstractPattern) -> IAbstractPattern:
        assert type(a1) is PatternMatchDomainElement
        assert type(a2) is PatternMatchDomainElement
        #if self.equals(a1, a2):
        #    return a1
        assert len(set.intersection(set(a1.reversed_renaming.keys()), set(a2.reversed_renaming.keys()))) == 0
        cps = [ 
            ud.disjunction(ctx, b1, b2) if (b1 is not None and b2 is not None) else (b1 if b2 is None else b2)
            for ud,b1,b2 in zip(self.underlying_domains, a1.constraint_per_state,a2.constraint_per_state)
        ]
        rr = dict(a1.reversed_renaming)
        rr.update(a2.reversed_renaming)
        return PatternMatchDomainElement(
            constraint_per_state=cps,
            reversed_renaming=rr
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
        #_LOGGER.warning(f'concretized_constraitns: {[[y.text for y in x] for x in concretized_constraints]}')
        concretized_constraints_renamed = [
            [ KoreUtils.rename_vars(dict(a.reversed_renaming), c) for c in cc]
            for cc in concretized_constraints
        ]
        ccr_conjs = [
            self.rs.simplify(RSUtils.make_conjunction(self.rs, ccr))
            for ccr in concretized_constraints_renamed
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
        s: str = indent*' ' + "pmd[\n"
        for i,(ud,b) in enumerate(zip(self.underlying_domains, a.constraint_per_state)):
            if b is None:
                continue
            if ud.is_bottom(b):
                continue
            bs = ud.to_str(b, indent=indent+1)
            s = s + f'{i} => \n{bs}\n'
        s = s + "]"
        return s