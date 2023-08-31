import abc
import collections
import dataclasses
import typing as T

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

@dataclasses.dataclass
class PatternMatchDomainElement(IAbstractPattern):
    constraint_per_state: T.List[IAbstractConstraint]
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
        self.underlying_domains = [
            underlying_domain_builder.build_abstract_constraint_domain(KoreUtils.free_evars_of_pattern(st))
            for st in states
        ]

    def abstract(self, ctx: AbstractionContext,  c: Kore.Pattern) -> PatternMatchDomainElement:
        mrs: T.List[MatchResult] = parallel_match(rs=self.rs, cfg=c, states=self.states)
        # We need to rename all free variables in the result of the paralle match
        # to some globally recognized variables. We need to do that anyway,
        # but one special reason for that is that we want different calls of `abstract`
        # to result in patterns with different variables being fed to the underlying domains.
        # Then, when we concretized two abstract values through an underlying domain,
        # they will have different variables, and therefore we can simply join the two reversed renamings.
        # For example, suppose we have two states, first with variables A, B and second with variable A, again.
        # Then, `parallel_match` will create two renamings: {A: A', B: B'}, and {A: A'}.
        renamings_2: T.List[T.Mapping[str, str]] = [
            { v: ctx.variable_manager.get_fresh_evar_name() for k,v in mr.renaming.items() }
            for mr in mrs
        ]
        # Now, `renamings_2` will be `[{A': SV1, B': SV2}, {A': SV3}]`.
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
        # Now, renamings_composed is `[{A: SV1, B: SV2}, {A: SV3}].`
        # We need to create a way back from these to A and B.
        renamings_reversed = [KoreUtils.reverse_renaming(r) for r in renamings_composed]
        renamings_joined = dict(collections.ChainMap(*renamings_reversed))
        # Now renamings_joined is `{SV1: A, SV2: B, SV3: A}`
        cps: T.List[IAbstractConstraint] = [
            self.underlying_domains[i].abstract(
                ctx=ctx,
                c=constraints,
            )
            for i,constraints in enumerate(constraints_renamed)
        ]
        return PatternMatchDomainElement(constraint_per_state=cps, reversed_renaming=renamings_joined)

    def refine(self, ctx: AbstractionContext, a: IAbstractPattern, c: Kore.Pattern) -> PatternMatchDomainElement:
        assert type(a) is PatternMatchDomainElement
        # no-op so far
        return a

    def disjunction(self, ctx: AbstractionContext, a1: IAbstractPattern, a2: IAbstractPattern) -> IAbstractPattern:
        assert type(a1) is PatternMatchDomainElement
        assert type(a2) is PatternMatchDomainElement
        assert len(set.intersection(set(a1.reversed_renaming.keys()), set(a2.reversed_renaming.keys()))) == 0
        cps = [ 
            ud.disjunction(ctx, b1, b2)
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
        return all([ud.is_top(b) for ud,b in zip(self.underlying_domains, a.constraint_per_state)])

    def is_bottom(self, a: IAbstractPattern) -> bool:
        assert type(a) is PatternMatchDomainElement
        return all([ud.is_bottom(b) for ud,b in zip(self.underlying_domains, a.constraint_per_state)])

    def concretize(self, a: IAbstractPattern) -> Kore.Pattern:
        assert type(a) is PatternMatchDomainElement
        concretized_constraints: T.List[T.List[Kore.MLPred]] = [
            ud.concretize(b)
            for ud,b in zip(self.underlying_domains, a.constraint_per_state)
        ]
        concretized_constraints_renamed = [
            [ KoreUtils.rename_vars(KoreUtils.reverse_renaming(a.reversed_renaming), c) for c in cc]
            for cc in concretized_constraints
        ]
        constrained_states: T.List[Kore.Pattern] = [
            Kore.And(self.rs.sortof(state), state, RSUtils.make_conjunction(self.rs, ccr))
            for state,ccr in zip(self.states, concretized_constraints_renamed)
        ]
        result = RSUtils.make_disjunction(self.rs, constrained_states)
        return result

    def equals(self, a1: IAbstractPattern, a2: IAbstractPattern) -> bool:
        assert type(a1) is PatternMatchDomainElement
        assert type(a2) is PatternMatchDomainElement
        return all([
            ud.equals(b1, b2)
            for ud,b1,b2 in zip(self.underlying_domains, a1.constraint_per_state, a2.constraint_per_state)
        ])

    def subsumes(self, a1: IAbstractPattern, a2: IAbstractPattern) -> bool:
        assert type(a1) is PatternMatchDomainElement
        assert type(a2) is PatternMatchDomainElement
        return all([
            ud.subsumes(b1, b2)
            for ud,b1,b2 in zip(self.underlying_domains, a1.constraint_per_state, a2.constraint_per_state)
        ])

    def to_str(self, a: IAbstractPattern) -> str:
        assert type(a) is PatternMatchDomainElement
        s: str = "pmd["
        for i,(ud,b) in enumerate(zip(self.underlying_domains, a.constraint_per_state)):
            if ud.is_bottom(b):
                continue
            bs = ud.to_str(b)
            s = s + f'{i} => {bs};'
        s = s + "]"
        return s