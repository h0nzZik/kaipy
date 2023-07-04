import typing as T
from dataclasses import dataclass
import functools

import pyk.kore.syntax as Kore

from .KompiledDefinitionWrapper import KompiledDefinitionWrapper, RuleID
from .IAbstractValue import IAbstractValue


NodeID: T.TypeAlias = int
EdgeID: T.TypeAlias = int

# NodePoint and SplitValue are in this file because they refer to `NodeID`s,
# which make sense only in the context of a PRGraph.
# In other words, SplitValue and PRGraph are tightly coupled


@T.final
@dataclass(frozen=True)
class NodePoint(IAbstractValue):
    constraint: T.Dict[Kore.EVar, Kore.Pattern]
    abstract_value: IAbstractValue
    successors: T.Set[NodeID]

    def constraint_pattern(self, top_sort: Kore.Sort) -> Kore.Pattern:
        eqs = [Kore.Equals(top_sort, e.sort, e, p) for e,p in self.constraint.items()]
        top: Kore.Pattern = Kore.Top(top_sort)
        return functools.reduce(lambda p, eq: Kore.And(top_sort, eq, p), eqs, top)
    
    def pattern(self, top_sort: Kore.Sort) -> Kore.Pattern:
        cp = self.constraint_pattern(top_sort)
        return Kore.And(top_sort, cp, self.abstract_value.pattern(top_sort))


@T.final
@dataclass(frozen=True)
class SplitValue(IAbstractValue):
    parts: T.Tuple[NodePoint,...]

    def pattern(self, top_sort: Kore.Sort) -> Kore.Pattern:
        ps: T.List[Kore.Pattern] = [p.pattern(top_sort) for p in self.parts]
        bot: Kore.Pattern = Kore.Bottom(top_sort)
        return functools.reduce(lambda disj, item: Kore.Or(top_sort, item, disj), ps, bot)

@T.final
@dataclass(frozen=True)
class Node:
    pattern: Kore.Pattern
    ruleID: RuleID

@T.final
@dataclass(frozen=False)
class PRGraph:
    definition: KompiledDefinitionWrapper
    nodes: T.Dict[NodeID, Node]
    edges: T.Set[T.Tuple[NodeID, NodeID]]