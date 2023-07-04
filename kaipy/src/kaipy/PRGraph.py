import functools
import typing as T
from dataclasses import dataclass

import pyk.kore.syntax as Kore

from .IAbstractValue import IAbstractValue
from .KompiledDefinitionWrapper import KompiledDefinitionWrapper, RuleID

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
        eqs = [Kore.Equals(top_sort, e.sort, e, p) for e, p in self.constraint.items()]
        top: Kore.Pattern = Kore.Top(top_sort)
        return functools.reduce(lambda p, eq: Kore.And(top_sort, eq, p), eqs, top)

    def pattern(self, top_sort: Kore.Sort) -> Kore.Pattern:
        cp = self.constraint_pattern(top_sort)
        return Kore.And(top_sort, cp, self.abstract_value.pattern(top_sort))


@T.final
@dataclass(frozen=True)
class SplitValue(IAbstractValue):
    parts: T.Tuple[NodePoint, ...]

    def pattern(self, top_sort: Kore.Sort) -> Kore.Pattern:
        ps: T.List[Kore.Pattern] = [p.pattern(top_sort) for p in self.parts]
        bot: Kore.Pattern = Kore.Bottom(top_sort)
        return functools.reduce(
            lambda disj, item: Kore.Or(top_sort, item, disj), ps, bot
        )


@T.final
@dataclass(frozen=True)
class Node:
    pattern: Kore.Pattern
    ruleid: RuleID
    splits: SplitValue


# Performs one step using the rule with the given RuleID
# TODO: implement.
def step_using(
    definition: KompiledDefinitionWrapper, ruleid: RuleID, pattern: Kore.Pattern
) -> Kore.Pattern:
    return Kore.Top(definition.top_sort)


def simplifies_to_bottom(
    definition: KompiledDefinitionWrapper, pattern: Kore.Pattern
) -> bool:
    raise NotImplementedError("Not implemented yet")


@T.final
@dataclass(frozen=False)
class PRGraph:
    definition: KompiledDefinitionWrapper
    nodes: T.Dict[NodeID, Node]
    edges: T.Set[T.Tuple[NodeID, NodeID]]

    def succ_of(self, nodeid: NodeID) -> T.Set[NodeID]:
        return {tgt for (src, tgt) in self.edges if src == nodeid}

    @property
    def invariant(self) -> bool:
        for nodeid, node in self.nodes.items():
            for np in node.splits.parts:
                if not np.successors <= self.succ_of(nodeid):
                    return False

                for excluded in self.succ_of(nodeid).difference(np.successors):
                    if not simplifies_to_bottom(
                        self.definition,
                        step_using(
                            self.definition,
                            node.ruleid,
                            Kore.And(
                                self.definition.top_sort,
                                node.pattern,
                                np.pattern(self.definition.top_sort),
                            ),
                        ),
                    ):
                        return False
        return True
