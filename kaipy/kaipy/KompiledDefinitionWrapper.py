import typing as T
from dataclasses import dataclass
from pathlib import Path

import pyk.kore.syntax as Kore
from pyk.kore.kompiled import KompiledKore

RuleID: T.TypeAlias = int


@T.final
@dataclass(frozen=True)
class KompiledDefinitionWrapper:
    kompiled_kore: KompiledKore

    def __init__(self, definition_dir: str | Path):
        kompiled_kore = KompiledKore(definition_dir)
        object.__setattr__(self, "kompiled_kore", kompiled_kore)

    @property
    def rule_ids(self) -> T.Set[RuleID]:
        return set()  # TODO implement

    def get_rule(self, ruleid: RuleID) -> Kore.Axiom:
        raise NotImplementedError("Not implemented yet")

    @property
    def top_sort(self) -> Kore.Sort:
        raise NotImplementedError("Not implemented yet")
