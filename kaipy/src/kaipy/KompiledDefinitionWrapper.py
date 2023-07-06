import typing as T
import functools as F
from dataclasses import dataclass
from pathlib import Path

import pyk.kore.syntax as Kore
from pyk.kore.kompiled import KompiledKore

from .kore_utils import (
    #axiom_label,
    #free_evars_of_pattern,
    #get_symbol_sort,
    #get_top_cell_initializer,
    #is_nonhooked_constructor_symbol,
    rewrite_axioms,
)

RuleID: T.TypeAlias = int


@T.final
@dataclass(frozen=True)
class KompiledDefinitionWrapper:
    kompiled_kore: KompiledKore
    main_module_name: str

    def __init__(self, definition_dir: Path):
        kompiled_kore = KompiledKore(definition_dir)
        with open(definition_dir / "mainModule.txt", "r") as mm:
            main_module_name = mm.read()
        object.__setattr__(self, "main_module_name", main_module_name)
        object.__setattr__(self, "kompiled_kore", kompiled_kore)

    @property
    def rule_ids(self) -> T.Set[RuleID]:
        return set()  # TODO implement

    def get_rule(self, ruleid: RuleID) -> Kore.Axiom:
        raise NotImplementedError("Not implemented yet")

    @property
    def top_sort(self) -> Kore.Sort:
        raise NotImplementedError("Not implemented yet")


    @F.cached_property
    def rewrite_rules(self) -> T.List[Kore.Axiom]:
        return list(rewrite_axioms(self.kompiled_kore.definition, self.main_module_name))