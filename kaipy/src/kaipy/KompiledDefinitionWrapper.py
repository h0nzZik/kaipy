import functools as F
import typing as T
from dataclasses import dataclass
from pathlib import Path

import pyk.kore.syntax as Kore
from pyk.kore.kompiled import KompiledKore
from pyk.kore.parser import KoreParser
from pyk.ktool import krun

import kaipy.kcommands as kcommands

from .kore_utils import (  # axiom_label,; get_symbol_sort,; get_top_cell_initializer,; is_nonhooked_constructor_symbol,
    free_evars_of_pattern,
    rewrite_axioms,
)

from .IManagedKompiledKore import IManagedKompiledKore
from .TriviallyManagedKompiledKore import TriviallyManagedKompiledKore
from .TmpKompiledKore import TmpKompiledKore
from .HeatonlyDefinition import heat_only_definition

RuleID: T.TypeAlias = int


@T.final
@dataclass(frozen=True)
class KompiledDefinitionWrapper:
    managed_kompiled_kore: IManagedKompiledKore
    main_module_name: str

    def __init__(self, managed_kompiled_kore: IManagedKompiledKore, main_module_name: str):
        object.__setattr__(self, "main_module_name", main_module_name)
        object.__setattr__(self, "managed_kompiled_kore", managed_kompiled_kore)

    @classmethod
    def load_from_dir(cls, definition_dir: Path):
        kompiled_kore = KompiledKore(definition_dir)
        with open(definition_dir / "mainModule.txt", "r") as mm:
            main_module_name = mm.read()
        return KompiledDefinitionWrapper(TriviallyManagedKompiledKore(kompiled_kore), main_module_name)

    @property
    def kompiled_kore(self) -> KompiledKore:
        return self.managed_kompiled_kore.kompiled_kore

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
        return list(
            rewrite_axioms(self.kompiled_kore.definition, self.main_module_name)
        )

    @F.cached_property
    def rules_variables(self) -> T.Set[Kore.EVar]:
        evars: T.Set[Kore.EVar] = set()
        for axiom in self.rewrite_rules:
            evars = evars.union(free_evars_of_pattern(axiom.pattern))
        return evars

    def get_input_kore(self, program: Path) -> Kore.Pattern:
        # we have to invent a name which does not occur among variables of the semantic rules
        n: int = 0
        names = [v.name for v in self.rules_variables]
        while ("VarARGS" + str(n)) in names:
            n = n + 1

        args_name = "VarARGS" + str(n)
        print(f"args_name: {args_name}")

        result = krun._krun(
            command=(kcommands.KRUN_COMMAND),
            input_file=Path(program),
            definition_dir=self.kompiled_kore.path,
            output=krun.KRunOutput.KORE,
            depth=0,
            cmap={"ARGS": (args_name + r":SortList{}")},
            pmap={"ARGS": "cat"},
        )
        krun.KRun._check_return_code(result.returncode, 0)
        parser = KoreParser(result.stdout)
        res = parser.pattern()
        assert parser.eof
        return res

    @F.cached_property
    def heat_only(self):
        new_definition = heat_only_definition(self.kompiled_kore.definition)
        tmp_kompiled_kore = TmpKompiledKore(new_definition)
        return KompiledDefinitionWrapper(tmp_kompiled_kore, self.main_module_name)

