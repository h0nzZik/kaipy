import functools as F
import typing as T
from dataclasses import dataclass
from pathlib import Path

import pyk.kore.syntax as Kore
from pyk.kore.kompiled import KompiledKore
from pyk.kore.parser import KoreParser
from pyk.ktool import krun

#import kaipy.kcommands as kcommands

import kaipy.kore_utils as KoreUtils
from .HeatonlyDefinition import heat_cool_only_definition
from .IManagedKompiledKore import IManagedKompiledKore
from .TmpKompiledKore import TmpKompiledKore
from .TriviallyManagedKompiledKore import TriviallyManagedKompiledKore

RuleID: T.TypeAlias = int


@T.final
@dataclass(frozen=True)
class KompiledDefinitionWrapper:
    managed_kompiled_kore: IManagedKompiledKore
    main_module_name: str
    _definition_dir: Path

    def __init__(
        self,
        managed_kompiled_kore: IManagedKompiledKore,
        main_module_name: str,
        definition_dir: Path,
    ):
        object.__setattr__(self, "main_module_name", main_module_name)
        object.__setattr__(self, "managed_kompiled_kore", managed_kompiled_kore)
        object.__setattr__(self, "_definition_dir", definition_dir)

    @property
    def definition_dir(self) -> Path:
        return self._definition_dir

    @classmethod
    def load_from_dir(cls, definition_dir: Path):
        kompiled_kore = KompiledKore(definition_dir)
        with open(definition_dir / "mainModule.txt", "r") as mm:
            main_module_name = mm.read()
        return KompiledDefinitionWrapper(
            TriviallyManagedKompiledKore(kompiled_kore),
            main_module_name,
            definition_dir=definition_dir,
        )

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
    def declared_sorts(self) -> T.List[str]:
        sort_decls = KoreUtils.sort_decls(self.kompiled_kore.definition, self.main_module_name)
        return [sd.name for sd in sort_decls]


    @F.cached_property
    def user_declared_sorts(self) -> T.List[str]:
        blacklist = [
            'SortIds',
            'SortIOInt',
            'SortIOFile',
            'SortList',
            'SortFloat',
            'SortMap',
            'SortString',
            'SortIOString',
            'SortId',
            'SortKConfigVar',
            'SortInt',
            'SortIOError',
            'SortSet',
            'SortKResult',
            'SortStream',
            'SortBool',
            'SortK',
#            'SortKItem',
        ]
        return [
            sn
            for sn in self.declared_sorts
            if not (
                sn.endswith('CellFragment') or
                sn.endswith('CellOpt') or
                sn.endswith('Cell') or
                sn in blacklist
                )
        ]


    @F.cached_property
    def rewrite_rules(self) -> T.List[Kore.Axiom]:
        return list(
            KoreUtils.rewrite_axioms(self.kompiled_kore.definition, self.main_module_name)
        )

    @F.cached_property
    def rules_variables(self) -> T.Set[Kore.EVar]:
        evars: T.Set[Kore.EVar] = set()
        for axiom in self.rewrite_rules:
            evars = evars.union(KoreUtils.free_evars_of_pattern(axiom.pattern))
        return evars

    def get_input_kore(self, program: Path) -> Kore.Pattern:
        # we have to invent a name which does not occur among variables of the semantic rules
        n: int = 0
        names = [v.name for v in self.rules_variables]
        while ("VarARGS" + str(n)) in names:
            n = n + 1

        args_name = "VarARGS" + str(n)
        #print(f"args_name: {args_name}")

        result = krun._krun(
            #command=(kcommands.KRUN_COMMAND),
            input_file=Path(program),
            definition_dir=self.definition_dir,
            output=krun.KRunOutput.KORE,
            depth=0,
            cmap={"ARGS": (args_name + r":SortList{}")},
            pmap={"ARGS": "cat"},
        )
        result.check_returncode()
        parser = KoreParser(result.stdout)
        res = parser.pattern()
        assert parser.eof
        return res

    @F.cached_property
    def heat_cool_only(self):
        new_definition = heat_cool_only_definition(self.kompiled_kore.definition)
        tmp_kompiled_kore = TmpKompiledKore(
            definition=new_definition,
            old_dir=self.definition_dir,
        )
        return KompiledDefinitionWrapper(
            tmp_kompiled_kore,
            main_module_name=self.main_module_name,
            definition_dir=tmp_kompiled_kore.definition_dir,
        )

    def sortof(self, p: Kore.Pattern) -> Kore.Sort:
        match p:
            case Kore.App('inj', (srcsort,dstsort), _):
                return dstsort
            case Kore.App(sym, _, _):
                return KoreUtils.get_symbol_sort(self.kompiled_kore.definition, self.main_module_name, sym)

        return p.sort # type: ignore