import typing as T
from pathlib import Path

import pyk.kore.prelude as KorePrelude
import pyk.kore.rpc as KoreRpc
import pyk.kore.syntax as Kore
import pytest
from pyk.kore.parser import KoreParser
from pyk.ktool.kprint import KPrint
from pyk.testing._kompiler import KompiledTest

import kaipy.rs_utils as RSUtils
from kaipy.HeatPreAnalysis import ContextAlias, ContextAliases, collect_rests
from kaipy.KompiledDefinitionWrapper import KompiledDefinitionWrapper
from kaipy.ReachabilitySystem import ReachabilitySystem

LANGUAGES: T.Final = (Path(__file__).parent / "languages").resolve(strict=True)


class ToyTestBase(KompiledTest):
    @pytest.fixture
    def kompiled_definition_wrapper(
        self, definition_dir: Path
    ) -> KompiledDefinitionWrapper:
        return KompiledDefinitionWrapper.load_from_dir(definition_dir)

    @pytest.fixture
    def reachability_system(
        self, kompiled_definition_wrapper: KompiledDefinitionWrapper
    ) -> ReachabilitySystem:
        return ReachabilitySystem(kdw=kompiled_definition_wrapper)


class TestToy(ToyTestBase):
    KOMPILE_MAIN_FILE = LANGUAGES / "toy/toy.k"
    KOMPILE_BACKEND = "haskell"

    def test_toy_exec(self, reachability_system: ReachabilitySystem):
        rs = reachability_system
        p: Kore.Pattern = Kore.App(
            "Lbl'-LT-'generatedTop'-GT-'",
            (),
            (
                Kore.App(
                    "Lbl'-LT-'k'-GT-'",
                    (),
                    (
                        KorePrelude.kseq([
                            Kore.EVar('VARX', KorePrelude.SORT_K_ITEM),
                            Kore.App(
                                "Lbl'Hash'freezerfoo'LParUndsRParUnds'TOY-SYNTAX'Unds'Stmt'Unds'AExp0'Unds'"
                            )
                        ]),
                    )
                ),
                Kore.EVar("VARGENERATEDCOUNTER", Kore.SortApp('SortGeneratedCounterCell'))
            ),
        )
        er = rs.kcs.client.execute(p, max_depth=1)
        print(f"er: {er.reason}")
        print(f"new term: {rs.kprint.kore_to_pretty(er.state.kore)}")
        assert False
