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


class MyTest(KompiledTest):
    MYTEST_CONTEXT_ALIAS_BEFORE: T.ClassVar[Path]
    MYTEST_CONTEXT_ALIAS_AFTER: T.ClassVar[Path]

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

    def _pattern_from_file(self, filename: Path) -> Kore.Pattern:
        with open(filename, mode="r") as fr:
            text = fr.read()
        parser = KoreParser(text)
        return parser.pattern()

    @pytest.fixture
    def context_aliases(self) -> ContextAliases:
        before = self._pattern_from_file(self.MYTEST_CONTEXT_ALIAS_BEFORE)
        after = self._pattern_from_file(self.MYTEST_CONTEXT_ALIAS_AFTER)
        return ContextAliases((ContextAlias(before, after),))


class TestImp(MyTest):
    KOMPILE_MAIN_FILE = LANGUAGES / "imp/imp.k"
    KOMPILE_BACKEND = "haskell"
    MYTEST_CONTEXT_ALIAS_BEFORE = LANGUAGES / "imp/context_alias_before.kore"
    MYTEST_CONTEXT_ALIAS_AFTER = LANGUAGES / "imp/context_alias_after.kore"

    def test_hello(self, kompiled_definition_wrapper: KompiledDefinitionWrapper):
        print(kompiled_definition_wrapper.main_module_name)
        assert True

    def test_heatcoolonly(
        self, reachability_system: ReachabilitySystem, context_aliases: ContextAliases
    ):
        heat_cool_only_def: KompiledDefinitionWrapper = (
            reachability_system.kdw.heat_cool_only
        )
        # We check that Imp has some non-heat or non-cool rules in the main module
        assert len(heat_cool_only_def.rewrite_rules) < len(
            reachability_system.kdw.rewrite_rules
        )
        input_pattern: Kore.Pattern = heat_cool_only_def.get_input_kore(
            LANGUAGES / "imp/sum.imp"
        )

        with ReachabilitySystem(heat_cool_only_def) as rs_heatcoolonly:
            input_simplified = rs_heatcoolonly.simplify(input_pattern)
            mapping = RSUtils.match_ca(
                rs_heatcoolonly, context_aliases.aliases[0].before, input_simplified
            )
            initial_here = mapping[
                Kore.EVar(name="VARHERE", sort=Kore.SortApp(name="SortKItem"))
            ]
            collected = collect_rests(
                rs_heatcoolonly, context_aliases.aliases[0], initial_here
            )

        assert False

    def test_simplify_kresult_kitem(self, reachability_system: ReachabilitySystem):
        x = Kore.EVar("VARX", KorePrelude.SORT_K_ITEM)
        x_k = KorePrelude.inj(KorePrelude.SORT_K_ITEM, KorePrelude.SORT_K, x)
        input_pattern = Kore.And(
            KorePrelude.SORT_K_ITEM,
            x,
            Kore.Equals(
                KorePrelude.BOOL,
                KorePrelude.SORT_K_ITEM,
                KorePrelude.TRUE,
                Kore.App("LblisKResult", (), (x_k,)),
            ),
        )
        # input_pattern = Kore.And(KorePrelude.SORT_K_ITEM, input_pattern, Kore.Equals(KorePrelude.SORT_K_ITEM, KorePrelude.SORT_K_ITEM, x, KorePrelude.inj(KorePrelude.INT, KorePrelude.SORT_K_ITEM, KorePrelude.int_dv(3))))
        print(
            f"input_pattern: {reachability_system.kprint.kore_to_pretty(input_pattern)}"
        )
        simp = reachability_system.kcs.client.simplify(input_pattern)[0]
        print(f"simplified: {reachability_system.kprint.kore_to_pretty(simp)}")
        assert False

    def test_simplify_kresult_3(self, reachability_system: ReachabilitySystem):
        krterm = Kore.App(
            "LblisKResult",
            (),
            (
                KorePrelude.inj(
                    KorePrelude.INT, KorePrelude.SORT_K, KorePrelude.int_dv(3)
                ),
            ),
        )

        print(
            f"krterm: {reachability_system.kprint.kore_to_pretty(krterm)}"
        )
        simp = reachability_system.kcs.client.simplify(krterm)[0]
        print(f"simplified: {reachability_system.kprint.kore_to_pretty(simp)}")

        input_pattern = Kore.Equals(
            KorePrelude.BOOL,
            KorePrelude.SORT_K_ITEM,
            KorePrelude.TRUE,
            krterm,
        )
        print(
            f"input_pattern: {reachability_system.kprint.kore_to_pretty(input_pattern)}"
        )
        simp = reachability_system.kcs.client.simplify(input_pattern)[0]
        print(f"simplified: {reachability_system.kprint.kore_to_pretty(simp)}")
        assert False
