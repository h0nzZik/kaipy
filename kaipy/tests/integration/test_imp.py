import typing as T
from pathlib import Path

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
        return ContextAliases((ContextAlias(before,after),))


class TestImp(MyTest):
    KOMPILE_MAIN_FILE = LANGUAGES / "imp/imp.k"
    KOMPILE_BACKEND = "haskell"
    MYTEST_CONTEXT_ALIAS_BEFORE = LANGUAGES / "imp/context_alias_before.kore"
    MYTEST_CONTEXT_ALIAS_AFTER = LANGUAGES / "imp/context_alias_after.kore"

    def test_hello(self, kompiled_definition_wrapper: KompiledDefinitionWrapper):
        print(kompiled_definition_wrapper.main_module_name)
        assert True

    def test_heatonly(
        self, reachability_system: ReachabilitySystem, context_aliases: ContextAliases
    ):
        # print(f"CA: {context_alias.text}")
        heat_only_def: KompiledDefinitionWrapper = reachability_system.kdw.heat_only
        # We assume that Imp has some non-heat rules in the main module
        assert len(heat_only_def.rewrite_rules) < len(
            reachability_system.kdw.rewrite_rules
        )
        input_pattern: Kore.Pattern = heat_only_def.get_input_kore(
            LANGUAGES / "imp/sum.imp"
        )

        with ReachabilitySystem(heat_only_def) as rs_heatonly:
            input_simplified = rs_heatonly.simplify(input_pattern)
            mapping = RSUtils.match_ca(rs_heatonly, context_aliases.aliases[0].before, input_simplified)
            initial_here = mapping[Kore.EVar(name="VARHERE", sort=Kore.SortApp(name="SortKItem"))]
            collected = collect_rests(rs_heatonly, context_aliases.aliases[0], initial_here)
            
            # print(input_simplified.text)
            # print(rs_heatonly.kprint.kore_to_pretty(input_simplified))
            # # This will stop because we have only heating rules in the semantics
            # execute_result = rs_heatonly.kcs.client.execute(input_pattern, max_depth=50)
            # assert execute_result.reason == KoreRpc.StopReason.STUCK
            # last = execute_result.state.kore
            # # print(execute_result.state.kore.text)
            # print(rs_heatonly.kprint.kore_to_pretty(last))
            # mapping = RSUtils.match_ca(rs_heatonly, context_aliases.aliases[0][0], last)
            # print(
            #     mapping[Kore.EVar(name="VARHERE", sort=Kore.SortApp(name="SortKItem"))]
            # )

        assert False
