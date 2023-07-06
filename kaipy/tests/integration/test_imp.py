import typing as T
from pathlib import Path
import pytest

from pyk.testing._kompiler import KompiledTest
import pyk.kore.syntax as Kore
import pyk.kore.rpc as KoreRpc
from pyk.ktool.kprint import KPrint
from pyk.kore.parser import KoreParser

import kaipy.rs_utils as RSUtils
from kaipy.KompiledDefinitionWrapper import KompiledDefinitionWrapper
from kaipy.ReachabilitySystem import ReachabilitySystem

LANGUAGES: T.Final = (Path(__file__).parent / "languages").resolve(strict=True)


class MyTest(KompiledTest):
    MYTEST_CONTEXT_ALIAS: T.ClassVar[str | Path]

    @pytest.fixture
    def kompiled_definition_wrapper(
        self, definition_dir: Path
    ) -> KompiledDefinitionWrapper:
        return KompiledDefinitionWrapper.load_from_dir(definition_dir)

    @pytest.fixture
    def reachability_system(self, kompiled_definition_wrapper: KompiledDefinitionWrapper) -> ReachabilitySystem:
        return ReachabilitySystem(kdw=kompiled_definition_wrapper)

    @pytest.fixture
    def context_alias(self) -> Kore.Pattern:
        with open(self.MYTEST_CONTEXT_ALIAS, mode="r") as fr:
            text = fr.read()
        parser = KoreParser(text)
        return parser.pattern()
        

class TestImp(MyTest):
    KOMPILE_MAIN_FILE = LANGUAGES / "imp/imp.k"
    KOMPILE_BACKEND = "haskell"
    MYTEST_CONTEXT_ALIAS = LANGUAGES / "imp/context_alias.kore"

    def test_hello(self, kompiled_definition_wrapper: KompiledDefinitionWrapper):
        print(kompiled_definition_wrapper.main_module_name)
        assert True

    def test_heatonly(self, reachability_system: ReachabilitySystem, context_alias: Kore.Pattern):
        print(f"CA: {context_alias.text}")
        heat_only_def: KompiledDefinitionWrapper = reachability_system.kdw.heat_only
        # We assume that Imp has some non-heat rules in the main module
        assert len(heat_only_def.rewrite_rules) < len(
            reachability_system.kdw.rewrite_rules
        )
        input_pattern: Kore.Pattern = heat_only_def.get_input_kore(LANGUAGES / "imp/sum.imp")

        with ReachabilitySystem(heat_only_def) as rs_heatonly:
            input_simplified = rs_heatonly.simplify(input_pattern)
            print(input_simplified.text)
            print(rs_heatonly.kprint.kore_to_pretty(input_simplified))
            # This will stop because we have only heating rules in the semantics
            execute_result = rs_heatonly.kcs.client.execute(input_pattern, max_depth=50)
            assert(execute_result.reason == KoreRpc.StopReason.STUCK)
            last = execute_result.state.kore
            #print(execute_result.state.kore.text)
            print(rs_heatonly.kprint.kore_to_pretty(last))
            mapping = RSUtils.match_ca(rs_heatonly, context_alias, last)
            print(mapping[Kore.EVar(name="VARHERE", sort=Kore.SortApp(name="SortKItem"))])

        assert False
