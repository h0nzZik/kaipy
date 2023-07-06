import typing as T
from pathlib import Path
import pytest

from pyk.testing._kompiler import KompiledTest
import pyk.kore.syntax as Kore
import pyk.kore.rpc as KoreRpc
from pyk.ktool.kprint import KPrint

from kaipy.KompiledDefinitionWrapper import KompiledDefinitionWrapper
from kaipy.ReachabilitySystem import ReachabilitySystem

LANGUAGES: T.Final = (Path(__file__).parent / "languages").resolve(strict=True)


class MyTest(KompiledTest):
    @pytest.fixture
    def kompiled_definition_wrapper(
        self, definition_dir: Path
    ) -> KompiledDefinitionWrapper:
        return KompiledDefinitionWrapper.load_from_dir(definition_dir)

    @pytest.fixture
    def reachability_system(self, kompiled_definition_wrapper: KompiledDefinitionWrapper) -> ReachabilitySystem:
        return ReachabilitySystem(kdw=kompiled_definition_wrapper)

class TestImp(MyTest):
    KOMPILE_MAIN_FILE = LANGUAGES / "imp/imp.k"
    KOMPILE_BACKEND = "haskell"

    def test_hello(self, kompiled_definition_wrapper: KompiledDefinitionWrapper):
        print(kompiled_definition_wrapper.main_module_name)
        assert True

    def test_heatonly(self, reachability_system: ReachabilitySystem):
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
            execute_result = rs_heatonly.kcs.client.execute(input_pattern, max_depth=None)
            assert(execute_result.reason == KoreRpc.StopReason.STUCK)
            #print(execute_result.state.kore.text)
            print(rs_heatonly.kprint.kore_to_pretty(execute_result.state.kore))

        assert False
