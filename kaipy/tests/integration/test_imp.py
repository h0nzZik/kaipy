import typing as T
from pathlib import Path

import pytest
from pyk.testing._kompiler import KompiledTest

from kaipy.KompiledDefinitionWrapper import KompiledDefinitionWrapper

LANGUAGES: T.Final = (Path(__file__).parent / "languages").resolve(strict=True)


class MyTest(KompiledTest):
    @pytest.fixture
    def kompiled_definition_wrapper(
        self, definition_dir: Path
    ) -> KompiledDefinitionWrapper:
        return KompiledDefinitionWrapper.load_from_dir(definition_dir)


class TestImp(MyTest):
    KOMPILE_MAIN_FILE = LANGUAGES / "imp/imp.k"
    KOMPILE_BACKEND = "haskell"

    def test_hello(self, kompiled_definition_wrapper: KompiledDefinitionWrapper):
        print(kompiled_definition_wrapper.main_module_name)
        assert True

    def test_heatonly(self, kompiled_definition_wrapper: KompiledDefinitionWrapper):
        heat_only_def: KompiledDefinitionWrapper = kompiled_definition_wrapper.heat_only
        # We assume that Imp has some non-heat rules in the main module
        assert len(heat_only_def.rewrite_rules) < len(
            kompiled_definition_wrapper.rewrite_rules
        )
        assert True
