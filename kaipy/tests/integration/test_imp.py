import typing as T
from pathlib import Path

import pytest
from pyk.testing._kompiler import KompiledTest

#import kaipy
from kaipy.KompiledDefinitionWrapper import KompiledDefinitionWrapper
from kaipy.HeatonlyDefinition import heat_only_definition

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
        assert True
