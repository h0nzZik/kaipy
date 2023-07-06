from pathlib import Path
import pytest
import typing as T

from pyk.testing._kompiler import KompiledTest

import kaipy
from kaipy.KompiledDefinitionWrapper import KompiledDefinitionWrapper

LANGUAGES: T.Final = (Path(__file__).parent / 'languages').resolve(strict=True)

class MyTest(KompiledTest):
    @pytest.fixture
    def kompiled_definition_wrapper(self, definition_dir: Path) -> KompiledDefinitionWrapper:
        return KompiledDefinitionWrapper(definition_dir)

class TestImp(MyTest):
    KOMPILE_MAIN_FILE = LANGUAGES / 'imp/imp.k'
    KOMPILE_BACKEND = 'haskell'

    def test_hello(self, kompiled_definition_wrapper: KompiledDefinitionWrapper):
        print(kompiled_definition_wrapper.main_module_name)
        assert(True)