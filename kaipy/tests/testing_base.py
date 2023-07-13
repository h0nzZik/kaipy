import typing as T
from pathlib import Path
import pytest

from pyk.testing._kompiler import KompiledTest

from kaipy.KompiledDefinitionWrapper import KompiledDefinitionWrapper
from kaipy.ReachabilitySystem import ReachabilitySystem

class RSTestBase(KompiledTest):
    LANGUAGES: T.Final = (Path(__file__).parent / "languages").resolve(strict=True)
    
    @pytest.fixture
    def kompiled_definition_wrapper(
        self, definition_dir: Path
    ) -> KompiledDefinitionWrapper:
        return KompiledDefinitionWrapper.load_from_dir(definition_dir)

    @pytest.fixture
    def reachability_system(
        self, kompiled_definition_wrapper: KompiledDefinitionWrapper
    ) -> T.Iterator[ReachabilitySystem]:
        with ReachabilitySystem(kdw=kompiled_definition_wrapper) as rs:
            yield rs