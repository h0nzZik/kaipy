import contextlib
import functools as F
import tempfile
import typing as T
from dataclasses import dataclass
from pathlib import Path

import pyk.kore.syntax as Kore
from pyk.kore.kompiled import KompiledKore

from .IManagedKompiledKore import IManagedKompiledKore


class TriviallyManagedKompiledKore(IManagedKompiledKore):
    _kompiled_kore: KompiledKore

    def __init__(self, kompiled_kore: KompiledKore):
        self._kompiled_kore = kompiled_kore

    @property
    def kompiled_kore(self) -> KompiledKore:
        return self._kompiled_kore

    def __enter__(self):
        return self

    def __exit__(self, *args: T.Any) -> None:
        return None
