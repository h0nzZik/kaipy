import functools as F
import typing as T
import contextlib
from dataclasses import dataclass
from pathlib import Path
import tempfile

import pyk.kore.syntax as Kore
from pyk.kore.kompiled import KompiledKore

from .IManagedKompiledKore import IManagedKompiledKore

class TmpKompiledKore(IManagedKompiledKore):
    _tmp_directory: tempfile.TemporaryDirectory
    _kompiled_kore: KompiledKore

    def __init__(self, definition: Kore.Definition):
        self._tmp_directory = tempfile.TemporaryDirectory()
        (Path(self._tmp_directory.name) / 'timestamp').touch()
        with open((Path(self._tmp_directory.name) / 'definition.kore')) as fw:
            fw.write(definition.text)

        self._kompiled_kore = KompiledKore(self._tmp_directory.name)
    
    def __enter__(self):
        return self

    def __exit__(self, *args: T.Any) -> None:
        self._tmp_directory.__exit__(*args)

    @property
    def kompiled_kore(self) -> KompiledKore:
        return self._kompiled_kore
