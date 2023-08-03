import contextlib
import functools as F
import shutil

# import os
import tempfile
import typing as T
from dataclasses import dataclass
from pathlib import Path

import pyk.kore.syntax as Kore
from pyk.kore.kompiled import KompiledKore

from .IManagedKompiledKore import IManagedKompiledKore


class TmpKompiledKore(IManagedKompiledKore):
    _tmp_directory: tempfile.TemporaryDirectory
    _kompiled_kore: KompiledKore

    definition_dir: Path

    def __init__(self, definition: Kore.Definition, old_dir: Path):
        self._tmp_directory = tempfile.TemporaryDirectory()
        self.definition_dir = Path(self._tmp_directory.name)
        (self.definition_dir / "timestamp").touch()
        with open((self.definition_dir / "definition.kore"), mode="w") as fw:
            fw.write(definition.text)
        self._kompiled_kore = KompiledKore(self._tmp_directory.name)

        def cp(filename: str):
            shutil.copy(src=old_dir / filename, dst=self.definition_dir / filename)

        cp("mainModule.txt")
        cp("mainSyntaxModule.txt")
        cp("scanner")
        cp("syntaxDefinition.kore")
        cp("configVars.sh")
        cp("compiled.bin")
        cp("macros.kore")
        cp("backend.txt")

        # TODO DEBUG ONLY
        # shutil.copy(src=self.definition_dir / "definition.kore", dst=os.path.expanduser("~/mydefinition.kore"))

    def __enter__(self):
        return self

    def __exit__(self, *args: T.Any) -> None:
        self._tmp_directory.__exit__(*args)

    @property
    def kompiled_kore(self) -> KompiledKore:
        return self._kompiled_kore
