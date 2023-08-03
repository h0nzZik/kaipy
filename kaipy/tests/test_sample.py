import typing as T
from pathlib import Path

from pyk.testing._kompiler import KompiledTest


def func(x):
    return x + 1


def test_answer():
    assert func(3) == 4
