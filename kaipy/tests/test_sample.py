from pathlib import Path

from pyk.testing._kompiler import KompiledTest

import typing as T

def func(x):
    return x + 1


def test_answer():
    assert func(3) == 4
