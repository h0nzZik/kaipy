import abc
import dataclasses
import typing as T

import pyk.kore.syntax as Kore

@dataclasses.dataclass
class IsTrue:
    pattern: Kore.Pattern # of sort SortBool