import dataclasses
import typing as T

import pyk.kore.syntax as Kore
import pyk.kore.prelude as KorePrelude

from kaipy.IsTrue import IsTrue

class Property:
    is_negated: bool

    def __init__(self):
        self.is_negated = False

    def negate(self):
        self.is_negated = not self.is_negated

class MapProperty(Property):
    ...

@dataclasses.dataclass
class MapProperty_Size(MapProperty):
    size: Kore.Pattern # functional pattern of sort SortInt

@dataclasses.dataclass
class MapProperty_HasKey(MapProperty):
    key: Kore.Pattern # functional pattern

@dataclasses.dataclass
class MapProperty_HasKeyValue(MapProperty):
    key: Kore.Pattern # functional pattern
    value: Kore.Pattern # functional pattern

def patternToProperty(phi: Kore.Pattern, about: Kore.EVar) -> Property | None:
    map_in_keys: str = "Lbl'Unds'in'Unds'keys'LParUndsRParUnds'MAP'Unds'Bool'Unds'KItem'Unds'Map"
    map_lookup: str = "LblMap'Coln'lookup"
    map_size: str = "Lblsize'LParUndsRParUnds'MAP'Unds'Int'Unds'Map"
    aboutp: Kore.Pattern = about
    match phi:
        case Kore.Not(_, phi2):
            pr = patternToProperty(phi2, about)
            if pr is not None:
                pr.negate()
            return pr
        # Map.in_keys
        case Kore.Equals(_, _, KorePrelude.TRUE, Kore.App(map_in_keys, (), (item, aboutp))):
            return MapProperty_HasKey(key=item)
        case Kore.Equals(_, _, Kore.App(map_in_keys, (), (item, aboutp)), KorePrelude.TRUE):
            return MapProperty_HasKey(key=item)
        # Map.lookup
        case Kore.Equals(_, _, Kore.App(map_lookup, (), (aboutp,key)), value):
            return MapProperty_HasKeyValue(key=key,value=value)
        case Kore.Equals(_, _, value, Kore.App(map_lookup, (), (aboutp,key))):
            return MapProperty_HasKeyValue(key=key,value=value)
        # Map.size
        case Kore.Equals(_, _, Kore.App(map_size, (), (aboutp,)), size):
            return MapProperty_Size(size=size)
        case Kore.Equals(_, _, size, Kore.App(map_size, (), (aboutp,))):
            return MapProperty_Size(size=size)
    return None