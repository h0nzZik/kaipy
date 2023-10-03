import dataclasses
import typing as T

import pyk.kore.syntax as Kore
import pyk.kore.prelude as KorePrelude

from kaipy.ReachabilitySystem import ReachabilitySystem
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


@dataclasses.dataclass(frozen=True)
class ThingWithProperties:
    thing: Kore.Pattern # should be functional in all valuations; e.g., a variable
    properties: T.List[Property]

class Labels:
    map_in_keys: T.Final = "Lbl'Unds'in'Unds'keys'LParUndsRParUnds'MAP'Unds'Bool'Unds'KItem'Unds'Map"
    map_lookup: T.Final = "LblMap'Coln'lookup"
    map_size: T.Final = "Lblsize'LParUndsRParUnds'MAP'Unds'Int'Unds'Map"

# `about` is usually a variable (Kore.EVar), but can be anything of sort Map
def patternToThingWithProperty(phi: Kore.Pattern) -> ThingWithProperties | None:
    match phi:
        case Kore.Not(_, phi2):
            tpr = patternToThingWithProperty(phi2)
            if tpr is not None:
                for p in tpr.properties:
                    p.negate()
            return tpr
        # Map.in_keys
        case Kore.Equals(_, _, KorePrelude.TRUE, Kore.App(Labels.map_in_keys, (), (item, about))):
            return ThingWithProperties(about, [MapProperty_HasKey(key=item)])
        case Kore.Equals(_, _, Kore.App(Labels.map_in_keys, (), (item, about)), KorePrelude.TRUE):
            return ThingWithProperties(about, [MapProperty_HasKey(key=item)])
        # Map.lookup
        case Kore.Equals(_, _, Kore.App(Labels.map_lookup, (), (about,key)), value):
            return ThingWithProperties(about, [MapProperty_HasKeyValue(key=key,value=value)])
        case Kore.Equals(_, _, value, Kore.App(Labels.map_lookup, (), (about,key))):
            return ThingWithProperties(about, [MapProperty_HasKeyValue(key=key,value=value)])
        # Map.size
        case Kore.Equals(_, _, Kore.App(Labels.map_size, (), (about,)), size):
            return ThingWithProperties(about, [MapProperty_Size(size=size)])
        case Kore.Equals(_, _, size, Kore.App(Labels.map_size, (), (about,))):
            return ThingWithProperties(about, [MapProperty_Size(size=size)])
    return None



def thingWithPropertiesToConstraints(rs: ReachabilitySystem, twp: ThingWithProperties) -> T.List[Kore.Pattern]:
    constraints: T.List[Kore.Pattern] = list()
    for p in twp.properties:
        match p:
            case MapProperty_Size(sz):
                constraints.append(Kore.Equals(Kore.SortApp('SortInt', ()), rs.top_sort, Kore.App(Labels.map_size, (), (twp.thing,)), sz))
            case MapProperty_HasKey(key):
                constraints.append(Kore.Equals(Kore.SortApp('SortBool', ()), rs.top_sort, KorePrelude.TRUE, Kore.App(Labels.map_in_keys, (), (key, twp.thing))))
            case MapProperty_HasKeyValue(key, value):
                constraints.append(Kore.Equals(rs.sortof(value), rs.top_sort, Kore.App(Labels.map_lookup, (), (twp.thing,key)), value))
    return constraints


# assumes there are no conjunctions in `constraints`;
# it is the responsibility of caller to make the input list as flat as possible
def constraints_to_things(constraints: T.List[Kore.Pattern]) -> T.List[ThingWithProperties]:
    twp_in_opt: T.List[ThingWithProperties|None]  = [patternToThingWithProperty(c) for c in constraints]
    twp_in: T.List[ThingWithProperties] = [t for t in twp_in_opt if t is not None]
    twp_out: T.Dict[Kore.Pattern, ThingWithProperties] = dict()
    # merge them
    for t in twp_in:
        if t.thing in twp_out.keys():
            found = twp_out[t.thing]
            twp_out[t.thing] = ThingWithProperties(t.thing, found.properties + t.properties)
        else:
            twp_out[t.thing] = t
    
    return list(twp_out.values())
