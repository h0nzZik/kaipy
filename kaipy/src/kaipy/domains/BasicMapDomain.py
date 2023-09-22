import abc
import dataclasses
import time
import typing as T

import pyk.kore.syntax as Kore
import pyk.kore.prelude as KorePrelude

from kaipy.PerfCounter import PerfCounter
import kaipy.Properties as Properties
import kaipy.kore_utils as KoreUtils
from kaipy.ReachabilitySystem import ReachabilitySystem
from kaipy.interfaces.IAbstractPatternDomain import IAbstractPattern, IAbstractPatternDomain
from kaipy.interfaces.IAbstractMapDomain import IAbstractMap, IAbstractMapDomain
from kaipy.AbstractionContext import AbstractionContext


@dataclasses.dataclass(frozen=True)
class BasicMap(IAbstractMap):
    # mapping from (typically functional) patterns, into (typically functional) patterns / terms.
    # None value represents an unknown value
    mapping : T.Mapping[IAbstractPattern, IAbstractPattern|None]

class BasicMapDomain(IAbstractMapDomain):
    rs: ReachabilitySystem
    key_domain: IAbstractPatternDomain
    value_domain: IAbstractPatternDomain
    abstract_perf_counter: PerfCounter

    # Stuff have to concretize to sort KItem in the underlying domains
    def __init__(self, rs: ReachabilitySystem, key_domain: IAbstractPatternDomain, value_domain: IAbstractPatternDomain):
        self.rs = rs
        self.key_domain = key_domain
        self.value_domain = value_domain
        self.abstract_perf_counter = PerfCounter()

    def _keys_overlap(self, k1: IAbstractPattern, k2: IAbstractPattern):
        return not KoreUtils.is_bottom(self.rs.simplify(Kore.And(KorePrelude.SORT_K_ITEM, self.key_domain.concretize(k1), self.key_domain.concretize(k2))))


    def abstract(self, ctx: AbstractionContext, properties: T.List[Properties.Property]) -> IAbstractMap:
        old = time.perf_counter()
        a = self._abstract(ctx, properties)
        new = time.perf_counter()
        self.abstract_perf_counter.add(new - old)
        return a

    def _abstract(self, ctx: AbstractionContext, properties: T.List[Properties.Property]) -> IAbstractMap:
        mapping : T.Dict[IAbstractPattern, IAbstractPattern|None] = dict()

        for p in properties:
            match p:
                case Properties.MapProperty_HasKey(key):
                    mapping[self.key_domain.abstract(ctx, key)] = None
                case Properties.MapProperty_HasKeyValue(key, value):
                    mapping[self.key_domain.abstract(ctx, key)] = self.value_domain.abstract(ctx, value) 
                case Properties.MapProperty_Size(size):
                    # TODO
                    pass

        # Assert that syntactically different keys do not overlap
        for k1 in mapping.keys():
            for k2 in mapping.keys():
                if k1 != k2:
                    assert not self._keys_overlap(k1, k2)

        return BasicMap(mapping=mapping)
    
    def concretize(self, a: IAbstractMap) -> T.List[Properties.Property]:
        assert type(a) is BasicMap
        properties: T.List[Properties.Property] = list()
        for k,v in a.mapping.items():
            if v is None:
                properties.append(Properties.MapProperty_HasKey(self.key_domain.concretize(k)))
            else:
                properties.append(Properties.MapProperty_HasKeyValue(self.key_domain.concretize(k), self.value_domain.concretize(v)))
        return properties

    
    def disjunction(self, ctx: AbstractionContext, a1: IAbstractMap, a2: IAbstractMap) -> IAbstractMap:
        assert type(a1) is BasicMap
        assert type(a2) is BasicMap
        mapping : T.Dict[IAbstractPattern, IAbstractPattern|None] = dict()
        overlapping_keys: T.Set[T.Tuple[IAbstractPattern, IAbstractPattern]]
        non_overlapping_keys: T.Set[T.Tuple[IAbstractPattern, IAbstractPattern]]
        for k1,v1 in a1.mapping.items():
            for k2,v2 in a2.mapping.items():
                if self._keys_overlap(k1, k2):
                    k1 = self.key_domain.disjunction(ctx, k1, k2)
                    if v1 is None:
                        v1 = v2
                    elif v2 is not None:
                        v1 = self.value_domain.disjunction(ctx, v1, v2)
            mapping[k1] = v1
        return BasicMap(mapping=mapping)
            
    
    def is_top(self, a: IAbstractMap) -> bool:
        assert type(a) is BasicMap
        return len(a.mapping.keys()) == 0

    def is_bottom(self, a: IAbstractMap) -> bool:
        return False

    def subsumes(self, a1: IAbstractMap, a2: IAbstractMap) -> bool:
        assert type(a1) is BasicMap
        assert type(a2) is BasicMap
        
        for k in a1.mapping.keys():
            if k not in a2.mapping:
                return False
            v1 = a1.mapping[k]
            v2 = a2.mapping[k]
            if v2 is None:
                continue
            if v1 is None:
                return False
            if not self.value_domain.subsumes(v1, v2):
                return False
        return True
    
    def equals(self, a1: IAbstractMap, a2: IAbstractMap) -> bool:
        return self.subsumes(a1, a2) and self.subsumes(a2, a1)
    
    def to_str(self, a: IAbstractMap, indent: int) -> str:
        assert type(a) is BasicMap
        s = (indent*' ') + "<bm\n"
        for k,v in a.mapping.items():
            s = s + self.key_domain.to_str(k, indent=indent+1) + ' => ' + (self.value_domain.to_str(v, indent=indent+1) if v is not None else "<None>") + ',\n'
        s = s + (indent*' ') + ">"
        return s
    
    def statistics(self) -> T.Dict[str, T.Any]:
        return {
            'abstract' : self.abstract_perf_counter.dict,
            'underlying' : {
                'key_domain' : self.key_domain.statistics(),
                'value_domain' : self.value_domain.statistics(),
            },
        }