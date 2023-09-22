import abc
import dataclasses
import time
import typing as T

import pyk.kore.syntax as Kore

import kaipy.kore_utils as KoreUtils
from kaipy.PerfCounter import PerfCounter
from kaipy.interfaces.IAbstractConstraintDomain import IAbstractConstraint, IAbstractConstraintDomain
from kaipy.interfaces.IAbstractMapDomain import IAbstractMap, IAbstractMapDomain
from kaipy.AbstractionContext import AbstractionContext
from kaipy.ReachabilitySystem import ReachabilitySystem
import kaipy.Properties



@dataclasses.dataclass(frozen=True)
class PropertyHubElement(IAbstractConstraint):
    thing: Kore.Pattern

@dataclasses.dataclass(frozen=True)
class PropertyHubMapElement(PropertyHubElement):
    abstract_map: IAbstractMap

@dataclasses.dataclass(frozen=True)
class PropertyHubElements(IAbstractConstraint):
    elements: T.List[PropertyHubElement]

class PropertyHubConstraintDomain(IAbstractConstraintDomain):
    rs: ReachabilitySystem
    map_domain: IAbstractMapDomain
    abstract_perf_counter: PerfCounter

    def __init__(self, rs: ReachabilitySystem, map_domain: IAbstractMapDomain):
        self.rs = rs
        self.map_domain = map_domain
        self.abstract_perf_counter = PerfCounter()

    def _thing_supported(self, thing: Kore.Pattern) -> bool:
        match thing:
            case Kore.EVar(_,_):
                return True
            #case Kore.App("Lbl'Stop'Map", (), ()):
            #    return True
        return False

    def abstract(self, ctx: AbstractionContext, over_variables: T.Set[Kore.EVar], constraints: T.List[Kore.Pattern]) -> IAbstractConstraint:
        old = time.perf_counter()
        a = self._abstract(ctx, over_variables, constraints)
        new = time.perf_counter()
        self.abstract_perf_counter.add(new - old)
        return a

    def _abstract(self, ctx: AbstractionContext, over_variables: T.Set[Kore.EVar], constraints: T.List[Kore.Pattern]) -> IAbstractConstraint:
        # TODO think about whether we want to use 'over_variables' or not
        twps: T.List[kaipy.Properties.ThingWithProperties] = kaipy.Properties.constraints_to_things(constraints)

        # TODO: What if there are too many things (with properties)? How do we ensure termination of everything, including disjunction?
        elements: T.List[PropertyHubElement] = list()
        for twp in twps:
            if not self._thing_supported(twp.thing):
                continue

            s = self.rs.sortof(twp.thing)
            match s:
                case Kore.SortApp('SortMap', ()):
                    elements.append(
                        PropertyHubMapElement(
                            thing=twp.thing,
                            abstract_map=self.map_domain.abstract(ctx, twp.properties)
                        )
                    )
        
        return PropertyHubElements(elements)
  
    def free_variables_of(self, a: IAbstractConstraint) -> T.Set[Kore.EVar]:
        assert type(a) is PropertyHubElements
        match a:
            case PropertyHubMapElement(thing, _):
                return KoreUtils.free_evars_of_pattern(thing)
        raise NotImplementedError()

    def refine(self, ctx: AbstractionContext, a: IAbstractConstraint, constraints: T.List[Kore.Pattern]) -> IAbstractConstraint:
        return a

    def disjunction(self, ctx: AbstractionContext, a1: IAbstractConstraint, a2: IAbstractConstraint) -> IAbstractConstraint:
        assert type(a1) is PropertyHubElements
        assert type(a2) is PropertyHubElements
        m1: T.Mapping[Kore.Pattern, PropertyHubElement] = { e.thing : e for e in a1.elements }
        m2: T.Mapping[Kore.Pattern, PropertyHubElement] = { e.thing : e for e in a2.elements }
        common_things: T.Set[Kore.Pattern] = set(m1.keys()).intersection(set(m2.keys()))
        uncommon_elements: T.List[PropertyHubElement] = [v for k,v in m1.items() if k not in common_things] + [v for k,v in m2.items() if k not in common_things]
        common_elements: T.List[PropertyHubElement] = []
        for thing in common_things:
            e1 = m1[thing]
            e2 = m2[thing]
            match e1:
                case PropertyHubMapElement(_, _):
                    assert type(e2) is PropertyHubMapElement
                    common_elements.append(PropertyHubMapElement(thing, self.map_domain.disjunction(ctx, e1.abstract_map, e2.abstract_map)))
                case _:
                    raise NotImplementedError()
        return PropertyHubElements(elements=uncommon_elements+common_elements)

    def concretize(self, a: IAbstractConstraint) -> T.List[Kore.Pattern]:
        assert type(a) is PropertyHubElements
        constraints: T.List[Kore.Pattern] = list()
        for e in a.elements:
            match e:
                case PropertyHubMapElement(Kore.EVar(_, _), ae):
                    props = self.map_domain.concretize(ae)
                    twp = kaipy.Properties.ThingWithProperties(e.thing, props)
                    constraints.extend(kaipy.Properties.thingWithPropertiesToConstraints(self.rs, twp))
                case _:
                    raise NotImplementedError()
        return constraints
    
    def is_top(self, a: IAbstractConstraint) -> bool:
        assert type(a) is PropertyHubElements
        return len(a.elements) <= 0

    def is_bottom(self, a: IAbstractConstraint) -> bool:
        assert type(a) is PropertyHubElements
        for e in a.elements:
            match e:
                case PropertyHubMapElement(_, am):
                    if self.map_domain.is_bottom(am):
                        return True
                case _:
                    raise NotImplementedError()
        return False

    def subsumes(self, a1: IAbstractConstraint, a2: IAbstractConstraint) -> bool:
        assert type(a1) is PropertyHubElements
        assert type(a2) is PropertyHubElements
        for e1 in a1.elements:
            assert type(e1.thing) is Kore.EVar
            found: bool = False
            for e2 in a2.elements:
                assert type(e2.thing) is Kore.EVar
                if e1.thing == e2.thing:
                    assert type(e1) is PropertyHubMapElement
                    assert type(e2) is PropertyHubMapElement
                    if not self.map_domain.subsumes(e1.abstract_map, e2.abstract_map):
                        return False
                    found = True
                    break
            if not found:
                return False
        return True
    
    def equals(self, a1: IAbstractConstraint, a2: IAbstractConstraint) -> bool:
        assert type(a1) is PropertyHubElements
        assert type(a2) is PropertyHubElements
        return self.subsumes(a1, a2) and self.subsumes(a2, a1)

    def to_str(self, a: IAbstractConstraint, indent: int) -> str:
        assert type(a) is PropertyHubElements
        s = (indent*' ') + "<phcd\n"
        for e in a.elements:
            assert type(e) is PropertyHubMapElement
            s = s + self.map_domain.to_str(e.abstract_map, indent=indent+1) + ',\n'
        s = s + (indent*' ') + ">"
        return s
    
    def statistics(self) -> T.Dict[str, T.Any]:
        return {
            'abstract' : self.abstract_perf_counter.dict,
            'underlying' : {
                'map_domain' : self.map_domain.statistics(),
            },
        }