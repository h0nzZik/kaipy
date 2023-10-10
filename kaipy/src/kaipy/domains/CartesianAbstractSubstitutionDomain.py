import dataclasses
import logging
import time
import typing as T
import pprint
import itertools

from immutabledict import immutabledict

import pyk.kore.syntax as Kore

from kaipy.PerfCounter import PerfCounter
import kaipy.kore_utils as KoreUtils
from kaipy.AbstractionContext import AbstractionContext
from kaipy.Substitution import Substitution
from kaipy.interfaces.IAbstractPatternDomain import IAbstractPatternDomain, IAbstractPattern
from kaipy.interfaces.IAbstractSubstitutionDomain import IAbstractSubstitution, IAbstractSubstitutionDomain


_LOGGER: T.Final = logging.getLogger(__name__)

@dataclasses.dataclass
class CartesianAbstractSubstitution(IAbstractSubstitution):
    mapping: T.Mapping[Kore.EVar, IAbstractPattern]

class CartesianAbstractSubstitutionDomain(IAbstractSubstitutionDomain):
    pattern_domain: IAbstractPatternDomain
    abstract_perf_counter: PerfCounter

    def __init__(self, pattern_domain: IAbstractPatternDomain):
        self.pattern_domain = pattern_domain
        self.abstract_perf_counter = PerfCounter()
    
    def abstract(self, ctx: AbstractionContext, subst: Substitution) -> CartesianAbstractSubstitution:
        old = time.perf_counter()
        a = self._abstract(ctx, subst)
        new = time.perf_counter()
        self.abstract_perf_counter.add(new - old)
        return a

    def _abstract(self, ctx: AbstractionContext, subst: Substitution) -> CartesianAbstractSubstitution:
        #_LOGGER.warning(f"abstract({subst})")
        # we ignore `preds`
        m = {
                v : self.pattern_domain.abstract(ctx, p)
                for (v,p) in subst.mapping.items()
                #if not KoreUtils.is_evar(p)
            }
        for k,v in m.items():
            if self.pattern_domain.is_top(v):
                # TODO let us 
                pass
        #m_filtered = {k:v for k,v in m.items() if not self.pattern_domain.is_top(v)}
        return CartesianAbstractSubstitution(m)
        #return CartesianAbstractSubstitution(m_filtered)

    def free_variables_of(self, a: IAbstractSubstitution) -> T.Set[Kore.EVar]:
        assert type(a) is CartesianAbstractSubstitution
        fvs = set(a.mapping.keys())
        for k,v in a.mapping.items():
            fvs.update(self.pattern_domain.free_variables_of(v))
        return fvs

    def concretize(self, a: IAbstractSubstitution) -> Substitution:
        assert type(a) is CartesianAbstractSubstitution
        mapping = {
            k: self.pattern_domain.concretize(v)
            for k,v in a.mapping.items()
            if not self.pattern_domain.is_top(v)
        }
        s =  Substitution(mapping)
        return s
    

    def disjunction(self, ctx: AbstractionContext, a1: IAbstractSubstitution, a2: IAbstractSubstitution) -> IAbstractSubstitution:
        assert type(a1) is CartesianAbstractSubstitution
        assert type(a2) is CartesianAbstractSubstitution
        mapping = {
            k: self.pattern_domain.disjunction(ctx, a1.mapping[k], a2.mapping[k])
            for k in set.intersection(set(a1.mapping.keys()), set(a2.mapping.keys()))
        }
        if len(a1.mapping.keys())  > len(mapping.keys()):
            _LOGGER.warning(f"Disjunction on CASD is generalizing way too much")
        return CartesianAbstractSubstitution(mapping)


    def is_top(self, a: IAbstractSubstitution) -> bool:
        assert type(a) is CartesianAbstractSubstitution
        return len(a.mapping.keys()) <= 0

    def is_bottom(self, a: IAbstractSubstitution) -> bool:
        assert type(a) is CartesianAbstractSubstitution
        return False

    def equals(self, a1: IAbstractSubstitution, a2: IAbstractSubstitution) -> bool:
        assert type(a1) is CartesianAbstractSubstitution
        assert type(a2) is CartesianAbstractSubstitution
        if a1.mapping.keys() != a2.mapping.keys():
            return False
        
        for k in a1.mapping.keys():
            ap1 = a1.mapping[k]
            ap2 = a2.mapping[k]
            if not self.pattern_domain.equals(ap1, ap2):
                return False
        return True

    def subsumes(self, a1: IAbstractSubstitution, a2: IAbstractSubstitution) -> bool:
        assert type(a1) is CartesianAbstractSubstitution
        assert type(a2) is CartesianAbstractSubstitution
        # If there is some key `k` in `a2` which is not in `a1`,
        # it means that `a2` restricts the state more than `a1`;
        # in that case, `a1` is not subsumed by `a2`.
        if not set(a1.mapping.keys()).issuperset(a2.mapping.keys()):
            return False
        # `a1` contains more keys; these are not restricted by `a2`.
        # It is enough to check for the keys of `a2`
        return all(
            [
                self.pattern_domain.subsumes(a1.mapping[k], a2.mapping[k])
                for k in a2.mapping.keys()
            ]
        )

    def to_str(self, a: IAbstractSubstitution, indent: int) -> str:
        assert type(a) is CartesianAbstractSubstitution
        s = (indent*' ') + '<cast\n'
        for k,v in a.mapping.items():
            s = s + ((indent+1)*' ') + k.text + ":\n"
            s = s + self.pattern_domain.to_str(v, indent=indent+2) + '\n'
        s = s + (indent*' ') + ">"
        return s

    def statistics(self) -> T.Dict[str, T.Any]:
        return {
            'name' : 'CartesianAbstractSubstitutionDomain',
            'abstract' : self.abstract_perf_counter.dict,
            'underlying': [self.pattern_domain.statistics()]
        }
