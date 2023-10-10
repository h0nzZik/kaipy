import dataclasses
import logging
import time
import typing as T
import pprint
import itertools

from immutabledict import immutabledict

import pyk.kore.syntax as Kore

import kaipy.kore_utils as KoreUtils
from kaipy.PerfCounter import PerfCounter
from kaipy.AbstractionContext import AbstractionContext
from kaipy.Substitution import Substitution
from kaipy.interfaces.IAbstractPatternDomain import IAbstractPatternDomain, IAbstractPattern
from kaipy.interfaces.IAbstractSubstitutionDomain import IAbstractSubstitution, IAbstractSubstitutionDomain
from kaipy.interfaces.IAbstractSubstitutionsDomain import IAbstractSubstitutions, IAbstractSubstitutionsDomain


_LOGGER: T.Final = logging.getLogger(__name__)

@dataclasses.dataclass
class SubstitutionList(IAbstractSubstitutions):
    elements: T.List[IAbstractSubstitution]

class SubstitutionListDomain(IAbstractSubstitutionsDomain):
    underlying: IAbstractSubstitutionDomain
    abstract_perf_counter: PerfCounter

    # `underlying` has to be a finite domain in order for this to have finite height
    def __init__(self, underlying: IAbstractSubstitutionDomain):
        self.underlying = underlying
        self.abstract_perf_counter = PerfCounter()
    
    def abstract(self, ctx: AbstractionContext, substs: T.List[Substitution]) -> IAbstractSubstitutions:
        old = time.perf_counter()
        a = self._abstract(ctx, substs)
        new = time.perf_counter()
        self.abstract_perf_counter.add(new - old)
        return a


    def _abstract(self, ctx: AbstractionContext, substs: T.List[Substitution]) -> IAbstractSubstitutions:
        els = [self.underlying.abstract(ctx, subst) for subst in substs]
        return SubstitutionList(elements=els)
    
    def free_variables_of(self, a: IAbstractSubstitutions) -> T.Set[Kore.EVar]:
        assert type(a) is SubstitutionList
        return set(itertools.chain(*[self.underlying.free_variables_of(e) for e in a.elements]))

    def disjunction(self, ctx: AbstractionContext, a1: IAbstractSubstitutions, a2: IAbstractSubstitutions) -> SubstitutionList:
        assert type(a1) is SubstitutionList
        assert type(a2) is SubstitutionList
        elements: T.List[IAbstractSubstitution] = a1.elements.copy()
        for e2 in a2.elements:
            skip: bool = False
            for e1 in elements:
                if self.underlying.equals(e1, e2):
                    skip = True
                    break
            if not skip:
                elements.append(e2)
        #_LOGGER.warning(f"disjunction: result_len={len(elements)}")
        return SubstitutionList(elements=elements)

    def concretize(self, a: IAbstractSubstitutions) -> T.List[Substitution]:
        assert type(a) is SubstitutionList
        return [
            self.underlying.concretize(e)
            for e in a.elements
        ]

    def equals(self, a1: IAbstractSubstitutions, a2: IAbstractSubstitutions) -> bool:
        return self.subsumes(a1, a2) and self.subsumes(a2, a1)

    def subsumes(self, a1: IAbstractSubstitutions, a2: IAbstractSubstitutions) -> bool:
        assert type(a1) is SubstitutionList
        assert type(a2) is SubstitutionList
        for e1 in a1.elements:
            for e2 in a1.elements:
                if not self.underlying.subsumes(e1, e2):
                    return False
        return True
    
    def is_top(self, a: IAbstractSubstitutions) -> bool:
        assert type(a) is SubstitutionList
        return any([self.underlying.is_top(e) for e in a.elements])

    def is_bottom(self, a: IAbstractSubstitutions) -> bool:
        assert type(a) is SubstitutionList
        return len(a.elements) <= 0

    def to_str(self, a: IAbstractSubstitutions, indent: int) -> str:
        assert type(a) is SubstitutionList
        s: str = (indent*' ') + "<sl\n"
        for e in a.elements:
            s = f"{self.underlying.to_str(e, indent=indent+1)},\n"
        s = s + (indent*' ') + ">"
        return s

    def statistics(self) -> T.Dict[str, T.Any]:
        return {
            'name' : "SubstitutionListDomain",
            'abstract' : self.abstract_perf_counter.dict,
            'underlying' : [self.underlying.statistics()]
        }