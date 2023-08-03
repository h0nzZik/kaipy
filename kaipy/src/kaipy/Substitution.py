import dataclasses
import typing as T

import pyk.kore.syntax as Kore

import kaipy.kore_utils

@dataclasses.dataclass(frozen=True)
class Substitution:
    mapping: T.Mapping[Kore.EVar, Kore.Pattern]

    def free_evars(self) -> T.Set[Kore.EVar]:
        fe: T.Set[Kore.EVar] = set()
        for _, p in self.mapping.items():
            fe = fe.union(kaipy.kore_utils.free_evars_of_pattern(p))
        return fe


def subst_to_pattern(sort: Kore.Sort, subst: Substitution) -> Kore.Pattern:
    return kaipy.kore_utils.mapping_to_pattern(sort, subst.mapping)