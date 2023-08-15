import dataclasses
import typing as T
import pprint
import itertools

from immutabledict import immutabledict

import pyk.kore.syntax as Kore

import kaipy.kore_utils as KoreUtils
from kaipy.Substitution import Substitution
from kaipy.IAbstractPatternDomain import IAbstractPatternDomain, IAbstractPattern
from kaipy.IAbstractSubstitutionDomain import IAbstractSubstitution, IAbstractSubstitutionDomain


@dataclasses.dataclass
class CartesianAbstractSubstitution(IAbstractSubstitution):
    mapping: T.Mapping[Kore.EVar, IAbstractPattern]

class CartesianAbstractSubstitutionDomain(IAbstractSubstitutionDomain):
    pattern_domain: IAbstractPatternDomain

    def __init__(self, pattern_domain: IAbstractPatternDomain):
        self.pattern_domain = pattern_domain
    
    def abstract(self, subst: Substitution, preds: T.List[Kore.Pattern]) -> IAbstractSubstitution:
        # we ignore `preds`
        m = {
                v : self.pattern_domain.abstract(p)
                for (v,p) in subst.mapping.items()
                if not KoreUtils.is_evar(p)
            }
        m_filtered = {k:v for k,v in m.items() if not self.pattern_domain.is_top(v)}
        return CartesianAbstractSubstitution(m_filtered)

    def concretize(self, a: IAbstractSubstitution) -> T.Tuple[Substitution, T.List[Kore.Pattern]]:
        assert type(a) is CartesianAbstractSubstitution

        # If `v` is top, we do not want to concretize it,
        # because the resulting constraint would be something like
        # `X = Top()`. But such substitution is useless.
        concretes: T.Dict[Kore.EVar, Kore.Pattern] = {
            k : self.pattern_domain.concretize(v)
            for k,v in a.mapping.items()
            if not self.pattern_domain.is_top(v)
        }
        for k in concretes:
            assert not KoreUtils.is_top(concretes[k])

        # It might happen that there are two evars, e1 and e2,
        # that are mapped to patterns p1 and p2, respectively,
        # such that p1 and p2 share some variable `v`.
        # This is unfortunate, because `v` in `p1` is unrelated
        # to `v` in `p2`, but the underlying pattern substitution
        # can not do anything about it. So we handle the case here.
        
        # Rename all the variables
        vars_to_rename = list(itertools.chain(*[
                    list(KoreUtils.free_evars_of_pattern(p))
                    for p in concretes.values()
                ]))
        vars_to_avoid: T.Set[Kore.EVar] = set()
        concretes_renamed: T.Dict[Kore.EVar, Kore.Pattern] = dict()
        for k,v in concretes.items():
            # But compute a separate renaming for each component
            renaming = KoreUtils.compute_renaming0(
                vars_to_avoid=list(vars_to_avoid),
                vars_to_rename=vars_to_rename
            )
            v_renamed = KoreUtils.rename_vars(renaming, v)
            concretes_renamed[k] = v_renamed
            vars_to_avoid = vars_to_avoid.union(
                KoreUtils.free_evars_of_pattern(v_renamed)
            )
        return (Substitution(immutabledict(concretes_renamed)),[])
    
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

    def print(self, a: IAbstractSubstitution) -> str:
        assert type(a) is CartesianAbstractSubstitution
        return pprint.pformat({ k: self.pattern_domain.print(v) for k,v in a.mapping.items() })
