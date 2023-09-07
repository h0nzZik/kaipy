import dataclasses
import logging
import typing as T
import pprint
import itertools

from immutabledict import immutabledict

import pyk.kore.syntax as Kore

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

    def __init__(self, pattern_domain: IAbstractPatternDomain):
        self.pattern_domain = pattern_domain
    
    def abstract(self, ctx: AbstractionContext, subst: Substitution) -> CartesianAbstractSubstitution:
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

    def refine(self, ctx: AbstractionContext, a: IAbstractSubstitution, c: T.List[Kore.MLPred]) -> CartesianAbstractSubstitution:
        assert type(a) is CartesianAbstractSubstitution
        return a
        #return self.do_refine(ctx, a, c)

    # I am not sure if this is useful
    def do_refine(self, ctx: AbstractionContext, a: IAbstractSubstitution, c: T.List[Kore.MLPred]) -> CartesianAbstractSubstitution:
        assert type(a) is CartesianAbstractSubstitution
        d = dict(a.mapping)
        for p in c:
            match p:
                case Kore.Equals(_, _, Kore.EVar(_, _), Kore.EVar(_, _)):
                    continue
                case Kore.Equals(_, _, Kore.EVar(n, s), right):
                    if Kore.EVar(n, s) in d.keys():
                        d[Kore.EVar(n,s)] = self.pattern_domain.refine(ctx, d[Kore.EVar(n, s)], right)
                    else:
                        d[Kore.EVar(n,s)] = self.pattern_domain.abstract(ctx, right)
                    continue
                case Kore.Equals(_, _, left, Kore.EVar(n, s)):
                    if Kore.EVar(n, s) in d.keys():
                        d[Kore.EVar(n,s)] = self.pattern_domain.refine(ctx, d[Kore.EVar(n, s)], left)
                    else:
                        d[Kore.EVar(n,s)] = self.pattern_domain.abstract(ctx, left)
        return CartesianAbstractSubstitution(d)


    def concretize(self, a: IAbstractSubstitution) -> Substitution:
        assert type(a) is CartesianAbstractSubstitution
        mapping = {
            k: self.pattern_domain.concretize(v)
            for k,v in a.mapping.items()
            if not self.pattern_domain.is_top(v)
        }
        s =  Substitution(mapping)
        #_LOGGER.warning(f"concretize() = {s}")
        return s
        # # If `v` is top, we do not want to concretize it,
        # # because the resulting constraint would be something like
        # # `X = Top()`. But such substitution is useless.
        # # So, we replace Top() with a free variable of a given sort.
        # concretes: T.Dict[Kore.EVar, Kore.Pattern] = {
        #     k : ( Kore.EVar(name="VarDEFAULT", sort=k.sort) if self.pattern_domain.is_top(v) else self.pattern_domain.concretize(v))
        #     for k,v in a.mapping.items()
        #     #if not self.pattern_domain.is_top(v)
        # }
        # for k in concretes:
        #     assert not KoreUtils.is_top(concretes[k])

        # # It might happen that there are two evars, e1 and e2,
        # # that are mapped to patterns p1 and p2, respectively,
        # # such that p1 and p2 share some variable `v`.
        # # This is unfortunate, because `v` in `p1` is unrelated
        # # to `v` in `p2`, but the underlying pattern substitution
        # # can not do anything about it. So we handle the case here.
        
        # # Rename all the variables
        # vars_to_rename = list(itertools.chain(*[
        #             list(KoreUtils.free_evars_of_pattern(p))
        #             for p in concretes.values()
        #         ]))
        # vars_to_avoid: T.Set[Kore.EVar] = set()
        # concretes_renamed: T.Dict[Kore.EVar, Kore.Pattern] = dict()
        # for k,v in concretes.items():
        #     # But compute a separate renaming for each component
        #     renaming = KoreUtils.compute_renaming0(
        #         vars_to_avoid=list(vars_to_avoid),
        #         vars_to_rename=vars_to_rename
        #     )
        #     v_renamed = KoreUtils.rename_vars(renaming, v)
        #     concretes_renamed[k] = v_renamed
        #     vars_to_avoid = vars_to_avoid.union(
        #         KoreUtils.free_evars_of_pattern(v_renamed)
        #     )
        # return Substitution(immutabledict(concretes_renamed))
    

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
