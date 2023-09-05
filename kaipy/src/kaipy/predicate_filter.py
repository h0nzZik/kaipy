import typing as T

import pyk.kore.syntax as Kore

import kaipy.kore_utils as KoreUtils
from kaipy.cnf import to_cnf

def filter_out_predicates(
    phi: Kore.Pattern,
) -> T.Tuple[T.Optional[Kore.Pattern], T.List[Kore.MLPred]]:
    if issubclass(type(phi), Kore.MLPred):
        return None, [phi] # type: ignore
    match phi:
        case Kore.And(sort, left, right):
            lf, ps1 = filter_out_predicates(left)
            rf, ps2 = filter_out_predicates(right)
            if lf is None:
                return rf, (ps1 + ps2)
            if rf is None:
                return lf, (ps1 + ps2)
            return Kore.And(sort, lf, rf), (ps1 + ps2)
        case Kore.Or(sort, left, right):
            lf, ps1 = filter_out_predicates(left)
            rf, ps2 = filter_out_predicates(right)
            ps1l = KoreUtils.make_conjunction(sort, ps1)
            ps2l = KoreUtils.make_conjunction(sort, ps2)
            l: T.List[Kore.MLPred] = KoreUtils.and_to_list(to_cnf(phi=Kore.Or(sort, ps1l, ps2l), sort=sort)) # type: ignore
            if lf is None:
                return rf, l
            if rf is None:
                return lf, l
            return Kore.Or(sort, lf, rf), l
        case _:
            return phi, []


def get_predicates(phi: Kore.Pattern) -> T.List[Kore.MLPred]:
    _, preds = filter_out_predicates(phi)
    return preds
