import typing as T

import pyk.kore.syntax as Kore

def make_conjunction(sort, l: T.Sequence[Kore.Pattern]) -> Kore.Pattern:
    result: Kore.Pattern = Kore.Top(sort)
    if len(l) == 0:
        return result
    if len(l) == 1:
        return l[0]
    result = l[0]
    for x in l[1:]:
        result = Kore.And(sort, result, x)
    return result

def make_disjunction(sort, l: T.Sequence[Kore.Pattern]) -> Kore.Pattern:
    result: Kore.Pattern = Kore.Bottom(sort)
    if len(l) == 0:
        return result
    if len(l) == 1:
        return l[0]
    result = l[0]
    for x in l[1:]:
        result = Kore.Or(sort, result, x)
    return result
