import typing as T

import pyk.kore.syntax as Kore

def make_conjunction(sort, l: T.Sequence[Kore.Pattern]) -> Kore.Pattern:
    result: Kore.Pattern = Kore.Top(sort)
    for x in l:
        result = Kore.And(sort, result, x)
    return result

def make_disjunction(sort, l: T.Sequence[Kore.Pattern]) -> Kore.Pattern:
    result: Kore.Pattern = Kore.Bottom(sort)
    for x in l:
        result = Kore.Or(sort, result, x)
    return result
