import typing as T

import pyk.kore.syntax as Kore

import sympy
import sympy.logic as SympyLogic
from sympy.logic.boolalg import Boolean
from sympy import And, Or, Symbol, symbols

import kaipy.kore_utils as KoreUtils

def _to_sympy(phi: Kore.Pattern):
    d: T.Dict[Kore.Pattern, sympy.Symbol] = dict()
    counter = 1
    def go(phi):
        nonlocal d
        nonlocal counter
        match phi:
            case Kore.And(_, l, r):
                return And(go(l), go(r))
            case Kore.Or(_, l, r):
                return Or(go(l), go(r))
            case _:
                if phi in d.keys():
                    return d[phi]
                s = symbols(f'x{counter}')
                counter = counter + 1
                d[phi] = s
                return s
    new_phi = go(phi)
    return new_phi, d


def _from_sympy(phi, dback, sort: Kore.Sort) -> Kore.Pattern:
    if phi in dback:
        return dback[phi]
    
    if type(phi) is And:
        args = [_from_sympy(a, dback, sort) for a in phi.args]
        return KoreUtils.make_conjunction(sort, l=args)
    if type(phi) is Or:
        args = [_from_sympy(a, dback, sort) for a in phi.args]
        return KoreUtils.make_disjunction(sort, l=args)
    if type(phi) is False:
        return Kore.Bottom(sort)
    if type(phi) is True:
        return Kore.Top(sort)
    assert False

def to_cnf(phi: Kore.Pattern, sort: Kore.Sort) -> Kore.Pattern:
    new_phi, d = _to_sympy(phi)
    dback = {v:k for k,v in d.items()}
    return _from_sympy(phi=SympyLogic.to_cnf(new_phi), dback=dback, sort=sort)