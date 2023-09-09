import typing as T

import pyk.kore.syntax as Kore

import kaipy.kore_utils as KoreUtils
import kaipy.cnf

def test_to_cnf():
    sortx = Kore.SortApp("SortX", ())
    x1 = Kore.EVar("x1", sortx)
    x2 = Kore.EVar("x2", sortx)
    x3 = Kore.EVar("x3", sortx)
    x4 = Kore.EVar("x4", sortx)
    dnf = Kore.Or(sortx, Kore.And(sortx, x1, x2), Kore.And(sortx, x3, x4))
    cnf = kaipy.cnf.to_cnf(dnf, sort=sortx)
    #print(cnf.text)
    cnf_clauses = {tuple(e.name for e in KoreUtils.or_to_list(x)) for x in KoreUtils.and_to_list(cnf)} # type: ignore
    #print(cnf_clauses)
    assert cnf_clauses == {('x2', 'x4'), ('x1', 'x3'), ('x1', 'x4'), ('x2', 'x3')}
