
from itertools import (
    chain,
    product,
)


from typing import (
    Optional,
    Set,
    List,
    Iterable,
    Dict,
)

import pyk.kore.syntax as Kore


from pyk.kore.manip import (
    free_occs
)

class DefinitionError(Exception):
    pass

def get_module_by_name(definition: Kore.Definition, module_name: str) -> Kore.Module:
    for m in definition.modules:
        if m.name == module_name:
            return m

    #return None
    raise DefinitionError("Module '" + module_name + "' not found")

def get_all_imported_module_names(definition: Kore.Definition, module_name: str) -> Set[str]:
    module = get_module_by_name(definition, module_name)
    names : Set[str] = set()
    for s in module.sentences:
        match s:
            case Kore.Import(imported_module_name, _):
                names.add(imported_module_name)
    return names

def get_symbol_decl_from_module(module: Kore.Module, symbol_name: str) -> Optional[Kore.SymbolDecl]:
    for s in module.sentences:
        match s:
            case Kore.SymbolDecl(symbol, _, _, _, _):
                if symbol.name == symbol_name:
                    return s
    return None

def axioms(definition: Kore.Definition, main_module_name: str) -> List[Kore.Axiom]:
    module_names = {main_module_name}.union(get_all_imported_module_names(definition, main_module_name))
    modules = map(lambda name: get_module_by_name(definition, name), module_names)
    axioms : List[Kore.Axiom] = []
    for m in modules:
        axioms.extend(m.axioms)
    return axioms

def rewrite_axioms(definition: Kore.Definition, main_module_name: str) -> Iterable[Kore.Axiom]:
    for a in axioms(definition, main_module_name):
        match a:
            case Kore.Axiom(_, Kore.Rewrites(_, _, _), _):
                yield a

def get_symbol_decl_from_definition(definition: Kore.Definition, main_module_name: str, symbol_name: str) -> Kore.SymbolDecl:
    module_names = {main_module_name}.union(get_all_imported_module_names(definition, main_module_name))
    modules = map(lambda name: get_module_by_name(definition, name), module_names)
    decls = [decl for decl in map(lambda module: get_symbol_decl_from_module(module, symbol_name), modules) if decl is not None]
    if len(list(decls)) >= 1:
        return decls[0]
    raise DefinitionError("No symbol '" + symbol_name + "' found in '" + main_module_name + "' (or recursively imported modules)")

def get_symbol_sort(definition: Kore.Definition, main_module_name: str, symbol_name: str) -> Kore.Sort:
    decl = get_symbol_decl_from_definition(definition, main_module_name, symbol_name)
    return decl.sort


def get_top_cell_initializer(definition: Kore.Definition) -> str:
    for a in definition.attrs:
        if a.symbol == "topCellInitializer":
            match a.args[0]:
                case Kore.App(sym, _, _):
                    return sym
    raise DefinitionError("topCellInitializer not found")
    
def rename_vars(renaming: Dict[str, str], phi: Kore.Pattern) -> Kore.Pattern:
    match phi:
        # The main case
        case Kore.EVar(name, sort):
            if name in renaming:
                return Kore.EVar(renaming[name], sort)
            return Kore.EVar(name, sort)

        # The recursive cases    
        case Kore.App(symbol_name, sorts, args):
            return Kore.App(symbol_name, sorts, tuple(map(lambda p: rename_vars(renaming, p), args)))
        case Kore.Not(sort, pattern):
            return Kore.Not(sort, rename_vars(renaming, pattern))
        case Kore.And(sort, left, right):
            return Kore.And(sort, rename_vars(renaming, left), rename_vars(renaming, right))
        case Kore.Or(sort, left, right):
            return Kore.Or(sort, rename_vars(renaming, left), rename_vars(renaming, right))
        case Kore.Implies(sort, left, right):
            return Kore.Implies(sort, rename_vars(renaming, left), rename_vars(renaming, right))
        case Kore.Iff(sort, left, right):
            return Kore.Iff(sort, rename_vars(renaming, left), rename_vars(renaming, right))
        case Kore.Exists(sort, var, pattern):
            new_dict = dict(renaming)
            new_dict.update({var.name : var.name})
            return Kore.Exists(sort, var, rename_vars(new_dict, pattern))
        case Kore.Forall(sort, var, pattern):
            new_dict = dict(renaming)
            new_dict.update({var.name : var.name})
            return Kore.Forall(sort, var, rename_vars(new_dict, pattern))
        # Base cases
        case Kore.Equals(op_sort, sort, left, right):
            return Kore.Equals(op_sort, sort, rename_vars(renaming, left), rename_vars(renaming, right))
        case Kore.In(op_sort, sort, left, right):
            return Kore.In(op_sort, sort, rename_vars(renaming, left), rename_vars(renaming, right))
        case Kore.DV(_,_):
            return phi
        case Kore.SVar(_, _):
            return phi
        case Kore.String(_):
            return phi
        case Kore.Top(_):
            return phi
        case Kore.Bottom(_):
            return phi
        case _:
            raise NotImplementedError()
    raise NotImplementedError()

def free_evars_of_pattern(p: Kore.Pattern) -> Set[Kore.EVar]:
    return set(chain.from_iterable(free_occs(p).values()))


def int_or_None(s: str) -> Optional[int]:
    try:
        return int(s)
    except:
        return None

def get_fresh_evars_with_sorts(avoid: List[Kore.EVar], sorts: List[Kore.Sort], prefix="Fresh") -> List[Kore.EVar]:
    names_to_avoid = map(lambda ev: ev.name, avoid)
    names_with_prefix_to_avoid : List[str] = [name for name in names_to_avoid if name.startswith(prefix)]
    suffixes_to_avoid : List[str] = [name.removeprefix(prefix) for name in names_with_prefix_to_avoid]
    nums_to_avoid : List[int] = [ion for ion in map(int_or_None, suffixes_to_avoid) if ion is not None]
    if len(list(nums_to_avoid)) >= 1:
        n = max(nums_to_avoid) + 1
    else:
        n = 0
    nums = list(range(n, n + len(sorts)))
    fresh_evars : List[Kore.EVar] = list(map(lambda m: Kore.EVar(name=prefix + str(m), sort=sorts[m - n]), nums))
    return fresh_evars

def get_attr(attrs: tuple[Kore.App, ...], attr: str, default_value):
    for a in attrs:
        if a.symbol == attr:
            return a.args
    return default_value

def axiom_uuid(axiom: Kore.Axiom) -> str:
    a2 = get_attr(axiom.attrs, "UNIQUE'Unds'ID", None)
    if a2 is not None:
        match a2[0]:
            case Kore.String(s):
                return s
    raise ValueError(f"No unique id! {axiom}")

def axiom_label(axiom: Kore.Axiom) -> str:
    a1 = get_attr(axiom.attrs, 'label', None)
    if a1 is not None:
        match a1[0]:
            case Kore.String(s):
                return s
    return axiom_uuid(axiom)


def extract_equalities_from_witness(expected_vars : Set[str], witness : Kore.Pattern) -> Dict[Kore.EVar, Kore.Pattern]:
    result : Dict[Kore.EVar, Kore.Pattern] = dict()
    def go(w : Kore.Pattern):
        match w:
            case Kore.And(_, l, r):
                go(l)
                go(r)
                return
            case Kore.Equals(_, _, l, r):
                if type(l) is Kore.EVar and l.name in expected_vars:
                    result[l] = r
                    return
                if type(r) is Kore.EVar and r.name in expected_vars:
                    result[r] = l
                    return
                raise ValueError(f"Unexpected equality '{l} = {r}' in the witness {witness}")
            case _:
                return

    go(witness)
    return result



def some_subpatterns_of(phi: Kore.Pattern) -> Set[Kore.Pattern]:
    subs: Set[Kore.Pattern] = set()
    match phi:
        # The recursive cases    
        case Kore.App(symbol_name, sorts, args):
            subs = set().union(*[some_subpatterns_of(a) for a in args])
    return {phi}.union(subs)
