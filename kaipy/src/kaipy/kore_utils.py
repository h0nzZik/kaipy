import functools
import typing as T
from itertools import chain, product

import pyk.kore.syntax as Kore
from pyk.kore.manip import free_occs


class DefinitionError(Exception):
    pass


def get_module_by_name(definition: Kore.Definition, module_name: str) -> Kore.Module:
    for m in definition.modules:
        if m.name == module_name:
            return m

    # return None
    raise DefinitionError("Module '" + module_name + "' not found")


def get_all_imported_module_names(
    definition: Kore.Definition, module_name: str
) -> T.Set[str]:
    module = get_module_by_name(definition, module_name)
    names: T.Set[str] = set()
    for s in module.sentences:
        match s:
            case Kore.Import(imported_module_name, _):
                names.add(imported_module_name)
    return names


def get_all_recursively_imported_module_names(
    definition: Kore.Definition, module_name: str
) -> T.Set[str]:
    names: T.Set[str] = {module_name}
    new_names: T.Set[str] = {module_name}
    while len(new_names) > 0:
        curr_name = new_names.pop()
        names_to_add = get_all_imported_module_names(definition, curr_name).difference(
            names
        )
        names = names.union(names_to_add)
        new_names = new_names.union(names_to_add)
    return names


def get_symbol_decl_from_module(
    module: Kore.Module, symbol_name: str
) -> T.Optional[Kore.SymbolDecl]:
    for s in module.sentences:
        match s:
            case Kore.SymbolDecl(symbol, _, _, _, _):
                if symbol.name == symbol_name:
                    return s
    return None


def axioms(definition: Kore.Definition, main_module_name: str) -> T.List[Kore.Axiom]:
    module_names = {main_module_name}.union(
        get_all_recursively_imported_module_names(definition, main_module_name)
    )
    modules = map(lambda name: get_module_by_name(definition, name), module_names)
    axioms: T.List[Kore.Axiom] = []
    for m in modules:
        axioms.extend(m.axioms)
    return axioms


def rewrite_axioms(
    definition: Kore.Definition, main_module_name: str
) -> T.Iterable[Kore.Axiom]:
    for a in axioms(definition, main_module_name):
        match a:
            case Kore.Axiom(_, Kore.Rewrites(_, _, _), _):
                yield a


def other_than_rewrite_axioms(
    definition: Kore.Definition, main_module_name: str
) -> T.Iterable[Kore.Axiom]:
    for a in axioms(definition, main_module_name):
        match a:
            case Kore.Axiom(_, Kore.Rewrites(_, _, _), _):
                continue
        yield a


def get_symbol_decl_from_definition(
    definition: Kore.Definition, main_module_name: str, symbol_name: str
) -> Kore.SymbolDecl:
    module_names = {main_module_name}.union(
        get_all_recursively_imported_module_names(definition, main_module_name)
    )
    modules = map(lambda name: get_module_by_name(definition, name), module_names)
    decls = [
        decl
        for decl in map(
            lambda module: get_symbol_decl_from_module(module, symbol_name), modules
        )
        if decl is not None
    ]
    if len(list(decls)) >= 1:
        return decls[0]
    raise DefinitionError(
        "No symbol '"
        + symbol_name
        + "' found in '"
        + main_module_name
        + "' (or recursively imported modules)"
    )


def get_symbol_sort(
    definition: Kore.Definition, main_module_name: str, symbol_name: str
) -> Kore.Sort:
    decl = get_symbol_decl_from_definition(definition, main_module_name, symbol_name)
    return decl.sort


def is_nonhooked_constructor_symbol(
    definition: Kore.Definition, main_module_name: str, symbol_name: str
) -> bool:
    decl = get_symbol_decl_from_definition(definition, main_module_name, symbol_name)
    if decl.hooked:
        print(f"symbol {symbol_name} is hooked")
        return False
    for attr in decl.attrs:
        match attr:
            case Kore.App("constructor", _, _):
                # print(f"symbol {symbol_name} is a constructor")
                return True
    # print(f"symbol {symbol_name} is NOT a constructor")
    return False


def get_top_cell_initializer(definition: Kore.Definition) -> str:
    for a in definition.attrs:
        if a.symbol == "topCellInitializer":
            match a.args[0]:
                case Kore.App(sym, _, _):
                    return sym
    raise DefinitionError("topCellInitializer not found")


def rename_vars(renaming: T.Dict[str, str], phi: Kore.Pattern) -> Kore.Pattern:
    match phi:
        # The main case
        case Kore.EVar(name, sort):
            if name in renaming:
                return Kore.EVar(renaming[name], sort)
            return Kore.EVar(name, sort)

        # The recursive cases
        case Kore.App(symbol_name, sorts, args):
            return Kore.App(
                symbol_name, sorts, tuple(map(lambda p: rename_vars(renaming, p), args))
            )
        case Kore.Not(sort, pattern):
            return Kore.Not(sort, rename_vars(renaming, pattern))
        case Kore.And(sort, left, right):
            return Kore.And(
                sort, rename_vars(renaming, left), rename_vars(renaming, right)
            )
        case Kore.Or(sort, left, right):
            return Kore.Or(
                sort, rename_vars(renaming, left), rename_vars(renaming, right)
            )
        case Kore.Implies(sort, left, right):
            return Kore.Implies(
                sort, rename_vars(renaming, left), rename_vars(renaming, right)
            )
        case Kore.Iff(sort, left, right):
            return Kore.Iff(
                sort, rename_vars(renaming, left), rename_vars(renaming, right)
            )
        case Kore.Exists(sort, var, pattern):
            new_dict = dict(renaming)
            new_dict.update({var.name: var.name})
            return Kore.Exists(sort, var, rename_vars(new_dict, pattern))
        case Kore.Forall(sort, var, pattern):
            new_dict = dict(renaming)
            new_dict.update({var.name: var.name})
            return Kore.Forall(sort, var, rename_vars(new_dict, pattern))
        # Base cases
        case Kore.Equals(op_sort, sort, left, right):
            return Kore.Equals(
                op_sort, sort, rename_vars(renaming, left), rename_vars(renaming, right)
            )
        case Kore.In(op_sort, sort, left, right):
            return Kore.In(
                op_sort, sort, rename_vars(renaming, left), rename_vars(renaming, right)
            )
        case Kore.DV(_, _):
            return phi
        case Kore.SVar(_, _):
            return phi
        case Kore.String(_):
            return phi
        case Kore.Top(_):
            return phi
        case Kore.Bottom(_):
            return phi
        case Kore.Ceil(op_sort, sort, pattern):
            return Kore.Ceil(op_sort, sort, rename_vars(renaming, pattern))
        case Kore.Floor(op_sort, sort, pattern):
            return Kore.Floor(op_sort, sort, rename_vars(renaming, pattern))
        case _:
            print(f"renaming not implemented for {phi}")
            raise NotImplementedError()
    raise NotImplementedError()



# This is very similar as as `rename_vars`
def apply_subst(subst: T.Mapping[Kore.EVar, Kore.Pattern], phi: Kore.Pattern) -> Kore.Pattern:
    match phi:
        # The main case
        case Kore.EVar(name, sort):
            if Kore.EVar(name, sort) in subst:
                return subst[Kore.EVar(name, sort)]
            return Kore.EVar(name, sort)

        # The recursive cases
        case Kore.App(symbol_name, sorts, args):
            return Kore.App(
                symbol_name, sorts, tuple(map(lambda p: apply_subst(subst, p), args))
            )
        case Kore.Not(sort, pattern):
            return Kore.Not(sort, apply_subst(subst, pattern))
        case Kore.And(sort, left, right):
            return Kore.And(
                sort, apply_subst(subst, left), apply_subst(subst, right)
            )
        case Kore.Or(sort, left, right):
            return Kore.Or(
                sort, apply_subst(subst, left), apply_subst(subst, right)
            )
        case Kore.Implies(sort, left, right):
            return Kore.Implies(
                sort, apply_subst(subst, left), apply_subst(subst, right)
            )
        case Kore.Iff(sort, left, right):
            return Kore.Iff(
                sort, apply_subst(subst, left), apply_subst(subst, right)
            )
        case Kore.Exists(sort, var, pattern):
            new_dict = dict(subst)
            new_dict.update({var: var})
            return Kore.Exists(sort, var, apply_subst(new_dict, pattern))
        case Kore.Forall(sort, var, pattern):
            new_dict = dict(subst)
            new_dict.update({var: var})
            return Kore.Forall(sort, var, apply_subst(new_dict, pattern))
        # Base cases
        case Kore.Equals(op_sort, sort, left, right):
            return Kore.Equals(
                op_sort, sort, apply_subst(subst, left), apply_subst(subst, right)
            )
        case Kore.In(op_sort, sort, left, right):
            return Kore.In(
                op_sort, sort, apply_subst(subst, left), apply_subst(subst, right)
            )
        case Kore.DV(_, _):
            return phi
        case Kore.SVar(_, _):
            return phi
        case Kore.String(_):
            return phi
        case Kore.Top(_):
            return phi
        case Kore.Bottom(_):
            return phi
        case Kore.Ceil(op_sort, sort, pattern):
            return Kore.Ceil(op_sort, sort, apply_subst(subst, pattern))
        case Kore.Floor(op_sort, sort, pattern):
            return Kore.Floor(op_sort, sort, apply_subst(subst, pattern))
        case _:
            print(f"substitution not implemented for {phi}")
            raise NotImplementedError()
    raise NotImplementedError()

def free_occs_det(pattern: Kore.Pattern) -> list[Kore.EVar]:
    occurrences: list[Kore.EVar] = []

    def collect(pattern: Kore.Pattern) -> None:
        if type(pattern) is Kore.EVar:
            if pattern not in occurrences:
                occurrences.append(pattern)
        else:
            for sub_pattern in pattern.patterns:
                collect(sub_pattern)

    collect(pattern)
    return occurrences

def free_evars_of_pattern(p: Kore.Pattern) -> T.Set[Kore.EVar]:
    return set(chain.from_iterable(free_occs(p).values()))


def existentially_quantify_variables(
    sort, pattern: Kore.Pattern, vars: T.List[Kore.EVar]
) -> Kore.Pattern:
    return functools.reduce(lambda p, var: Kore.Exists(sort, var, p), vars, pattern)


def existentially_quantify_free_variables(
    sort: Kore.Sort, pattern: Kore.Pattern
) -> Kore.Pattern:
    return existentially_quantify_variables(
        sort, pattern, list(free_evars_of_pattern(pattern))
    )


def int_or_None(s: str) -> T.Optional[int]:
    try:
        return int(s)
    except:
        return None


def get_fresh_evars_with_sorts(
    avoid: T.List[Kore.EVar], sorts: T.List[Kore.Sort], prefix="Fresh"
) -> T.List[Kore.EVar]:
    names_to_avoid = map(lambda ev: ev.name, avoid)
    names_with_prefix_to_avoid: T.List[str] = [
        name for name in names_to_avoid if name.startswith(prefix)
    ]
    suffixes_to_avoid: T.List[str] = [
        name.removeprefix(prefix) for name in names_with_prefix_to_avoid
    ]
    nums_to_avoid: T.List[int] = [
        ion for ion in map(int_or_None, suffixes_to_avoid) if ion is not None
    ]
    if len(list(nums_to_avoid)) >= 1:
        n = max(nums_to_avoid) + 1
    else:
        n = 0
    nums = list(range(n, n + len(sorts)))
    fresh_evars: T.List[Kore.EVar] = list(
        map(lambda m: Kore.EVar(name=prefix + str(m), sort=sorts[m - n]), nums)
    )
    return fresh_evars


def get_fresh_evar(
    avoid: T.List[Kore.EVar], sort: Kore.Sort, prefix="Fresh"
) -> Kore.EVar:
    return get_fresh_evars_with_sorts(avoid, [sort], prefix=prefix)[0]


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
    a1 = get_attr(axiom.attrs, "label", None)
    if a1 is not None:
        match a1[0]:
            case Kore.String(s):
                return s
    return axiom_uuid(axiom)


def extract_equalities_and_rest_from_witness(
    expected_vars: T.Set[str], witness: Kore.Pattern
) -> T.Tuple[T.Dict[Kore.EVar, Kore.Pattern], T.Optional[Kore.Pattern]]:
    result: T.Dict[Kore.EVar, Kore.Pattern] = dict()
    rest: T.Optional[Kore.Pattern] = None

    def add_to_rest(p: Kore.Pattern):
        nonlocal rest
        if rest is not None:
            rest = Kore.And(p.sort, rest, p)  # type: ignore
        else:
            rest = p

    def go(w: Kore.Pattern):
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
                add_to_rest(w)
                # raise ValueError(f"Unexpected equality '{l} = {r}' in the witness {witness}")
            case _:
                add_to_rest(w)
                return

    go(witness)
    return result, rest


def extract_equalities_from_witness(
    expected_vars: T.Set[str], witness: Kore.Pattern
) -> T.Dict[Kore.EVar, Kore.Pattern]:
    equalities, rest = extract_equalities_and_rest_from_witness(expected_vars, witness)
    return equalities


def some_subpatterns_of(phi: Kore.Pattern) -> T.Dict[Kore.Pattern, int]:
    subs: T.Dict[Kore.Pattern, int] = dict()

    def go(phi):
        subs[phi] = subs.get(phi, 0) + 1
        match phi:
            # The recursive cases
            case Kore.App(symbol_name, sorts, args):
                for a in args:
                    go(a)

    go(phi)
    return subs


def get_lhs(rule: Kore.Axiom) -> Kore.Pattern:
    match rule:
        case Kore.Axiom(vs, Kore.Rewrites(sort, lhs, rhs) as rewrites, _):
            return lhs
    raise RuntimeError("Not a rewrite rule")


def get_rhs(rule: Kore.Axiom) -> Kore.Pattern:
    match rule:
        case Kore.Axiom(vs, Kore.Rewrites(sort, lhs, rhs) as rewrites, _):
            return rhs
    raise RuntimeError("Not a rewrite rule")


def compute_renaming0(
    vars_to_avoid: T.List[Kore.EVar], vars_to_rename: T.List[Kore.EVar]
) -> T.Dict[str, str]:
    vars_to_avoid = vars_to_rename + vars_to_avoid
    new_vars = get_fresh_evars_with_sorts(
        avoid=list(vars_to_avoid), sorts=list(map(lambda ev: ev.sort, vars_to_rename))
    )
    vars_fr: T.List[str] = list(map(lambda e: e.name, vars_to_rename))
    vars_to: T.List[str] = list(map(lambda e: e.name, new_vars))
    renaming = dict(zip(vars_fr, vars_to))
    return renaming


def compute_renaming(
    patt: Kore.Pattern, vars_to_avoid: T.List[Kore.EVar]
) -> T.Dict[str, str]:
    return compute_renaming0(
        vars_to_avoid=vars_to_avoid, vars_to_rename=list(free_evars_of_pattern(patt))
    )


def filter_out_predicates(
    phi: Kore.Pattern,
) -> T.Tuple[T.Optional[Kore.Pattern], T.List[Kore.Pattern]]:
    if issubclass(type(phi), Kore.MLPred):
        return None, [phi]
    match phi:
        case Kore.And(sort, left, right):
            lf, ps1 = filter_out_predicates(left)
            rf, ps2 = filter_out_predicates(right)
            if lf is None:
                return rf, (ps1 + ps2)
            if rf is None:
                return lf, (ps1 + ps2)
            return Kore.And(sort, lf, rf), (ps1 + ps2)
        case _:
            return phi, []


def get_predicates(phi: Kore.Pattern) -> T.List[Kore.Pattern]:
    _, preds = filter_out_predicates(phi)
    return preds


def is_bottom(pattern: Kore.Pattern) -> bool:
    match pattern:
        case Kore.Bottom(_):
            return True
    return False


def is_top(pattern: Kore.Pattern) -> bool:
    match pattern:
        case Kore.Top(_):
            return True
    return False


# TODO use make_conjunction
def mapping_to_pattern(
    sort: Kore.Sort, m: T.Mapping[Kore.EVar, Kore.Pattern]
) -> Kore.Pattern:
    result: Kore.Pattern = Kore.Top(sort)
    for lhs, rhs in m.items():
        result = Kore.And(sort, result, Kore.Equals(lhs.sort, sort, lhs, rhs))
    return result
