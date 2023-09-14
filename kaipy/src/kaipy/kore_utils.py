import functools
import typing as T
from itertools import chain, product
import logging

import pyk.kore.syntax as Kore
from pyk.kore.manip import free_occs

import kaipy.predicate_filter as PredicateFilter
import kaipy.BasicKoreUtils as BasicKoreUtils

_LOGGER: T.Final = logging.getLogger(__name__)

def make_conjunction(sort, l: T.Sequence[Kore.Pattern]) -> Kore.Pattern:
    return BasicKoreUtils.make_conjunction(sort, l)

def make_disjunction(sort, l: T.Sequence[Kore.Pattern]) -> Kore.Pattern:
    return BasicKoreUtils.make_disjunction(sort, l)

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


def sentences(definition: Kore.Definition, main_module_name: str) -> T.List[Kore.Sentence]:
    module_names = {main_module_name}.union(
        get_all_recursively_imported_module_names(definition, main_module_name)
    )
    modules = map(lambda name: get_module_by_name(definition, name), module_names)
    sentences: T.List[Kore.Sentence] = []
    for m in modules:
        sentences.extend(m.sentences)
    return sentences

def is_sort_decl(s: Kore.Sentence) -> bool:
    match s:
        case Kore.SortDecl(_,_,_,_):
            return True
    return False


def sort_decls(definition: Kore.Definition, main_module_name: str) -> T.List[Kore.SortDecl]:
    return [s for s in sentences(definition, main_module_name) if is_sort_decl(s)] #type: ignore


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


def rename_vars(renaming: T.Mapping[str, str], phi: Kore.Pattern, total: bool = False) -> Kore.Pattern:
    match phi:
        # The main case
        case Kore.EVar(name, sort):
            if name in renaming:
                return Kore.EVar(renaming[name], sort)
            assert not total
            return Kore.EVar(name, sort)

        # The recursive cases
        case Kore.App(symbol_name, sorts, args):
            return Kore.App(
                symbol_name, sorts, tuple(map(lambda p: rename_vars(renaming, p, total=total), args))
            )
        case Kore.Not(sort, pattern):
            return Kore.Not(sort, rename_vars(renaming, pattern, total=total))
        case Kore.And(sort, left, right):
            return Kore.And(
                sort, rename_vars(renaming, left, total=total), rename_vars(renaming, right, total=total)
            )
        case Kore.Or(sort, left, right):
            return Kore.Or(
                sort, rename_vars(renaming, left, total=total), rename_vars(renaming, right, total=total)
            )
        case Kore.Implies(sort, left, right):
            return Kore.Implies(
                sort, rename_vars(renaming, left, total=total), rename_vars(renaming, right, total=total)
            )
        case Kore.Iff(sort, left, right):
            return Kore.Iff(
                sort, rename_vars(renaming, left, total=total), rename_vars(renaming, right, total=total)
            )
        case Kore.Exists(sort, var, pattern):
            new_dict = dict(renaming)
            new_dict.update({var.name: var.name})
            return Kore.Exists(sort, var, rename_vars(new_dict, pattern, total=total))
        case Kore.Forall(sort, var, pattern):
            new_dict = dict(renaming)
            new_dict.update({var.name: var.name})
            return Kore.Forall(sort, var, rename_vars(new_dict, pattern, total=total))
        # Base cases
        case Kore.Equals(op_sort, sort, left, right):
            return Kore.Equals(
                op_sort, sort, rename_vars(renaming, left, total=total), rename_vars(renaming, right, total=total)
            )
        case Kore.In(op_sort, sort, left, right):
            return Kore.In(
                op_sort, sort, rename_vars(renaming, left, total=total), rename_vars(renaming, right, total=total)
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
            return Kore.Ceil(op_sort, sort, rename_vars(renaming, pattern, total=total))
        case Kore.Floor(op_sort, sort, pattern):
            return Kore.Floor(op_sort, sort, rename_vars(renaming, pattern, total=total))
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

def is_bottom(pattern: Kore.Pattern) -> bool:
    match pattern:
        case Kore.Bottom(_):
            return True
    return False

def any_is_bottom(l: T.Iterable[Kore.Pattern]) -> bool:
    return any([is_bottom(x) for x in l])


def is_top(pattern: Kore.Pattern) -> bool:
    match pattern:
        case Kore.Top(_):
            return True
    return False


def is_evar(pattern: Kore.Pattern) -> bool:
    match pattern:
        case Kore.EVar(_, _):
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


def reverse_renaming(renaming: T.Mapping[str, str]) -> T.Dict[str, str]:
    return {v:k for k,v in renaming.items()}

def or_to_list(phi: Kore.Pattern) -> T.List[Kore.Pattern]:
    match phi:
        case Kore.Or(_, l, r):
            return or_to_list(l) + or_to_list(r)
        case _:
            return [phi]

def and_to_list(phi: Kore.Pattern) -> T.List[Kore.Pattern]:
    match phi:
        case Kore.And(_, l, r):
            return and_to_list(l) + and_to_list(r)
        case _:
            return [phi]


def normalize_pattern(cfg: Kore.Pattern, prefix="V") -> Kore.Pattern:
    vs = list(dict.fromkeys(free_occs_det(cfg))) # We need to eliminate duplicates, https://stackoverflow.com/a/7961390/6209703
    # Different sorts will have different namespaces.
    # This way we avoid clashes of names like `X:SortInt` with `X:SortList`
    #renaming = { v.name : (f"VAR'V{v.sort.name}'{str(i)}") for i,v in enumerate(vs)}
    renaming = { v.name : (f"VAR{prefix}{v.sort.name}X{str(i)}") for i,v in enumerate(vs)}
    return rename_vars(renaming, cfg, total=True)


def let_sort_rec(sort: Kore.Sort, phi: Kore.Pattern) -> Kore.Pattern:
    match phi:
        case Kore.And(_, left, right):
            return Kore.And(sort, let_sort_rec(sort, left), let_sort_rec(sort, right))
        case Kore.Or(_, left, right):
            return Kore.Or(sort, let_sort_rec(sort, left), let_sort_rec(sort, right))
        case Kore.Top(_):
            return Kore.Top(sort)
        case Kore.Bottom(_):
            return Kore.Bottom(sort)
        case Kore.Equals(os, _, left, right):
            return Kore.Equals(os, sort, left, right)
        case Kore.In(os, _, left, right):
            return Kore.In(os, sort, left, right)
        case Kore.Floor(os, _, phi):
            return Kore.Floor(os, sort, phi)
        case Kore.Ceil(os, _, phi):
            return Kore.Ceil(os, sort, phi)
    return phi.with_sort(sort) # type: ignore

def is_predicate_pattern(phi: Kore.Pattern) -> bool:
    if issubclass(type(phi), Kore.MLPred):
        return True

    match phi:
        case Kore.And(_, l, r):
            return is_predicate_pattern(l) and is_predicate_pattern(r)
        case Kore.Or(_, l, r):
            return is_predicate_pattern(l) and is_predicate_pattern(r)
        case Kore.Not(_, phi2):
            return is_predicate_pattern(phi2)

    return False

def get_nonpredicate_part(phi: Kore.Pattern) -> Kore.Pattern | None:
    if is_predicate_pattern(phi):
        return None
    
    match phi:
        case Kore.And(s, l, r):
            fl = get_nonpredicate_part(l)
            fr = get_nonpredicate_part(r)
            if not fl and not fr:
                return None
            if not fl:
                return fr
            if not fr:
                return fl
            return Kore.And(s, fl, fr)
        case Kore.Or(s, l, r):
            fl = get_nonpredicate_part(l)
            fr = get_nonpredicate_part(r)
            if not fl and not fr:
                return None
            if not fl:
                return fr
            if not fr:
                return fl
            return Kore.Or(s, fl, fr)
        case Kore.Not(s, phi2):
            f = get_nonpredicate_part(phi2)
            if not f:
                return None
            return Kore.Not(s, f)

    return phi

def filter_out_unrelated_predicates(evs: T.Set[Kore.EVar], phi: Kore.Pattern) -> Kore.Pattern | None:
    #if not is_predicate_pattern(phi):
    #    return phi

    match phi:
        case Kore.Equals(os, s, l, r):
            if type(l) is Kore.EVar and type(r) is Kore.EVar:
                if l not in evs:
                    return None
                if r not in evs:
                    return None
            elif type(l) is Kore.EVar:
                if l not in evs:
                    return None
            elif type(r) is Kore.EVar:
                if r not in evs:
                    return None

    if issubclass(type(phi), Kore.MLPred):
        if len(free_evars_of_pattern(phi).intersection(evs)) > 0:
            return phi
        return None

    match phi:
        case Kore.And(s, l, r):
            lf = filter_out_unrelated_predicates(evs.union(free_evars_of_pattern(r)), l)
            rf = filter_out_unrelated_predicates(evs.union(free_evars_of_pattern(l)), r)
            if not lf and not rf:
                return None
            if not lf:
                return rf
            if not rf:
                return lf
            return Kore.And(s, lf, rf)
        case Kore.Or(s, l, r):
            lf = filter_out_unrelated_predicates(evs.union(free_evars_of_pattern(r)), l)
            rf = filter_out_unrelated_predicates(evs.union(free_evars_of_pattern(l)), r)
            if not lf and not rf:
                return None
            if not lf:
                return rf
            if not rf:
                return lf
            return Kore.Or(s, lf, rf)
        case Kore.Not(s, phi2):
            f = filter_out_unrelated_predicates(evs, phi2)
            if not f:
                return None
            return Kore.Not(s, f)
    return phi
    #assert False


def cleanup_pattern_new(phi: Kore.Pattern) -> Kore.Pattern:
    nonp = get_nonpredicate_part(phi)
    assert nonp is not None
    evs = free_evars_of_pattern(nonp)
    filtered = filter_out_unrelated_predicates(evs, phi)
    assert filtered is not None
    return filtered


def cleanup_pattern_old(top_sort: Kore.Sort, phi: Kore.Pattern) -> Kore.Pattern:
    main_part, _ = PredicateFilter.filter_out_predicates(phi)
    assert main_part is not None
    fvphi = free_evars_of_pattern(phi)
    eqs, rest = extract_equalities_and_rest_from_witness({v.name for v in fvphi}, phi)
    evs2_p = cleanup_eqs(top_sort, main_part, eqs)
    if rest is None:
        return evs2_p
    return Kore.And(top_sort, rest, evs2_p)

def cleanup_eqs(
    top_sort: Kore.Sort,
    main_part: Kore.Pattern,
    eqs: T.Dict[Kore.EVar, Kore.Pattern],
) -> Kore.Pattern:
    fvs = free_evars_of_pattern(main_part)
    evs2 = {k: v for k, v in eqs.items() if (k in fvs)}
    evs2_p = mapping_to_pattern(top_sort, evs2)
    return evs2_p