import typing as T
import dataclasses

import pyk.kore.syntax as Kore

import kaipy.kore_utils as KoreUtils
from kaipy.ReachabilitySystem import ReachabilitySystem

@dataclasses.dataclass(frozen=True)
class _RawPatternProjection:
    cfg: Kore.Pattern
    conj: Kore.Pattern
    #info: StateInfo
    st: Kore.Pattern
    #st_renamed: Kore.Pattern
    cfg_renamed: Kore.Pattern
    cfg_renaming: T.Dict[str, str]
    #renaming: T.Dict[str, str]

    def with_conj(self, new_conj: Kore.Pattern) -> "_RawPatternProjection":
        return _RawPatternProjection(
            cfg=self.cfg,
            conj=new_conj,
            st=self.st,
            cfg_renamed=self.cfg_renamed,
            cfg_renaming=self.cfg_renaming
            #st_renamed=self.st_renamed,
            #renaming=self.renaming
        )

def _rename_to_avoid(
    pattern_to_rename: Kore.Pattern,
    pattern_to_avoid: Kore.Pattern
) -> T.Tuple[Kore.Pattern, T.Dict[str, str]]:
    renaming = KoreUtils.compute_renaming0(
        vars_to_avoid=list(KoreUtils.free_evars_of_pattern(pattern_to_avoid)),
        vars_to_rename=list(KoreUtils.free_evars_of_pattern(pattern_to_rename))
    )
    renamed = KoreUtils.rename_vars(
        renaming,
        pattern_to_rename
    )
    return renamed,renaming


def _compute_raw_pattern_projection(
    rs: ReachabilitySystem,
    what: Kore.Pattern,
    to: Kore.Pattern,
) -> _RawPatternProjection:
    what_renamed,renaming = _rename_to_avoid(what, to)
    conj = Kore.And(rs.top_sort, what_renamed, to)
    return _RawPatternProjection(
        cfg=what,
        conj=conj,
        st=to,
        cfg_renamed=what_renamed,
        cfg_renaming=renaming,
        #st_renamed=to_renamed,
        #renaming=renaming,
    )

def _compute_list_of_raw_pattern_projections(
    rs: ReachabilitySystem,
    states: T.List[Kore.Pattern],
    cfg: Kore.Pattern,
) -> T.List[_RawPatternProjection]:
    conjinfos: T.List[_RawPatternProjection] = list()
    for st in states:
        conjinfos.append(
            _compute_raw_pattern_projection(
                rs,
                cfg,
                st,
            )
        )
    return conjinfos

@dataclasses.dataclass
class MatchResult:
    cfg: Kore.Pattern                # what is being matched
    state: Kore.Pattern              # against which the match goes
    renaming: T.Dict[str, str]       # how we renamed the variables of `.state`
    constraints: T.List[Kore.MLPred]

# Guarantees that the i-th position of the result corresponds to the i-th position of `states`
def parallel_match(rs: ReachabilitySystem, cfg: Kore.Pattern, states: T.List[Kore.Pattern]) -> T.List[MatchResult]:
    # list of conjunctions of `cfgs` and renamed `states`
    conjinfos: T.List[_RawPatternProjection] = _compute_list_of_raw_pattern_projections(rs=rs, states=states, cfg=cfg)
    #_LOGGER.warning(f'Simplifying {len(conjinfos)} items at once')
    conjs_simplified = rs.map_simplify([ci.conj for ci in conjinfos])
    #_LOGGER.warning(f'done.')
    conjinfos2: T.List[_RawPatternProjection] = [ci.with_conj(conj2) for ci,conj2 in zip(conjinfos, conjs_simplified)]
    result = [
        MatchResult(
            cfg=ci.cfg,
            state=ci.st,
            renaming=ci.cfg_renaming,
            # A problem occurring here is that `ci.conj` is too simplified:
            # it does not contain predicates that the backend is able to deduce are always true.
            # For example, we might have a state:
            # `</k> someValue() ~> #freezer() ...</k>`
            # and a cooling rule
            # ```
            # <k> (X:Stmt ~> #freezer()) => something(...) ...</k>
            # \and true = isKResult(X ~> .)
            # ```
            # , which yields a match `X \equiv someValue()`
            # but the fact that `isKResult(X ~> .)` is forgotten.
            # Therefore, we have to read the predicates of the state
            # and add them to the list of predicates derived from the conjunction.
            constraints=([ci.conj] if KoreUtils.is_bottom(ci.conj) else KoreUtils.get_predicates(ci.conj)+KoreUtils.get_predicates(ci.st_renamed)) #type: ignore
        )
        for ci in conjinfos2
    ]
    return result

