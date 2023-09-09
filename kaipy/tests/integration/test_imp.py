import logging
import typing as T
from pathlib import Path
from immutabledict import immutabledict

import pyk.kore.prelude as KorePrelude
import pyk.kore.rpc as KoreRpc
import pyk.kore.syntax as Kore
import pytest
from pyk.kore.parser import KoreParser
from pyk.ktool.kprint import KPrint
from pyk.testing._kompiler import KompiledTest

import kaipy.kore_utils as KoreUtils
import kaipy.rs_utils as RSUtils

from kaipy.interfaces.IAbstractSubstitutionDomain import IAbstractSubstitutionDomain
from kaipy.interfaces.IAbstractPatternDomain import IAbstractPatternDomain

from kaipy.AbstractionContext import AbstractionContext
from kaipy.DefaultAbstractionContext import make_ctx
from kaipy.HeatPreAnalysis import ContextAlias, ContextAliases, pre_analyze
from kaipy.ReachabilitySystem import ReachabilitySystem
from kaipy.domains.FinitePatternDomain import FinitePattern, FinitePatternDomain
from kaipy.domains.PatternMatchDomain import PatternMatchDomain, PatternMatchDomainElement
from kaipy.domains.BigsumPatternDomain import BigsumPattern, BigsumPatternDomain
from kaipy.domains.ExactPatternDomain import ExactPattern, ExactPatternDomain
from kaipy.domains.KResultConstraintDomain import KResultConstraint, KResultConstraintDomain
from kaipy.domains.KeepEverythingConstraintDomain import KeepEverything, KeepEverythingConstraintDomain
from kaipy.testing.testingbase import RSTestBase
from kaipy.DefaultAbstractionContext import make_ctx
from kaipy.DefaultPatternDomain import build_abstract_pattern_domain

import kaipy.DefaultPatternDomain
from kaipy.analyzer import AnalysisResult, analyze

_LOGGER: T.Final = logging.getLogger(__name__)


class MyTest(RSTestBase):
    MYTEST_CONTEXT_ALIAS_BEFORE: T.ClassVar[Path]
    MYTEST_CONTEXT_ALIAS_AFTER: T.ClassVar[Path]

    def _pattern_from_file(self, filename: Path) -> Kore.Pattern:
        with open(filename, mode="r") as fr:
            text = fr.read()
        parser = KoreParser(text)
        return parser.pattern()

    @pytest.fixture
    def context_aliases(self) -> ContextAliases:
        before = self._pattern_from_file(self.MYTEST_CONTEXT_ALIAS_BEFORE)
        after = self._pattern_from_file(self.MYTEST_CONTEXT_ALIAS_AFTER)
        return ContextAliases((ContextAlias(before, after),))


class TestImp(MyTest):
    KOMPILE_MAIN_FILE = RSTestBase.LANGUAGES / "imp/imp.k"
    KOMPILE_BACKEND = "haskell"
    MYTEST_CONTEXT_ALIAS_BEFORE = RSTestBase.LANGUAGES / "imp/context_alias_before.kore"
    MYTEST_CONTEXT_ALIAS_AFTER = RSTestBase.LANGUAGES / "imp/context_alias_after.kore"

    # def test_hello(self, kompiled_definition_wrapper: KompiledDefinitionWrapper):
    #     print(kompiled_definition_wrapper.main_module_name)
    #     assert True

    # def test_heatcoolonly_has_fewer_rules(
    #     self, reachability_system: ReachabilitySystem
    # ):
    #     heat_cool_only_def: KompiledDefinitionWrapper = (
    #         reachability_system.kdw.heat_cool_only
    #     )
    #     # We check that Imp has some non-heat or non-cool rules in the main module
    #     assert len(heat_cool_only_def.rewrite_rules) < len(
    #         reachability_system.kdw.rewrite_rules
    #     )

    def test_heatcoolonly(
        self,
        reachability_system: ReachabilitySystem,
        context_aliases: ContextAliases,
        request,
    ):
        input_pattern: Kore.Pattern = reachability_system.kdw.get_input_kore(
            RSTestBase.LANGUAGES / "imp/sum.imp"
        )

        rests = pre_analyze(reachability_system, context_aliases, input_pattern)

        #print("Rests:")
        #for i, a_rest in enumerate(rests):
        #    _LOGGER.warning(f"{i}.text: {a_rest.text}")
        #    _LOGGER.warning(f"{i}: {reachability_system.kprint.kore_to_pretty(a_rest)}")
        
        rests_pretty: T.List[str] = [reachability_system.kprint.kore_to_pretty(a_rest).strip() for a_rest in rests]
        # 0
        assert "#freezer___IMP-SYNTAX_Stmt_Stmt_Stmt0_ ( n = getArg ( 0 ) ; sum = 0 ; while ( ! n <= 0 ) { sum = sum + n ; n = n + - 1 ; } ~> . ) ~> VARREST2 ~> ." in rests_pretty
        # 10
        assert "#freezer_+__IMP-SYNTAX_AExp_AExp_AExp1_ ( HOLE:AExp ~> . ) ~> #freezer_=_;_IMP-SYNTAX_Stmt_Id_AExp1_ ( sum ~> . ) ~> #freezer___IMP-SYNTAX_Stmt_Stmt_Stmt0_ ( n = n + - 1 ; ~> . ) ~> VARREST2 ~> ." in rests_pretty
        # 12
        assert "#freezer_=_;_IMP-SYNTAX_Stmt_Id_AExp1_ ( n ~> . ) ~> #freezer___IMP-SYNTAX_Stmt_Stmt_Stmt1_ ( HOLE2:Stmt ~> . ) ~> VARREST2 ~> ." in rests_pretty

        assert len(rests) == 17

    def test_sort_decl(
        self,
        reachability_system: ReachabilitySystem
    ):
        ss = reachability_system.kdw.user_declared_sorts
        print(ss)
        assert set(ss) == set(['SortKItem', 'SortVoidVal', 'SortAExp', 'SortBlock', 'SortBExp', 'SortPgm', 'SortStmt', 'SortValue'])

    def test_exact_and_bigsum_pattern_domain(
        self,
        reachability_system: ReachabilitySystem
    ):
        p1: Kore.Pattern = Kore.App('dotk', sorts=(), args=())
        p2: Kore.Pattern = Kore.DV(Kore.SortApp('SortInt', ()), Kore.String("3"))
        p3: Kore.Pattern = KorePrelude.inj(Kore.SortApp('SortInt', ()), Kore.SortApp('SortKItem', ()), p2)
        p4: Kore.Pattern = Kore.App('kseq', (), (p1,p3))
        
        pd_p4 = ExactPatternDomain(rs=reachability_system, patterns=[p4])
        assert KoreUtils.is_top(pd_p4.concretize(pd_p4.abstract(ctx=make_ctx(), c=p3)))
        assert p4 == pd_p4.concretize(pd_p4.abstract(ctx=make_ctx(), c=p4))

        pd_p2 = ExactPatternDomain(rs=reachability_system, patterns=[p2])
        pd_bigsum = BigsumPatternDomain(rs=reachability_system, domains=[pd_p4, pd_p2])
        assert KoreUtils.is_top(pd_bigsum.concretize(pd_bigsum.abstract(ctx=make_ctx(), c=p3)))
        assert p4 == pd_bigsum.concretize(pd_bigsum.abstract(ctx=make_ctx(), c=p4))
        assert p2 == pd_bigsum.concretize(pd_bigsum.abstract(ctx=make_ctx(), c=p2))

    def _analyze_file(
        self,
        reachability_system: ReachabilitySystem,
        context_aliases: ContextAliases,
        filename: str,
    ) -> AnalysisResult:
        input_pattern: Kore.Pattern = reachability_system.kdw.get_input_kore(
            RSTestBase.LANGUAGES / filename
        )

        rests = pre_analyze(reachability_system, context_aliases, input_pattern)
        pattern_domain: IAbstractPatternDomain = build_abstract_pattern_domain(
            reachability_system,
            rests,
            input_pattern
        )
        result = analyze(
            reachability_system,
            pattern_domain=pattern_domain,
            initial_configuration=input_pattern,
        )
        _LOGGER.warning(f"abstract: {pattern_domain.to_str(result.reachable_configurations, indent=0)}")
        concrete_reachable_configurations = pattern_domain.concretize(result.reachable_configurations)
        _LOGGER.warning(reachability_system.kprint.kore_to_pretty(concrete_reachable_configurations))
        return result
    
    def test_finitepd_cooperation(
        self,
        reachability_system: ReachabilitySystem,
        context_aliases : ContextAliases
    ):
        pat1 = Kore.App(symbol="Lbl'Hash'freezer'UndsPlusUndsUnds'IMP-SYNTAX'Unds'AExp'Unds'AExp'Unds'AExp1'Unds'", sorts=(), args=(Kore.App('kseq', (), (Kore.EVar('HOLE', Kore.SortApp('SortKItem', ())),KorePrelude.DOTK)),))
        pat2 = Kore.App(symbol="Lbl'Hash'freezer'UndsPlusUndsUnds'IMP-SYNTAX'Unds'AExp'Unds'AExp'Unds'AExp1'Unds'", sorts=(), args=(Kore.App('kseq', (), (Kore.EVar('XYZ', Kore.SortApp('SortKItem', ())),KorePrelude.DOTK)),))
        ctx = make_ctx()
        fpd: IAbstractPatternDomain = FinitePatternDomain(rs=reachability_system, pl=[
            pat1,
        ])
        a = fpd.abstract(ctx=ctx, c=pat2)
        concretized = fpd.concretize(a)
        #print(a)
        #print(concretized)
        #print(ctx.broadcast_channel.constraints)
        match concretized:
            case Kore.App("Lbl'Hash'freezer'UndsPlusUndsUnds'IMP-SYNTAX'Unds'AExp'Unds'AExp'Unds'AExp1'Unds'", (), (Kore.App('kseq', (), (ev1, KorePrelude.DOTK)),)):
                #print(ev1)
                match ctx.broadcast_channel.constraints:
                    case [Kore.Equals(_, _, ev1, Kore.EVar('XYZ', Kore.SortApp('SortKItem', ())))]:
                        assert True
                    case [Kore.Equals(_, _, Kore.EVar('XYZ', Kore.SortApp('SortKItem', ())), ev1)]:
                        assert True
                    case _:
                        assert False
                assert True
            case _:
                assert False
        assert True

    def test_dotk(
        self,
        reachability_system: ReachabilitySystem,
        context_aliases : ContextAliases
    ):
        input_pattern: Kore.Pattern = reachability_system.kdw.get_input_kore(
            RSTestBase.LANGUAGES / "imp/very-simple.imp"
        )

        rests = pre_analyze(reachability_system, context_aliases, input_pattern)
        pattern_domain = build_abstract_pattern_domain(
            reachability_system,
            rests,
            input_pattern
        )
        ctx = make_ctx()
        #concrete_text = r'''Lbl'-LT-'generatedTop'-GT-'{}(Lbl'-LT-'T'-GT-'{}(Lbl'-LT-'k'-GT-'{}(kseq{}(inj{SortStmt{}, SortKItem{}}(Lblint'UndsSClnUnds'IMP-SYNTAX'Unds'Stmt'Unds'Ids{}(Lbl'Stop'List'LBraQuotUndsCommUndsUnds'IMP-SYNTAX'Unds'Ids'Unds'Id'Unds'Ids'QuotRBraUnds'Ids{}())), kseq{}(Lbl'Hash'freezer'UndsUndsUnds'IMP-SYNTAX'Unds'Stmt'Unds'Stmt'Unds'Stmt0'Unds'{}(kseq{}(inj{SortStmt{}, SortKItem{}}(Lbl'UndsEqlsUndsSClnUnds'IMP-SYNTAX'Unds'Stmt'Unds'Id'Unds'AExp{}(\dv{SortId{}}("x"), inj{SortInt{}, SortAExp{}}(\dv{SortInt{}}("3")))), dotk{}())), dotk{}()))), Lbl'-LT-'state'-GT-'{}(Lbl'UndsPipe'-'-GT-Unds'{}(inj{SortId{}, SortKItem{}}(\dv{SortId{}}("x")), inj{SortInt{}, SortKItem{}}(\dv{SortInt{}}("0")))), Lbl'-LT-'args'-GT-'{}(VARVSortListX0 : SortList{})), Lbl'-LT-'generatedCounter'-GT-'{}(\dv{SortInt{}}("0")))'''
        concrete_text = r'''Lbl'-LT-'generatedTop'-GT-'{}(Lbl'-LT-'T'-GT-'{}(Lbl'-LT-'k'-GT-'{}(kseq{}(inj{SortStmt{}, SortKItem{}}(Lblint'UndsSClnUnds'IMP-SYNTAX'Unds'Stmt'Unds'Ids{}(Lbl'Stop'List'LBraQuotUndsCommUndsUnds'IMP-SYNTAX'Unds'Ids'Unds'Id'Unds'Ids'QuotRBraUnds'Ids{}())), kseq{}(Lbl'Hash'freezer'UndsUndsUnds'IMP-SYNTAX'Unds'Stmt'Unds'Stmt'Unds'Stmt0'Unds'{}(kseq{}(inj{SortStmt{}, SortKItem{}}(Lbl'UndsEqlsUndsSClnUnds'IMP-SYNTAX'Unds'Stmt'Unds'Id'Unds'AExp{}(\dv{SortId{}}("x"), inj{SortInt{}, SortAExp{}}(\dv{SortInt{}}("3")))), dotk{}())), dotk{}()))), Lbl'-LT-'state'-GT-'{}(Lbl'UndsPipe'-'-GT-Unds'{}(inj{SortId{}, SortKItem{}}(\dv{SortId{}}("x")), inj{SortInt{}, SortKItem{}}(\dv{SortInt{}}("0")))), Lbl'-LT-'args'-GT-'{}(VARVSortListX0 : SortList{})), Lbl'-LT-'generatedCounter'-GT-'{}(\dv{SortInt{}}("0")))'''
        parser = KoreParser(concrete_text)
        concrete = parser.pattern()
        #_LOGGER.warning(f"concrete: {reachability_system.kprint.kore_to_pretty(concrete)}")
        a = pattern_domain.abstract(ctx=ctx, c=concrete)
        _LOGGER.warning(f"a: {pattern_domain.to_str(a, indent=0)}")
        #assert a.
        concretized = pattern_domain.concretize(a)
        _LOGGER.warning(f"concretized: {reachability_system.kprint.kore_to_pretty(concretized)}")
        

    def test_kresult_cooperation(
        self,
        reachability_system: ReachabilitySystem,
        context_aliases : ContextAliases
    ):
        input_pattern: Kore.Pattern = reachability_system.kdw.get_input_kore(
            RSTestBase.LANGUAGES / "imp/very-simple.imp"
        )

        rests = pre_analyze(reachability_system, context_aliases, input_pattern)
        pattern_domain = build_abstract_pattern_domain(
            reachability_system,
            rests,
            input_pattern
        )
        ctx = make_ctx()
        concrete_text = r'''\and{SortGeneratedTopCell{}}(Lbl'-LT-'generatedTop'-GT-'{}(Lbl'-LT-'T'-GT-'{}(Lbl'-LT-'k'-GT-'{}(kseq{}(inj{SortStmt{}, SortKItem{}}(Lbl'UndsEqlsUndsSClnUnds'IMP-SYNTAX'Unds'Stmt'Unds'Id'Unds'AExp{}(\dv{SortId{}}("x"), inj{SortInt{}, SortAExp{}}(\dv{SortInt{}}("3")))), kseq{}(Lbl'Hash'freezer'UndsUndsUnds'IMP-SYNTAX'Unds'Stmt'Unds'Stmt'Unds'Stmt1'Unds'{}(kseq{}(inj{SortStmt{}, SortKItem{}}(VARVSortStmtX0 : SortStmt{}), dotk{}())), VARVSortKX1 : SortK{}))), VARVSortStateCellX2 : SortStateCell{}, Lbl'-LT-'args'-GT-'{}(VARVSortListX3 : SortList{})), Lbl'-LT-'generatedCounter'-GT-'{}(\dv{SortInt{}}("0"))), \equals{SortBool{}, SortGeneratedTopCell{}}(\dv{SortBool{}}("true"), LblisKResult{}(kseq{}(inj{SortStmt{}, SortKItem{}}(VARVSortStmtX0 : SortStmt{}), dotk{}()))))'''
        parser = KoreParser(concrete_text)
        concrete = parser.pattern()
        #_LOGGER.warning(f"concrete: {reachability_system.kprint.kore_to_pretty(concrete)}")
        a = pattern_domain.abstract(ctx=ctx, c=concrete)
        _LOGGER.warning(f"a: {pattern_domain.to_str(a, indent=0)}")
        #assert a.
        concretized = pattern_domain.concretize(a)
        #_LOGGER.warning(f"concretized_text: {concretized.text}")
        assert concretized.text == r'''\and{SortGeneratedTopCell{}}(Lbl'-LT-'generatedTop'-GT-'{}(Lbl'-LT-'T'-GT-'{}(Lbl'-LT-'k'-GT-'{}(kseq{}(inj{SortStmt{}, SortKItem{}}(Lbl'UndsEqlsUndsSClnUnds'IMP-SYNTAX'Unds'Stmt'Unds'Id'Unds'AExp{}(\dv{SortId{}}("x"), inj{SortInt{}, SortAExp{}}(\dv{SortInt{}}("3")))), kseq{}(Lbl'Hash'freezer'UndsUndsUnds'IMP-SYNTAX'Unds'Stmt'Unds'Stmt'Unds'Stmt1'Unds'{}(kseq{}(inj{SortStmt{}, SortKItem{}}(VARZ33SortStmtX0 : SortStmt{}), dotk{}())), VARZ33SortKX1 : SortK{}))), Lbl'-LT-'state'-GT-'{}(VARZ33SortMapX2 : SortMap{}), Lbl'-LT-'args'-GT-'{}(VARZ33SortListX3 : SortList{})), Lbl'-LT-'generatedCounter'-GT-'{}(\dv{SortInt{}}("0"))), \equals{SortBool{}, SortGeneratedTopCell{}}(\dv{SortBool{}}("true"), LblisKResult{}(kseq{}(inj{SortStmt{}, SortKItem{}}(VARZ33SortStmtX0 : SortStmt{}), dotk{}()))))'''
        #_LOGGER.warning(f"concretized: {reachability_system.kprint.kore_to_pretty(concretized)}")

    def test_kresult_constraint_domain(
        self,
        reachability_system: ReachabilitySystem,
        context_aliases : ContextAliases
    ):
        sortInt = Kore.SortApp("SortInt", ())
        x1 = Kore.EVar("x1", sortInt)
        domain = KResultConstraintDomain(rs=reachability_system)
        ctx = make_ctx()
        concrete_constraint = domain._mk_isKResult_pattern(x1, reachability_system.top_sort)
        a = domain.abstract(ctx=ctx, over_variables={x1}, constraints=[concrete_constraint])
        assert x1 in a.kresult_vars
        c = domain.concretize(a=a)
        assert c == [concrete_constraint]
        x2 = Kore.EVar("x2", sortInt)
        x1_eq_x2 = Kore.Equals(sortInt, sortInt, x1, x2)
        a2 = domain.refine(ctx=ctx, a=a, constraints=[x1_eq_x2])
        assert x1 in a2.kresult_vars
        assert x2 in a2.kresult_vars


    def test_patternmatch_constraint_domain(
        self,
        reachability_system: ReachabilitySystem,
        context_aliases : ContextAliases
    ):
        sortKItem = Kore.SortApp("SortKItem", ())
        sortInt = Kore.SortApp("SortInt", ())
        x1_kitem = Kore.EVar("x1", sortKItem)
        x2_int = Kore.EVar("x2", sortInt)
        y1_k = Kore.EVar("y1", KorePrelude.SORT_K)

        underlying_domain = KeepEverythingConstraintDomain()
        st1 = Kore.App('kseq', (), (x1_kitem,y1_k))
        st1_constrained = Kore.And(KorePrelude.SORT_K, st1, Kore.Not(KorePrelude.SORT_K, Kore.Equals(sortKItem, KorePrelude.SORT_K, x1_kitem, KorePrelude.inj(sortInt, sortKItem, x2_int))))
        pm_domain = PatternMatchDomain(
            rs=reachability_system,
            underlying_domains=[underlying_domain],
            states=[(st1,"only")])
        #print(pm_domain)
        ctx = make_ctx()
        a1 = pm_domain.abstract(ctx=ctx, c=st1_constrained)
        #print(a1)
        #print(f"a: {pm_domain.to_str(a1, indent=0)}")
        #print(f"renaming: {a1.renaming}")
        c1 = pm_domain.concretize(a1)
        #_LOGGER.warning(c1.text)
        match c1:
            #case Kore.And(_, Kore.App('kseq', _, (Kore.EVar(_, _), Kore.EVar(_, _))), Kore.And(_, _, Kore.Not(_, Kore.Equals(_, _, _, _)))):
            case Kore.And(_, Kore.App('kseq', _, (Kore.EVar(_, _), Kore.EVar(_, _))), Kore.Not(_, Kore.Equals(_, _, _, _))):
                assert True
            case _:
                assert False

    def test_analyze_very_simple(
        self,
        reachability_system: ReachabilitySystem,
        context_aliases: ContextAliases
    ):
        result = self._analyze_file(
            reachability_system=reachability_system,
            context_aliases=context_aliases,
            filename="imp/very-simple.imp"
        )
        print(result)
        #si: kaipy.analyzer.StateInfo = states.states_by_id['IMP.assignment']
        #si.print(kprint=reachability_system.kprint, subst_domain=subst_domain)
        #concrete_substitutions = list(si.concrete_substitutions(subst_domain))
        #assert len(concrete_substitutions) == 1
        #assert reachability_system.kprint.kore_to_pretty(concrete_substitutions[0].mapping[Kore.EVar("Var'Unds'DotVar2", Kore.SortApp('SortK', ()))]).strip() == '#freezer___IMP-SYNTAX_Stmt_Stmt_Stmt1_ ( Fresh3:Stmt ~> . ) ~> Fresh2 ~> .'

    def test_analyze_simple(
        self,
        reachability_system: ReachabilitySystem,
        context_aliases: ContextAliases
    ):
        result = self._analyze_file(
            reachability_system=reachability_system,
            context_aliases=context_aliases,
            filename="imp/simple.imp"
        )
        print(result)

    def test_analyze_simple_symbolic(
        self,
        reachability_system: ReachabilitySystem,
        context_aliases: ContextAliases
    ):
        result = self._analyze_file(
            reachability_system=reachability_system,
            context_aliases=context_aliases,
            filename="imp/simple-symbolic.imp"
        )
        print(result)

    def test_analyze_sum(
        self, reachability_system: ReachabilitySystem, context_aliases: ContextAliases
    ):
        result = self._analyze_file(
            reachability_system=reachability_system,
            context_aliases=context_aliases,
            filename="imp/sum.imp"
        )
        print(result)

    def test_simplify_kresult_3(self, reachability_system: ReachabilitySystem):
        krterm = Kore.App(
            "LblisKResult",
            (),
            (
                KorePrelude.kseq(
                    [
                        KorePrelude.inj(
                            KorePrelude.INT,
                            KorePrelude.SORT_K_ITEM,
                            KorePrelude.int_dv(3),
                        ),
                    ]
                ),
            ),
        )

        print(f"krterm: {reachability_system.kprint.kore_to_pretty(krterm)}")
        simp = reachability_system.kcs.client.simplify(krterm)[0]
        print(f"simplified: {reachability_system.kprint.kore_to_pretty(simp)}")

        input_pattern = Kore.Equals(
            KorePrelude.BOOL,
            KorePrelude.SORT_K_ITEM,
            KorePrelude.TRUE,
            krterm,
        )
        print(
            f"input_pattern: {reachability_system.kprint.kore_to_pretty(input_pattern)}"
        )
        simp = reachability_system.kcs.client.simplify(input_pattern)[0]
        print(f"simplified: {reachability_system.kprint.kore_to_pretty(simp)}")
        assert type(simp) is Kore.Top
