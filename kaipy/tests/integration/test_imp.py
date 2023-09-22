import logging
import typing as T
import sys
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
import kaipy.Properties
from kaipy.DefaultAbstractionContext import make_ctx
from kaipy.HeatPreAnalysis import ContextAlias, ContextAliases, pre_analyze
from kaipy.ReachabilitySystem import ReachabilitySystem
from kaipy.domains.FiniteTermDomain import FiniteTerm, FiniteTermDomain
from kaipy.domains.PatternMatchDomain import PatternMatchDomain, PatternMatchDomainElement
from kaipy.domains.BigsumPatternDomain import BigsumPattern, BigsumPatternDomain
from kaipy.domains.ExactTermDomain import ExactTerm, ExactTermDomain
from kaipy.domains.KResultConstraintDomain import KResultConstraint, KResultConstraintDomain
from kaipy.domains.KeepEverythingMapDomain import KeepEverythingMap, KeepEverythingMapDomain
from kaipy.domains.PropertyHubConstraintDomain import PropertyHubElements, PropertyHubConstraintDomain
from kaipy.domains.KeepEverythingConstraintDomain import KeepEverything, KeepEverythingConstraintDomain
from kaipy.domains.BasicMapDomain import BasicMap, BasicMapDomain
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

    def test_propertyhub_domain(
        self,
        reachability_system: ReachabilitySystem
    ):
        md = KeepEverythingMapDomain()
        domain = PropertyHubConstraintDomain(rs=reachability_system, map_domain=md)
        prop1 = Kore.Equals(
            Kore.SortApp('SortBool', ()),
            reachability_system.top_sort,
            KorePrelude.TRUE,
            Kore.App(kaipy.Properties.map_in_keys, (), (KorePrelude.inj(Kore.SortApp('SortInt', ()), KorePrelude.SORT_K_ITEM, KorePrelude.int_dv(5)), Kore.EVar('m', Kore.SortApp('SortMap', ()))))
        )
        a1 = domain.abstract(ctx=make_ctx(), over_variables=set(), constraints=[prop1])
        _LOGGER.warning(f'{a1}')
        c1 = domain.concretize(a1)
        _LOGGER.warning(f'{[p.text for p in c1]}')
        assert c1 == [prop1]
        assert True

    def test_basic_map_domain(
        self,
        reachability_system: ReachabilitySystem,
    ):
        sortid = Kore.SortApp("SortId", ())
        x = Kore.DV(sortid, Kore.String("x"))
        y = Kore.DV(sortid, Kore.String("y"))
        z = Kore.DV(sortid, Kore.String("z"))
        x_kitem = KorePrelude.inj(sortid, KorePrelude.SORT_K_ITEM, x)
        y_kitem = KorePrelude.inj(sortid, KorePrelude.SORT_K_ITEM, y)
        z_kitem = KorePrelude.inj(sortid, KorePrelude.SORT_K_ITEM, z)
        # TODO write a domain that wraps ExactTermDomain and allows injections to SortKItem
        etd = ExactTermDomain(rs=reachability_system, patterns=[
            x_kitem, y_kitem, z_kitem,
        ])
        md = BasicMapDomain(rs=reachability_system, key_domain=etd, value_domain=etd)
        domain = PropertyHubConstraintDomain(rs=reachability_system, map_domain=md)
        prop1 = Kore.Equals(
            Kore.SortApp('SortBool', ()),
            reachability_system.top_sort,
            KorePrelude.TRUE,
            Kore.App(kaipy.Properties.map_in_keys, (), (x_kitem, Kore.EVar('m', Kore.SortApp('SortMap', ()))))
        )
        prop2 = Kore.Equals(
            KorePrelude.SORT_K_ITEM,
            reachability_system.top_sort,
            Kore.App(kaipy.Properties.map_lookup, (), (Kore.EVar('m', Kore.SortApp('SortMap', ())),y_kitem)), z_kitem
        )

        a1 = domain.abstract(ctx=make_ctx(), over_variables=set(), constraints=[prop1, prop2])
        _LOGGER.warning(f'{domain.to_str(a1, indent=0)}')
        concretized1 = domain.concretize(a1)
        assert concretized1 == [prop1,prop2]

    def test_cleanup(
        self,
        reachability_system: ReachabilitySystem
    ):
        concrete_text = r'''\and{SortGeneratedTopCell{}}(Lbl'-LT-'generatedTop'-GT-'{}(Lbl'-LT-'T'-GT-'{}(Lbl'-LT-'k'-GT-'{}(kseq{}(inj{SortStmt{}, SortKItem{}}(Lblint'UndsSClnUnds'IMP-SYNTAX'Unds'Stmt'Unds'Ids{}(Lbl'UndsCommUndsUnds'IMP-SYNTAX'Unds'Ids'Unds'Id'Unds'Ids{}(\dv{SortId{}}("x"), Lbl'UndsCommUndsUnds'IMP-SYNTAX'Unds'Ids'Unds'Id'Unds'Ids{}(\dv{SortId{}}("y"), Lbl'UndsCommUndsUnds'IMP-SYNTAX'Unds'Ids'Unds'Id'Unds'Ids{}(\dv{SortId{}}("z"), Lbl'Stop'List'LBraQuotUndsCommUndsUnds'IMP-SYNTAX'Unds'Ids'Unds'Id'Unds'Ids'QuotRBraUnds'Ids{}()))))), kseq{}(Lbl'Hash'freezer'UndsUndsUnds'IMP-SYNTAX'Unds'Stmt'Unds'Stmt'Unds'Stmt0'Unds'{}(kseq{}(inj{SortStmt{}, SortKItem{}}(Lbl'UndsUndsUnds'IMP-SYNTAX'Unds'Stmt'Unds'Stmt'Unds'Stmt{}(Lbl'UndsEqlsUndsSClnUnds'IMP-SYNTAX'Unds'Stmt'Unds'Id'Unds'AExp{}(\dv{SortId{}}("x"), inj{SortInt{}, SortAExp{}}(\dv{SortInt{}}("1"))), Lbl'UndsUndsUnds'IMP-SYNTAX'Unds'Stmt'Unds'Stmt'Unds'Stmt{}(Lbl'UndsEqlsUndsSClnUnds'IMP-SYNTAX'Unds'Stmt'Unds'Id'Unds'AExp{}(\dv{SortId{}}("y"), Lbl'UndsPlusUndsUnds'IMP-SYNTAX'Unds'AExp'Unds'AExp'Unds'AExp{}(inj{SortInt{}, SortAExp{}}(\dv{SortInt{}}("2")), inj{SortId{}, SortAExp{}}(\dv{SortId{}}("x")))), Lbl'UndsUndsUnds'IMP-SYNTAX'Unds'Stmt'Unds'Stmt'Unds'Stmt{}(Lbl'UndsEqlsUndsSClnUnds'IMP-SYNTAX'Unds'Stmt'Unds'Id'Unds'AExp{}(\dv{SortId{}}("z"), Lbl'UndsPlusUndsUnds'IMP-SYNTAX'Unds'AExp'Unds'AExp'Unds'AExp{}(inj{SortId{}, SortAExp{}}(\dv{SortId{}}("y")), inj{SortInt{}, SortAExp{}}(\dv{SortInt{}}("3")))), Lbl'UndsEqlsUndsSClnUnds'IMP-SYNTAX'Unds'Stmt'Unds'Id'Unds'AExp{}(\dv{SortId{}}("x"), Lbl'UndsPlusUndsUnds'IMP-SYNTAX'Unds'AExp'Unds'AExp'Unds'AExp{}(inj{SortId{}, SortAExp{}}(\dv{SortId{}}("x")), inj{SortId{}, SortAExp{}}(\dv{SortId{}}("z")))))))), dotk{}())), VARREST2 : SortK{}))), VARSTATECELL : SortStateCell{}, VARARGSCELL : SortArgsCell{}), VARGENCOUNTERCELL : SortGeneratedCounterCell{}), \and{SortGeneratedTopCell{}}(\equals{SortKItem{}, SortGeneratedTopCell{}}(VARHERE : SortKItem{}, inj{SortStmt{}, SortKItem{}}(Lbl'UndsUndsUnds'IMP-SYNTAX'Unds'Stmt'Unds'Stmt'Unds'Stmt{}(Lblint'UndsSClnUnds'IMP-SYNTAX'Unds'Stmt'Unds'Ids{}(Lbl'UndsCommUndsUnds'IMP-SYNTAX'Unds'Ids'Unds'Id'Unds'Ids{}(\dv{SortId{}}("x"), Lbl'UndsCommUndsUnds'IMP-SYNTAX'Unds'Ids'Unds'Id'Unds'Ids{}(\dv{SortId{}}("y"), Lbl'UndsCommUndsUnds'IMP-SYNTAX'Unds'Ids'Unds'Id'Unds'Ids{}(\dv{SortId{}}("z"), Lbl'Stop'List'LBraQuotUndsCommUndsUnds'IMP-SYNTAX'Unds'Ids'Unds'Id'Unds'Ids'QuotRBraUnds'Ids{}())))), Lbl'UndsUndsUnds'IMP-SYNTAX'Unds'Stmt'Unds'Stmt'Unds'Stmt{}(Lbl'UndsEqlsUndsSClnUnds'IMP-SYNTAX'Unds'Stmt'Unds'Id'Unds'AExp{}(\dv{SortId{}}("x"), inj{SortInt{}, SortAExp{}}(\dv{SortInt{}}("1"))), Lbl'UndsUndsUnds'IMP-SYNTAX'Unds'Stmt'Unds'Stmt'Unds'Stmt{}(Lbl'UndsEqlsUndsSClnUnds'IMP-SYNTAX'Unds'Stmt'Unds'Id'Unds'AExp{}(\dv{SortId{}}("y"), Lbl'UndsPlusUndsUnds'IMP-SYNTAX'Unds'AExp'Unds'AExp'Unds'AExp{}(inj{SortInt{}, SortAExp{}}(\dv{SortInt{}}("2")), inj{SortId{}, SortAExp{}}(\dv{SortId{}}("x")))), Lbl'UndsUndsUnds'IMP-SYNTAX'Unds'Stmt'Unds'Stmt'Unds'Stmt{}(Lbl'UndsEqlsUndsSClnUnds'IMP-SYNTAX'Unds'Stmt'Unds'Id'Unds'AExp{}(\dv{SortId{}}("z"), Lbl'UndsPlusUndsUnds'IMP-SYNTAX'Unds'AExp'Unds'AExp'Unds'AExp{}(inj{SortId{}, SortAExp{}}(\dv{SortId{}}("y")), inj{SortInt{}, SortAExp{}}(\dv{SortInt{}}("3")))), Lbl'UndsEqlsUndsSClnUnds'IMP-SYNTAX'Unds'Stmt'Unds'Id'Unds'AExp{}(\dv{SortId{}}("x"), Lbl'UndsPlusUndsUnds'IMP-SYNTAX'Unds'AExp'Unds'AExp'Unds'AExp{}(inj{SortId{}, SortAExp{}}(\dv{SortId{}}("x")), inj{SortId{}, SortAExp{}}(\dv{SortId{}}("z")))))))))), \equals{SortK{}, SortGeneratedTopCell{}}(VARREST : SortK{}, VARREST2 : SortK{})))'''
        parser = KoreParser(concrete_text)
        concrete = parser.pattern()
        nonp = KoreUtils.get_nonpredicate_part(concrete)
        assert nonp is not None
        _LOGGER.warning(f"nonp: {reachability_system.kprint.kore_to_pretty(nonp)}")
        cln = KoreUtils.cleanup_pattern_new(concrete)
        _LOGGER.warning(f"cln: {reachability_system.kprint.kore_to_pretty(cln)}")
        assert type(cln) is Kore.App

        sortInt = Kore.SortApp("SortInt", ())
        second_pattern: Kore.Pattern = Kore.And(sortInt, Kore.EVar("X", sortInt), Kore.And(sortInt,
            Kore.Equals(sortInt, sortInt, Kore.DV(sortInt, Kore.String("3")), Kore.EVar("Z", sortInt)),
            Kore.Equals(sortInt, sortInt, Kore.EVar("Z", sortInt), Kore.EVar("X", sortInt)),
        ))
        _LOGGER.warning(f"second: {reachability_system.kprint.kore_to_pretty(second_pattern)}")
        second_cln = KoreUtils.cleanup_pattern_new(second_pattern)
        _LOGGER.warning(f"second_cln: {reachability_system.kprint.kore_to_pretty(second_cln)}")
        assert second_cln.text == second_pattern.text
        

    def test_exact_and_bigsum_pattern_domain(
        self,
        reachability_system: ReachabilitySystem
    ):
        p1: Kore.Pattern = Kore.App('dotk', sorts=(), args=())
        p2: Kore.Pattern = Kore.DV(Kore.SortApp('SortInt', ()), Kore.String("3"))
        p3: Kore.Pattern = KorePrelude.inj(Kore.SortApp('SortInt', ()), Kore.SortApp('SortKItem', ()), p2)
        p4: Kore.Pattern = Kore.App('kseq', (), (p1,p3))
        
        pd_p4 = ExactTermDomain(rs=reachability_system, patterns=[p4])
        assert KoreUtils.is_top(pd_p4.concretize(pd_p4.abstract(ctx=make_ctx(), c=p3)))
        assert p4 == pd_p4.concretize(pd_p4.abstract(ctx=make_ctx(), c=p4))

        pd_p2 = ExactTermDomain(rs=reachability_system, patterns=[p2])
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
        fpd: IAbstractPatternDomain = FiniteTermDomain(rs=reachability_system, pl=[
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

    def test_abstract_concretize_simple(
        self,
        reachability_system: ReachabilitySystem,
        context_aliases: ContextAliases
    ):
        sys.setrecursionlimit(4*10**3)
        input_pattern: Kore.Pattern = reachability_system.kdw.get_input_kore(
            RSTestBase.LANGUAGES / "imp/simple.imp"
        )
        rests = pre_analyze(reachability_system, context_aliases, input_pattern)
        pattern_domain: IAbstractPatternDomain = build_abstract_pattern_domain(
            reachability_system,
            rests,
            input_pattern
        )
        ctx = make_ctx()
        concrete_text = r'''\and{SortGeneratedTopCell{}}(Lbl'-LT-'generatedTop'-GT-'{}(Lbl'-LT-'T'-GT-'{}(Lbl'-LT-'k'-GT-'{}(kseq{}(inj{SortStmt{}, SortKItem{}}(Lbl'UndsUndsUnds'IMP-SYNTAX'Unds'Stmt'Unds'Stmt'Unds'Stmt{}(Lbl'UndsEqlsUndsSClnUnds'IMP-SYNTAX'Unds'Stmt'Unds'Id'Unds'AExp{}(\dv{SortId{}}("x"), inj{SortInt{}, SortAExp{}}(\dv{SortInt{}}("1"))), Lbl'UndsUndsUnds'IMP-SYNTAX'Unds'Stmt'Unds'Stmt'Unds'Stmt{}(Lbl'UndsEqlsUndsSClnUnds'IMP-SYNTAX'Unds'Stmt'Unds'Id'Unds'AExp{}(\dv{SortId{}}("y"), Lbl'UndsPlusUndsUnds'IMP-SYNTAX'Unds'AExp'Unds'AExp'Unds'AExp{}(inj{SortInt{}, SortAExp{}}(\dv{SortInt{}}("2")), inj{SortId{}, SortAExp{}}(\dv{SortId{}}("x")))), Lbl'UndsUndsUnds'IMP-SYNTAX'Unds'Stmt'Unds'Stmt'Unds'Stmt{}(Lbl'UndsEqlsUndsSClnUnds'IMP-SYNTAX'Unds'Stmt'Unds'Id'Unds'AExp{}(\dv{SortId{}}("z"), Lbl'UndsPlusUndsUnds'IMP-SYNTAX'Unds'AExp'Unds'AExp'Unds'AExp{}(inj{SortId{}, SortAExp{}}(\dv{SortId{}}("y")), inj{SortInt{}, SortAExp{}}(\dv{SortInt{}}("3")))), Lbl'UndsEqlsUndsSClnUnds'IMP-SYNTAX'Unds'Stmt'Unds'Id'Unds'AExp{}(\dv{SortId{}}("x"), Lbl'UndsPlusUndsUnds'IMP-SYNTAX'Unds'AExp'Unds'AExp'Unds'AExp{}(inj{SortId{}, SortAExp{}}(\dv{SortId{}}("x")), inj{SortId{}, SortAExp{}}(\dv{SortId{}}("z")))))))), kseq{}(Lbl'Hash'freezer'UndsUndsUnds'IMP-SYNTAX'Unds'Stmt'Unds'Stmt'Unds'Stmt1'Unds'{}(kseq{}(inj{SortStmt{}, SortKItem{}}(VARVSortStmtX0 : SortStmt{}), dotk{}())), dotk{}()))), VARVSortStateCellX1 : SortStateCell{}, Lbl'-LT-'args'-GT-'{}(VARVSortListX2 : SortList{})), Lbl'-LT-'generatedCounter'-GT-'{}(\dv{SortInt{}}("0"))), \equals{SortBool{}, SortGeneratedTopCell{}}(\dv{SortBool{}}("true"), LblisKResult{}(kseq{}(inj{SortStmt{}, SortKItem{}}(VARVSortStmtX0 : SortStmt{}), dotk{}()))))'''
        parser = KoreParser(concrete_text)
        concrete = parser.pattern()
        _LOGGER.warning(f"Input: {reachability_system.kprint.kore_to_pretty(concrete)}")
        a = pattern_domain.abstract(ctx=ctx, c=concrete)
        _LOGGER.warning(f"abstracted: {pattern_domain.to_str(a, 0)}")
        _LOGGER.warning(f"statistics: {pattern_domain.statistics()}")
        c = pattern_domain.concretize(a)
        _LOGGER.warning(f"concretized: {reachability_system.kprint.kore_to_pretty(c)}")
        _LOGGER.warning(f"statistics: {pattern_domain.statistics()}")


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
        _LOGGER.warning(result)
        #si: kaipy.analyzer.StateInfo = states.states_by_id['IMP.assignment']
        #si.print(kprint=reachability_system.kprint, subst_domain=subst_domain)
        #concrete_substitutions = list(si.concrete_substitutions(subst_domain))
        #assert len(concrete_substitutions) == 1
        #assert reachability_system.kprint.kore_to_pretty(concrete_substitutions[0].mapping[Kore.EVar("Var'Unds'DotVar2", Kore.SortApp('SortK', ()))]).strip() == '#freezer___IMP-SYNTAX_Stmt_Stmt_Stmt1_ ( Fresh3:Stmt ~> . ) ~> Fresh2 ~> .'

    def test_rl_num_rules(self, reachability_system: ReachabilitySystem):
        cnt = 0
        for axiom in reachability_system.kdw.rewrite_rules:
            match axiom:
                case Kore.Axiom(_, Kore.Rewrites(_, lhs, _), _):
                    cnt = cnt + 1
        _LOGGER.warning(f"Rewriting rules: {cnt}")
        assert True


    def test_analyze_simple_concrete(
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
