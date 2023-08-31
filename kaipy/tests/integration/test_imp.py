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

from kaipy.HeatPreAnalysis import ContextAlias, ContextAliases, pre_analyze
from kaipy.ReachabilitySystem import ReachabilitySystem
from kaipy.domains.BigsumPatternDomain import BigsumPattern, BigsumPatternDomain
from kaipy.domains.ExactPatternDomain import ExactPattern, ExactPatternDomain
from kaipy.testing.testingbase import RSTestBase
from kaipy.DefaultAbstractionContext import make_ctx
from kaipy.DefaultPatternDomain import build_abstract_pattern_domain

import kaipy.DefaultPatternDomain
import kaipy.analyzer

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
    ):
        input_pattern: Kore.Pattern = reachability_system.kdw.get_input_kore(
            RSTestBase.LANGUAGES / filename
        )

        rests = pre_analyze(reachability_system, context_aliases, input_pattern)
        pattern_domain: IAbstractPatternDomain = build_abstract_pattern_domain(
            reachability_system,
            rests,
            input_pattern
        )
        result = kaipy.analyzer.analyze(
            reachability_system,
            pattern_domain=pattern_domain,
            initial_configuration=input_pattern,
        )
        return result

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
