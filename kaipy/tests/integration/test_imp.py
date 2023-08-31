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
from kaipy.HeatPreAnalysis import ContextAlias, ContextAliases, pre_analyze
from kaipy.ReachabilitySystem import ReachabilitySystem
from kaipy.domains.BigsumPatternDomain import BigsumPattern, BigsumPatternDomain
from kaipy.domains.ExactPatternDomain import ExactPattern, ExactPatternDomain
from kaipy.testing.testingbase import RSTestBase

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
        self, reachability_system: ReachabilitySystem, context_aliases: ContextAliases
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
        assert set(ss) == set(['SortVoidVal', 'SortAExp', 'SortBlock', 'SortBExp', 'SortPgm', 'SortStmt', 'SortValue'])

    def test_exact_and_bigsum_pattern_domain(
        self,
        reachability_system: ReachabilitySystem
    ):
        p1: Pattern = Kore.App('dotk', sorts=(), args=())
        p2: Pattern = Kore.DV(Kore.SortApp('SortInt', ()), "3")
        p3: Pattern = KorePrelude.inj(Kore.SortApp('SortInt', ()), Kore.SortApp('SortKItem', ()), p2)
        p4: Pattern = Kore.App('kseq', (), (p1,p3))
        
        pd_p4 = ExactPatternDomain(rs=reachability_system, patterns=[p4])
        assert KoreUtils.is_top(pd_p4.concretize(pd_p4.abstract(p3)))
        assert p4 == pd_p4.concretize(pd_p4.abstract(p4))

        pd_p2 = ExactPatternDomain(rs=reachability_system, patterns=[p2])
        pd_bigsum = BigsumPatternDomain(rs=reachability_system, domains=[pd_p4, pd_p2])
        assert KoreUtils.is_top(pd_bigsum.concretize(pd_bigsum.abstract(p3)))
        assert p4 == pd_bigsum.concretize(pd_bigsum.abstract(p4))
        assert p2 == pd_bigsum.concretize(pd_bigsum.abstract(p2))

    def test_analyze_very_simple(
        self,
        reachability_system: ReachabilitySystem,
        context_aliases: ContextAliases
    ):
        input_pattern: Kore.Pattern = reachability_system.kdw.get_input_kore(
            RSTestBase.LANGUAGES / "imp/very-simple.imp"
        )

        rests = pre_analyze(reachability_system, context_aliases, input_pattern)
        subst_domain: IAbstractSubstitutionDomain = kaipy.DefaultSubstitutionDomain.build_abstract_substitution_domain(
            reachability_system,
            rests,
            input_pattern
        )
        states = kaipy.analyzer.analyze(
            reachability_system,
            subst_domain=subst_domain,
            initial_configuration=input_pattern,
        )
        si: kaipy.analyzer.StateInfo = states.states_by_id['IMP.assignment']
        si.print(kprint=reachability_system.kprint, subst_domain=subst_domain)
        concrete_substitutions = list(si.concrete_substitutions(subst_domain))
        assert len(concrete_substitutions) == 1
        assert reachability_system.kprint.kore_to_pretty(concrete_substitutions[0].mapping[Kore.EVar("Var'Unds'DotVar2", Kore.SortApp('SortK', ()))]).strip() == '#freezer___IMP-SYNTAX_Stmt_Stmt_Stmt1_ ( Fresh3:Stmt ~> . ) ~> Fresh2 ~> .'

    def test_analyze_simple(
        self,
        reachability_system: ReachabilitySystem,
        context_aliases: ContextAliases
    ):
        input_pattern: Kore.Pattern = reachability_system.kdw.get_input_kore(
            RSTestBase.LANGUAGES / "imp/simple.imp"
        )

        rests = pre_analyze(reachability_system, context_aliases, input_pattern)
        subst_domain: IAbstractSubstitutionDomain = kaipy.DefaultSubstitutionDomain.build_abstract_substitution_domain(
            reachability_system,
            rests,
            input_pattern
        )
        states = kaipy.analyzer.analyze(
            reachability_system,
            subst_domain=subst_domain,
            initial_configuration=input_pattern,
        )
        si: kaipy.analyzer.StateInfo = states.states_by_id['IMP.assignment']
        si.print(kprint=reachability_system.kprint, subst_domain=subst_domain)
        concrete_substitutions = list(si.concrete_substitutions(subst_domain))
        assert len(concrete_substitutions) == 4
        assert any([
            reachability_system.kprint.kore_to_pretty(
                s.mapping.get(Kore.EVar("Var'Unds'DotVar2", Kore.SortApp('SortK', ())))
            ).strip() == '#freezer___IMP-SYNTAX_Stmt_Stmt_Stmt0_ ( y = 2 + x ; z = y + 3 ; x = x + z ; ~> . ) ~> #freezer___IMP-SYNTAX_Stmt_Stmt_Stmt1_ ( Fresh3:Stmt ~> . ) ~> Fresh2 ~> .'
            for s in concrete_substitutions
        ])

    def test_analyze_simple_symbolic(
        self,
        reachability_system: ReachabilitySystem,
        context_aliases: ContextAliases
    ):
        input_pattern: Kore.Pattern = reachability_system.kdw.get_input_kore(
            RSTestBase.LANGUAGES / "imp/simple-symbolic.imp"
        )

        rests = pre_analyze(reachability_system, context_aliases, input_pattern)
        subst_domain: IAbstractSubstitutionDomain = kaipy.DefaultSubstitutionDomain.build_abstract_substitution_domain(
            reachability_system,
            rests,
            input_pattern
        )
        states = kaipy.analyzer.analyze(
            reachability_system,
            subst_domain=subst_domain,
            initial_configuration=input_pattern,
        )
        si: kaipy.analyzer.StateInfo = states.states_by_id['IMP.assignment']
        si.print(kprint=reachability_system.kprint, subst_domain=subst_domain)
        #concrete_substitutions = list(si.concrete_substitutions(subst_domain))

    def test_analyze(
        self, reachability_system: ReachabilitySystem, context_aliases: ContextAliases
    ):
        reachability_system.stats.reset()
        input_pattern: Kore.Pattern = reachability_system.kdw.get_input_kore(
            RSTestBase.LANGUAGES / "imp/sum.imp"
        )

        rests = pre_analyze(reachability_system, context_aliases, input_pattern)
        subst_domain: IAbstractSubstitutionDomain = kaipy.DefaultSubstitutionDomain.build_abstract_substitution_domain(
            reachability_system,
            rests,
            input_pattern
        )
        states = kaipy.analyzer.analyze(
            reachability_system,
            subst_domain=subst_domain,
            initial_configuration=input_pattern,
        )
        _LOGGER.info(reachability_system.stats.dict)
        states.states_by_id['IMP.assignment'].print(kprint=reachability_system.kprint, subst_domain=subst_domain)
        #states.print(kprint=reachability_system.kprint, subst_domain=subst_domain)
        #assert(False) # To print stuff

    # def test_execute_var(self, reachability_system: ReachabilitySystem):
    #     #x = Kore.EVar("VARX", KorePrelude.SORT_K_ITEM)
    #     #x_k: Kore.Pattern = KorePrelude.kseq([x])
    #     x_k = Kore.EVar("VARX", KorePrelude.SORT_K)
    #     er = reachability_system.kcs.client.execute(x_k, max_depth=1)
    #     print(er)
    #     assert False

    # def test_simplify_kresult_kitem(self, reachability_system: ReachabilitySystem):
    #     x = Kore.EVar("VARX", KorePrelude.SORT_K_ITEM)
    #     #x_k = KorePrelude.inj(KorePrelude.SORT_K_ITEM, KorePrelude.SORT_K, x)
    #     x_k = KorePrelude.kseq([x])
    #     input_pattern = Kore.And(
    #         KorePrelude.SORT_K_ITEM,
    #         x,
    #         Kore.Equals(
    #             KorePrelude.BOOL,
    #             KorePrelude.SORT_K_ITEM,
    #             KorePrelude.TRUE,
    #             Kore.App("LblisKResult", (), (x_k,)),
    #         ),
    #     )
    #     # input_pattern = Kore.And(KorePrelude.SORT_K_ITEM, input_pattern, Kore.Equals(KorePrelude.SORT_K_ITEM, KorePrelude.SORT_K_ITEM, x, KorePrelude.inj(KorePrelude.INT, KorePrelude.SORT_K_ITEM, KorePrelude.int_dv(3))))
    #     print(
    #         f"input_pattern: {reachability_system.kprint.kore_to_pretty(input_pattern)}"
    #     )
    #     simp = reachability_system.kcs.client.simplify(input_pattern)[0]
    #     print(f"simplified: {reachability_system.kprint.kore_to_pretty(simp)}")
    #     mr = reachability_system.kcs.client.get_model(input_pattern)
    #     #print(f"sat? {mr}")
    #     #match mr:
    #     #    case KoreRpc.SatResult(pat):
    #     #        print(f"simplified: {reachability_system.kprint.kore_to_pretty(pat)}")
    #     assert False

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
