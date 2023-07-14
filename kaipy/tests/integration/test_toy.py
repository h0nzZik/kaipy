import typing as T
from pathlib import Path

import pyk.kore.prelude as KorePrelude
import pyk.kore.rpc as KoreRpc
import pyk.kore.syntax as Kore
import pytest
from pyk.kore.parser import KoreParser
from pyk.ktool.kprint import KPrint
from pyk.testing._kompiler import KompiledTest

import kaipy.rs_utils as RSUtils
from kaipy.HeatPreAnalysis import ContextAlias, ContextAliases, collect_rests
from kaipy.KompiledDefinitionWrapper import KompiledDefinitionWrapper
from kaipy.ReachabilitySystem import ReachabilitySystem
from kaipy.rs_utils import cleanup_pattern

from kaipy.testing.testingbase import RSTestBase

class ToyTestBase(RSTestBase):
    ...

class TestToy(ToyTestBase):
    KOMPILE_MAIN_FILE = ToyTestBase.LANGUAGES / "toy/toy.k"
    KOMPILE_BACKEND = "haskell"

    def test_toy_get_model_1(self, reachability_system: ReachabilitySystem):
        rs = reachability_system
        phi = Kore.Equals(KorePrelude.BOOL, rs.top_sort, KorePrelude.TRUE, KorePrelude.FALSE)
        m = rs.kcs.client.get_model(phi)
        assert type(m) is KoreRpc.UnsatResult

    def test_toy_get_model_2(self, reachability_system: ReachabilitySystem):
        rs = reachability_system
        varx = Kore.EVar('VARX', KorePrelude.BOOL)
        phi = Kore.Equals(KorePrelude.BOOL, rs.top_sort, KorePrelude.TRUE, varx)
        m = rs.kcs.client.get_model(phi)
        assert type(m) is KoreRpc.SatResult

    def test_toy_get_model_3(self, reachability_system: ReachabilitySystem):
        rs = reachability_system
        varx = Kore.EVar('VARX', KorePrelude.BOOL)
        side = Kore.Equals(KorePrelude.BOOL, KorePrelude.BOOL, KorePrelude.TRUE, varx)
        phi = Kore.And(KorePrelude.BOOL, varx, side)
        m = rs.kcs.client.get_model(phi)
        #print(m.model.text if m.model else "<empty-subst>")
        assert type(m) is KoreRpc.SatResult

    # def test_toy_get_model_4(self, reachability_system: ReachabilitySystem):
    #     rs = reachability_system
    #     varx = Kore.EVar('VARX', Kore.SortApp("SortInt"))
    #     varx_kitem = KorePrelude.inj(Kore.SortApp("SortInt"), KorePrelude.SORT_K_ITEM, varx)
    #     varx_k = Kore.App(KorePrelude.KSEQ, (), (varx_kitem, KorePrelude.DOTK))
    #     #side = Kore.Top(KorePrelude.SORT_K) # This leads to UnknownResult, which is fine
    #     side = Kore.Equals(
    #                     KorePrelude.BOOL,
    #                     KorePrelude.SORT_K,
    #                     KorePrelude.TRUE,
    #                     Kore.App("LblisKResult", (), (varx_k,)),
    #                 )
        
    #     phi = Kore.And(KorePrelude.SORT_K, varx_k, side)
    #     print(phi.text)
    #     m = rs.kcs.client.get_model(phi)
    #     print(m)
    #     #assert type(m) is KoreRpc.SatResult
    #     assert False

    def test_toy_exec(self, reachability_system: ReachabilitySystem):
        rs = reachability_system
        varx = Kore.EVar('VARX', KorePrelude.SORT_K_ITEM)
        p: Kore.Pattern = Kore.App(
            "Lbl'-LT-'generatedTop'-GT-'",
            (),
            (
                Kore.App(
                    "Lbl'-LT-'k'-GT-'",
                    (),
                    (
                        Kore.App(
                            KorePrelude.KSEQ, (), (
                                varx,
                                Kore.App(
                                    KorePrelude.KSEQ, (), (
                                        Kore.App(
                                            "Lbl'Hash'freezerfoo'LParUndsRParUnds'TOY-SYNTAX'Unds'Stmt'Unds'AExp0'Unds'"
                                        ),
                                        KorePrelude.DOTK
                                    )
                                )
                            )
                        ),
                    )
                ),
                Kore.EVar("VARGENERATEDCOUNTER", Kore.SortApp('SortGeneratedCounterCell'))
            ),
        )
        varx_k = Kore.App(KorePrelude.KSEQ, (), (varx, KorePrelude.DOTK))
        side_cond = Kore.Equals(
                        KorePrelude.BOOL,
                        rs.top_sort,
                        KorePrelude.TRUE,
                        Kore.App("LblisKResult", (), (varx_k,)),
                    )
        p_w_side = Kore.And(
                    rs.top_sort,
                    p,
                    side_cond,
        )
        
        er = rs.kcs.client.execute(p_w_side, max_depth=1, log_failed_rewrites=True, log_successful_rewrites=True)

        assert er.reason == KoreRpc.StopReason.BRANCHING
        assert er.next_states is not None
        assert er.next_states[0].substitution is not None
        assert er.next_states[1].substitution is None # the residual

        # if er.next_states:
        #     print(f"len(next_states): {len(er.next_states)}")
        #     for st in er.next_states:
        #         print(f"branch: {rs.kprint.kore_to_pretty(st.kore)}")
        #         if st.substitution is not None:
        #             print(f"(subst): {rs.kprint.kore_to_pretty(st.substitution)}")
        # assert False
