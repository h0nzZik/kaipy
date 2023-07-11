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

LANGUAGES: T.Final = (Path(__file__).parent / "languages").resolve(strict=True)


class ToyTestBase(KompiledTest):
    @pytest.fixture
    def kompiled_definition_wrapper(
        self, definition_dir: Path
    ) -> KompiledDefinitionWrapper:
        return KompiledDefinitionWrapper.load_from_dir(definition_dir)

    @pytest.fixture
    def reachability_system(
        self, kompiled_definition_wrapper: KompiledDefinitionWrapper
    ) -> ReachabilitySystem:
        return ReachabilitySystem(kdw=kompiled_definition_wrapper)


class TestToy(ToyTestBase):
    KOMPILE_MAIN_FILE = LANGUAGES / "toy/toy.k"
    KOMPILE_BACKEND = "haskell"

    def test_toy_exec(self, reachability_system: ReachabilitySystem):
        rs = reachability_system
        varx = Kore.EVar('VARX', KorePrelude.SORT_K_ITEM)
        # But we had to guess the sort of the the variable!
        #varx0 = Kore.EVar('VARX', Kore.SortApp('SortAExp'))
        #varx = KorePrelude.inj(Kore.SortApp('SortAExp'), KorePrelude.SORT_K_ITEM, varx0)
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
        
        print(f"old: {rs.kprint.kore_to_pretty(p_w_side)}")
        er = rs.kcs.client.execute(p_w_side, max_depth=1, log_failed_rewrites=True, log_successful_rewrites=True)
        #assert er.reason == KoreRpc.StopReason.DEPTH_BOUND
        #print(f"er.reason: {er.reason}")
        #print(f"er: {er}")
        
        #print(f"new: {rs.kprint.kore_to_pretty(er.state.kore)}")
        
        if er.next_states:
            print(f"len(next_states): {len(er.next_states)}")
            for st in er.next_states:
                px = st.kore
                print(f"branch: {rs.kprint.kore_to_pretty(px)}")
                px = cleanup_pattern(rs, px)
                print(f"clean: {rs.kprint.kore_to_pretty(px)}")
                gmr = rs.kcs.client.get_model(px)
                print(f"gmr: {gmr}")
        assert False
