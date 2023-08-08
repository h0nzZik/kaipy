import functools as F
import logging
import typing as T
import time
#import multiprocessing as mp
import multiprocess as mp # type: ignore
import multiprocess.pool as mpPool # type: ignore
from pathlib import Path

import pyk.kore.syntax as Kore
from pyk.kast.outer import KDefinition
from pyk.kore.parser import KoreParser
import pyk.kore.rpc as KoreRpc
from pyk.ktool.kprint import KPrint

from .PerfCounter import PerfCounter
from .kcommands import KORE_RPC_COMMAND
from .KompiledDefinitionWrapper import KompiledDefinitionWrapper
import kaipy.kore_utils as KoreUtils

_LOGGER: T.Final = logging.getLogger(__name__)

class KoreClientServer:
    server: T.Optional[KoreRpc.KoreServer]
    client: KoreRpc.KoreClient

    def __init__(
        self,
        definition_dir: Path,
        main_module_name: str,
        kore_rpc_args: T.Iterable[str] = ["--enable-log-timestamps"],
        # connect_to_port: T.Optional[str] = None,
    ):
        # if connect_to_port is not None:
        #    port = int(connect_to_port)
        #    timeout = 1500
        #    self.server = None
        # else:
        # port = utils.find_free_port()
        self.server = KoreRpc.KoreServer(
            kompiled_dir=definition_dir,
            module_name=main_module_name,
            command=list((KORE_RPC_COMMAND,)) + list(kore_rpc_args),
            # port=port,
        )
        timeout = None
        self.client = KoreRpc.KoreClient("localhost", port=self.server.port, timeout=timeout)

    def __enter__(self) -> "KoreClientServer":
        return self

    def __exit__(self, *args: T.Any) -> None:
        self.client.close()
        if self.server is not None:
            self.server.close()
            self.server = None


class RSStats:
    implies: PerfCounter
    execute_step: PerfCounter
    simplify: PerfCounter
    map_simplify: PerfCounter

    def __init__(self):
        self.reset()
    
    def reset(self) -> None:
        self.implies = PerfCounter()
        self.execute_step = PerfCounter()
        self.simplify = PerfCounter()

    @property
    def dict(self) -> T.Dict[str, T.Any]:
        return {
            'implies' : self.implies.dict,
            'execute_step' : self.execute_step.dict,
            'simplify' : self.simplify.dict,
            'map_simplify' : self.map_simplify.dict,
        }   



global_kcs: KoreClientServer|None = None
def set_global_kcs(kcs: KoreClientServer):
    global global_kcs
    global_kcs = kcs


class KcsPool:
    pool: mpPool.Pool
    def __init__(
        self,
        definition_dir: Path,
        main_module_name: str,
        kore_rpc_args: T.Iterable[str] = ["--enable-log-timestamps"],
    ):
        self.pool = mp.Pool(
            processes=mp.cpu_count(),
            initializer=lambda: set_global_kcs(KoreClientServer(definition_dir, main_module_name, kore_rpc_args))
        )
    
    def map_simplify(self, ps: T.List[Kore.Pattern]) -> T.List[Kore.Pattern]:
        def f(p):
            assert global_kcs is not None
            return global_kcs.client.simplify(p)[0]

        return self.pool.map(f, ps)

class ReachabilitySystem:
    kcs: KoreClientServer
    kcspool: KcsPool
    kdw: KompiledDefinitionWrapper
    kprint: KPrint
    stats: RSStats

    def __init__(
        self,
        kdw: KompiledDefinitionWrapper,
    ):
        self.kdw = kdw
        self.kprint = KPrint(kdw.definition_dir)
        self.kcs = KoreClientServer(
            definition_dir=kdw.definition_dir,
            main_module_name=self.kdw.main_module_name,
        )
        self.kcspool = KcsPool(
            definition_dir=kdw.definition_dir,
            main_module_name=self.kdw.main_module_name,
        )
        self.stats = RSStats()

    @property
    def definition_dir(self) -> Path:
        return self.kdw.definition_dir

    def __enter__(self) -> "ReachabilitySystem":
        return self

    def __exit__(self, *args: T.Any) -> None:
        self.kcs.__exit__()

    def get_symbol_sort(self, symbol: str) -> Kore.Sort:
        return KoreUtils.get_symbol_sort(self.definition, self.kdw.main_module_name, symbol)

    @F.cached_property
    def definition(self) -> Kore.Definition:
        return self.kdw.kompiled_kore.definition

    @F.cached_property
    def top_sort(self) -> Kore.Sort:
        return self.get_symbol_sort(KoreUtils.get_top_cell_initializer(self.definition))

    @F.cached_property
    def kast_definition(self) -> KDefinition:
        return self.kprint.definition

    def rule_by_id(self, ruleid: str) -> Kore.Axiom:
        for axiom in self.kdw.rewrite_rules:
            if KoreUtils.axiom_label(axiom) == ruleid:
                return axiom
        raise ValueError(f"Axiom with id {ruleid} not found.")

    def is_nonhooked_constructor(self, name: str) -> bool:
        return KoreUtils.is_nonhooked_constructor_symbol(
            self.definition, self.kdw.main_module_name, name
        )

    def execute_step(self, cfg: Kore.Pattern) -> KoreRpc.ExecuteResult:
        old = time.perf_counter()
        rv = self.kcs.client.execute(cfg, max_depth=1)
        new = time.perf_counter()
        self.stats.execute_step.add(new - old)
        return rv

    def simplify(self, pattern: Kore.Pattern) -> Kore.Pattern:
        try:
            old = time.perf_counter()
            rv = self.kcs.client.simplify(pattern)[0]
            new = time.perf_counter()
            self.stats.simplify.add(new - old)
            return rv
        except KoreRpc.KoreClientError as e:
            _LOGGER.warning(f"Error when simplifying: {self.kprint.kore_to_pretty(pattern)}")
            _LOGGER.warning(f"exception: {str(e)}")
            _LOGGER.warning(f"data: {str(e.data)}")
            raise
    
    def map_simplify(self, ps: T.List[Kore.Pattern]) -> T.List[Kore.Pattern]:
        try:
            old = time.perf_counter()
            rv = self.kcspool.map_simplify(ps)
            new = time.perf_counter()
            self.stats.map_simplify.add(new - old, count=len(ps))
            return rv
        except KoreRpc.KoreClientError as e:
            _LOGGER.warning(f"Error when simplifying (multiple patterns)")
            _LOGGER.warning(f"exception: {str(e)}")
            _LOGGER.warning(f"data: {str(e.data)}")
            raise

    def implies(self, ant: Kore.Pattern, con: Kore.Pattern) -> KoreRpc.ImpliesResult:
        try:
            old = time.perf_counter()
            rv = self.kcs.client.implies(ant, con)
            new = time.perf_counter()
            self.stats.implies.add(new - old)
            return rv
        except KoreRpc.KoreClientError as e:
            _LOGGER.warning(f"Error during implication check.")
            _LOGGER.warning(f"ant: {ant.text}")
            _LOGGER.warning(f"con: {con.text}")
            _LOGGER.warning(f"ant(pretty): {self.kprint.kore_to_pretty(ant)}")
            _LOGGER.warning(f"con(pretty): {self.kprint.kore_to_pretty(con)}")
            _LOGGER.warning(f"exception: {str(e)}")
            _LOGGER.warning(f"data: {str(e.data)}")
            raise
    
    def sortof(self, p: Kore.Pattern) -> Kore.Sort:
        match p:
            case Kore.App('inj', (srcsort,dstsort), _):
                return dstsort
            case Kore.App(sym, _, _):
                return self.get_symbol_sort(sym)

        return p.sort # type: ignore


    def subsumes(self, ant: Kore.Pattern, con: Kore.Pattern) -> T.Tuple[bool, T.Dict[str,str] | None]:
        renaming = KoreUtils.compute_renaming0(
            vars_to_avoid=list(KoreUtils.free_evars_of_pattern(ant)),
            vars_to_rename=list(KoreUtils.free_evars_of_pattern(con))
        )
        con_renamed: Kore.Pattern = KoreUtils.rename_vars(
            renaming,
            con,
        )
        con_eqa = KoreUtils.existentially_quantify_free_variables(self.sortof(con_renamed), con_renamed)
        ir = self.implies(ant, con_eqa)
        return ir.satisfiable,(renaming if ir.satisfiable else None)