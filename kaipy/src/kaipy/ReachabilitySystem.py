import functools as F
import typing as T
from pathlib import Path

import pyk.kore.syntax as Kore
from pyk.kast.outer import KDefinition
from pyk.kore.parser import KoreParser
import pyk.kore.rpc as KoreRpc
from pyk.ktool.kprint import KPrint

from .kcommands import KORE_RPC_COMMAND
from .KompiledDefinitionWrapper import KompiledDefinitionWrapper
from .kore_utils import (
    axiom_label,
    existentially_quantify_free_variables,
    free_evars_of_pattern,
    get_symbol_sort,
    get_top_cell_initializer,
    is_nonhooked_constructor_symbol,
    rewrite_axioms,
)


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


class ReachabilitySystem:
    kcs: KoreClientServer
    kdw: KompiledDefinitionWrapper
    kprint: KPrint

    def __init__(
        self,
        kdw: KompiledDefinitionWrapper,
        # kore_rpc_args: T.Iterable[str] = (),
        # connect_to_port: T.Optional[str] = None,
    ):
        self.kdw = kdw
        self.kprint = KPrint(kdw.definition_dir)
        self.kcs = KoreClientServer(
            definition_dir=kdw.definition_dir,
            main_module_name=self.kdw.main_module_name,
            # kore_rpc_args=kore_rpc_args,
            # connect_to_port=connect_to_port,
        )

    @property
    def definition_dir(self) -> Path:
        return self.kdw.definition_dir

    def __enter__(self) -> "ReachabilitySystem":
        return self

    def __exit__(self, *args: T.Any) -> None:
        self.kcs.__exit__()

    def get_symbol_sort(self, symbol: str) -> Kore.Sort:
        return get_symbol_sort(self.definition, self.kdw.main_module_name, symbol)

    @F.cached_property
    def definition(self) -> Kore.Definition:
        return self.kdw.kompiled_kore.definition

    @F.cached_property
    def top_sort(self) -> Kore.Sort:
        return self.get_symbol_sort(get_top_cell_initializer(self.definition))

    @F.cached_property
    def kast_definition(self) -> KDefinition:
        return self.kprint.definition

    def rule_by_id(self, ruleid: str) -> Kore.Axiom:
        for axiom in self.kdw.rewrite_rules:
            if axiom_label(axiom) == ruleid:
                return axiom
        raise ValueError(f"Axiom with id {ruleid} not found.")

    def is_nonhooked_constructor(self, name: str) -> bool:
        return is_nonhooked_constructor_symbol(
            self.definition, self.kdw.main_module_name, name
        )

    def simplify(self, pattern: Kore.Pattern) -> Kore.Pattern:
        try:
            return self.kcs.client.simplify(pattern)[0]
        except:
            print(f"Error when simplifying: {self.kprint.kore_to_pretty(pattern)}")
            raise

    def implies(self, ant: Kore.Pattern, con: Kore.Pattern) -> KoreRpc.ImpliesResult:
        try:
            return self.kcs.client.implies(ant, con)
        except:
            print(f"Error during implication check.")
            print(f"ant: {self.kprint.kore_to_pretty(ant)}")
            print(f"con: {self.kprint.kore_to_pretty(con)}")
            raise