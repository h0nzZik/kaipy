from functools import cached_property
from pathlib import Path

from typing import (
    Any,
    Final,
    Iterable,
    Optional,
    IO,
)

from pyk.kast.outer import (
    KDefinition,
)

from pyk.ktool.kprint import (
    KPrint
)

from pyk.kore.rpc import (
    KoreServer,
    KoreClient
)

from pyk.kore.parser import (
    KoreParser
)

from pyk.kore.syntax import (
    Definition,
    Sort,
)

from .kcommands import KORE_RPC_COMMAND

class KoreClientServer:
    server: Optional[KoreServer]
    client: KoreClient

    def __init__(self,
        definition_dir: Path,
        main_module_name: str,
        kore_rpc_args: Iterable[str] = (),
        connect_to_port : Optional[str] = None,
        ):
        if connect_to_port is not None:
            port = int(connect_to_port)
            timeout=1500
            self.server = None
        else:
            port = 3000
            self.server = KoreServer(
                kompiled_dir=definition_dir, 
                module_name=main_module_name, 
                command=(KORE_RPC_COMMAND,) + tuple(kore_rpc_args), 
                port=port)
            timeout=None
        self.client = KoreClient('localhost', port=port, timeout=timeout)
    
    def __enter__(self) -> 'KoreClientServer':
        return self

    def __exit__(self, *args: Any) -> None:
        self.client.close()
        if self.server is not None:
            self.server.close()
            self.server = None

class ReachabilitySystem:
    kcs: KoreClientServer
    definition: Definition
    main_module_name: str
    kprint : KPrint
    definition_dir : Path

    def __init__(self,
        definition_dir: Path,
        kore_rpc_args: Iterable[str] = (),
        connect_to_port : Optional[str] = None
        ):
        self.definition_dir = definition_dir
        with open(definition_dir / 'mainModule.txt', 'r') as mm:
            self.main_module_name = mm.read()
        with open(definition_dir / 'definition.kore', 'r') as dc:
            d = dc.read()
        kparser = KoreParser(d)
        
        self.definition = kparser.definition()
        self.kprint = KPrint(definition_dir)
        self.kcs = KoreClientServer(
            definition_dir=definition_dir,
            main_module_name=self.main_module_name,
            kore_rpc_args=kore_rpc_args,
            connect_to_port=connect_to_port,
            )

    def __enter__(self) -> 'ReachabilitySystem':
        return self

    def __exit__(self, *args: Any) -> None:
        self.kcs.__exit__()

    @cached_property
    def kast_definition(self) -> KDefinition:
        return self.kprint.definition
