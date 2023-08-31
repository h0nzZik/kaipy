import typing as T
import pyk.kore.syntax as Kore

from kaipy.AbstractionContext import AbstractionContext
from kaipy.VariableManager import VariableManager
from kaipy.IBroadcastChannel import IBroadcastChannel


def make_ctx() -> AbstractionContext:
    class BC(IBroadcastChannel):
        def broadcast(self, m: T.List[Kore.MLPred]):
            pass
    bc = BC()
    vm = VariableManager(5) # TODO generate high-enough number
    ctx = AbstractionContext(broadcast_channel=bc, variable_manager=vm)
    return ctx