import typing as T
import pyk.kore.syntax as Kore

from kaipy.AbstractionContext import AbstractionContext
from kaipy.VariableManager import VariableManager
from kaipy.BroadcastChannel import BroadcastChannel


def make_ctx() -> AbstractionContext:
    bc = BroadcastChannel()
    vm = VariableManager(5) # TODO generate high-enough number
    ctx = AbstractionContext(broadcast_channel=bc, variable_manager=vm)
    return ctx