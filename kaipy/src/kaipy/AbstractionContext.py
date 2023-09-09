import dataclasses

from kaipy.BroadcastChannel import BroadcastChannel
from kaipy.VariableManager import VariableManager


@dataclasses.dataclass
class AbstractionContext:
    broadcast_channel: BroadcastChannel
    variable_manager: VariableManager