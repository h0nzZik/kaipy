import dataclasses

from kaipy.IBroadcastChannel import IBroadcastChannel
from kaipy.VariableManager import VariableManager


@dataclasses.dataclass
class AbstractionContext:
    broadcast_channel: IBroadcastChannel
    variable_manager: VariableManager