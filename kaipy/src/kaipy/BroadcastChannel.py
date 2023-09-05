import abc
import typing as T

import pyk.kore.syntax as Kore


class BroadcastChannel(abc.ABC):
    constraints: T.List[Kore.MLPred]
    
    def broadcast(self, m: T.List[Kore.MLPred]):
        self.constraints.extend(m)
    
    def reset(self):
        self.constraints = []