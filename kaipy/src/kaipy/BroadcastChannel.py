import abc
import typing as T

import pyk.kore.syntax as Kore


class BroadcastChannel(abc.ABC):
    constraints: T.List[Kore.Pattern]
    
    def __init__(self):
        self.constraints = list()

    def broadcast(self, m: T.List[Kore.Pattern]):
        self.constraints.extend(m)
    
    def reset(self):
        self.constraints = []