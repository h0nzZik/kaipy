import abc
import typing as T

import pyk.kore.syntax as Kore


class IBroadcastChannel(abc.ABC):
    @abc.abstractmethod
    def broadcast(self, m: T.List[Kore.MLPred]):
        ...
    