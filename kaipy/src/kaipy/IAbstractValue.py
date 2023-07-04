import abc
import typing as T

import pyk.kore.syntax as Kore


class IAbstractValue(abc.ABC):
    # @abc.abstractmethod
    # def variables(self) -> T.Set[Kore.EVar]:
    #    ...
    ## invariant:
    ## FV(self.pattern) \subseteq self.variables

    @abc.abstractmethod
    def pattern(self, top_sort: Kore.Sort) -> Kore.Pattern:
        ...
