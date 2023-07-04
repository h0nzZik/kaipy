import abc
import pyk.kore.syntax as Kore
import typing as T

class IAbstractValue(abc.ABC):

    #@abc.abstractmethod
    #def variables(self) -> T.Set[Kore.EVar]:
    #    ...
    ## invariant:
    ## FV(self.pattern) \subseteq self.variables    
    
    @abc.abstractmethod
    def pattern(self, top_sort: Kore.Sort) -> Kore.Pattern:
        ...
