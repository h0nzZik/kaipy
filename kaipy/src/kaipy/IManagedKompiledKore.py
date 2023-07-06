import abc
import typing as T

from pyk.kore.kompiled import KompiledKore

class IManagedKompiledKore(T.ContextManager['IManagedKompiledKore'], abc.ABC):

    @property
    @abc.abstractmethod
    def kompiled_kore(self) -> KompiledKore:
        ...

    @abc.abstractmethod
    def __enter__(self):
        ...
    
    @abc.abstractmethod
    def __exit__(self, *args: T.Any) -> None:
        ...
