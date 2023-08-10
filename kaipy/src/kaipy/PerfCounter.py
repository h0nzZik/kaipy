import typing as T
import dataclasses

@dataclasses.dataclass
class PerfCounter:
    total_count : int = 0
    total_time : float = 0.0

    @property
    def dict(self) -> T.Dict[str, T.Any]:
        return {
            'total_count' : self.total_count,
            'total_time' : self.total_time
        }   

    def add(self, time_diff : float, count=1) -> None:
        self.total_count = self.total_count + count
        self.total_time = self.total_time + time_diff