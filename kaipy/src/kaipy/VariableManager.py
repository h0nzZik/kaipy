import typing as T

import pyk.kore.syntax as Kore

class VariableManager:
    counter: int

    # TODO skip first `n` variables (those that occur somewhere?)
    def __init__(self, initial_counter: int):
        self.counter = initial_counter
    
    def get_fresh_evar_name(self) -> str:
        c = self.counter
        self.counter = self.counter + 1
        return "VARSV"+str(c)

    def get_fresh_evar(self, sort: Kore.Sort) -> Kore.EVar:
        name = self.get_fresh_evar_name()
        return Kore.EVar(name=name, sort=sort)