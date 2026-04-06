import re
import typing
from types import NoneType
from typing import Union, Set
from utils import CVC5

if CVC5:
    from cvc5.pythonic import ExprRef, Solver, sat, ModelRef, Or
else:
    from z3 import ExprRef, Solver, sat, ModelRef, Or

from tactics import Tactic
from variables import TypeVariable


class SearchState:
    def __init__(self, constraints: Set[ExprRef]):
        self.solver = Solver()
        self.solver.add(*constraints)
        self._original_constraints = constraints
        self.applied_tactics = set()
        self.leading_tactics = set()
        self._sols = set()


    TYVAR_REGEX = re.compile(r"Tyvar(\d+)")

    def _block_model(self, model: ModelRef):
        if CVC5:
            self.solver.add(Or([f != model[f] for f in model.decls() if getattr(f, "arity", lambda: 0)() == 0 and
                                not SearchState.TYVAR_REGEX.fullmatch(str(f))]))
        else:
            self.solver.add(Or([f() != model[f] for f in model.decls() if f.arity() == 0 and
                                not SearchState.TYVAR_REGEX.fullmatch(f.name())]))

    def __next__(self):
        if self.solver.check() == sat:
            model = self.solver.model()
            self._block_model(model)
            self._sols.add(model)
            return model
        else:
            raise StopIteration

    def has_next(self):
        return self.solver.check() == sat

    def try_branch_with_tactic(self, tactic: Tactic, clazz: typing.Tuple[TypeVariable]) \
            -> Union[type(None), 'SearchState']:
        if (tactic, clazz) in self.applied_tactics:
            return None
        self.applied_tactics |= {(tactic, clazz)}
        conjecture = tactic.generate_conjecture_clause(clazz[0])
        new_state = SearchState(set(self._original_constraints) | {conjecture})  # todo, do I need to ret the conj?
        if new_state.has_next():
            new_state.leading_tactics = self.leading_tactics | {(tactic, clazz)}
            self.solver.add(tactic.generate_blocking_clause(clazz[0]))
            return new_state
        return None

    def __str__(self):
        return str(self.leading_tactics)

