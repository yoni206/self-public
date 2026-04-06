import ast
import typing
from abc import ABCMeta, abstractmethod
from collections import defaultdict
from typing import Set

import utils
from utils import fresh_tyvar, Solution, RejectFunction, fresh_genvar, GENVAR_PATTERN, CVC5
if CVC5:
    from cvc5.pythonic import ExprRef, Exists, Not, simplify, Or, BoolVal
else:
    from z3 import ExprRef, Exists, Not, simplify, Or, BoolVal
from variables import TypeVariable, TypeSolution


_any = None

USE_OPTIMAL_HEURISTIC = True


class Tactic(metaclass=ABCMeta):

    def get_heuristic_foci(self, sols: Set[Solution]) -> typing.Union[Set[TypeVariable], None]:
        if USE_OPTIMAL_HEURISTIC:
            return None
        return self._get_heuristic_foci(sols)

    @abstractmethod
    def _get_heuristic_foci(self, sols: Set[Solution]) -> typing.Union[Set[TypeVariable], None]:
        """
        :param sols: Current set of solutions
        :return: Set of variables that are likely to be valid foci of this tactic, or `None` if it's all of them
        """
        return NotImplemented

    @abstractmethod
    def generate_conjecture_clause(self, var: TypeVariable) -> ExprRef:
        return NotImplemented

    @abstractmethod
    def generate_blocking_clause(self, var: TypeVariable) -> ExprRef:
        return NotImplemented

    @classmethod
    def get_name(cls) -> str:
        return getattr(cls, "NAME", cls.__name__.removesuffix("Tactic"))

    def __repr__(self):
        return self.get_name()

    def __eq__(self, other):
        return isinstance(other, Tactic) and self.get_name() == other.get_name()

    def __hash__(self):
        return hash(self.get_name())


class GenerifyTactic(Tactic):

    def _get_heuristic_foci(self, sols: Set[Solution]) -> Set[TypeVariable]:
        return set()

    def generate_conjecture_clause(self, var: TypeVariable) -> ExprRef:
        genvar = fresh_genvar()
        return var.var == genvar

    def generate_blocking_clause(self, var: TypeVariable) -> ExprRef:
        return BoolVal(False)  # utils.type_sort.is_T(var.var)

    def get_name(self) -> str:
        return "Generify"


# note: can't remove lambda due to scoping of utils.type_sort, utils.types
MyTactic = GenerifyTactic()
