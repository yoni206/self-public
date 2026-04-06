import ast
import re
import typing
from _ast import expr, arg
from ast import unparse
from typing import Iterable, Union, Dict

CVC5 = True
if CVC5:
    from cvc5.pythonic import ExprRef, Datatype, Const, Or, And, IntSort
else:
    from z3 import ExprRef, Datatype, Const, Or, And, IntSort

from variables import TypeVariable, TypeSolution


ATOMIC_TYPES = ['int', 'str', 'bool', 'float', "unit"]
DEBUG = True
SOL_COUNT = 10
type_sort = Datatype("Type")
type_sort.declare("_any")  # for model completion - not a real type
for ty in ATOMIC_TYPES:
    type_sort.declare(ty)
type_sort.declare("list", ("tyvar", type_sort))
type_sort.declare("tuple", ("tyvar", type_sort))
type_sort.declare("dict", ("tyvar_key", type_sort), ("tyvar_value", type_sort))
type_sort.declare("union", ("tyvar_left", type_sort), ("tyvar_right", type_sort))
type_sort.declare("callable0", ("returnval", type_sort))
type_sort.declare("callable1", ("returnval", type_sort), ("arg1", type_sort))
type_sort.declare("callable2", ("returnval", type_sort), ("arg1", type_sort), ("arg2", type_sort))
type_sort.declare("T", ("idx", IntSort()))
types = {}
Solution = Dict[TypeVariable, TypeSolution]
RejectFunction = typing.Callable[[], None]


def _(*clauses: Iterable[ExprRef]) -> ExprRef:
    return Or(*[And(*clause) for clause in clauses])


curr_tyvar = 0


def fresh_tyvar() -> ExprRef:
    global curr_tyvar
    curr_tyvar += 1
    return Const(f"Tyvar{curr_tyvar}", type_sort)


curr_genvar = 0


def fresh_genvar() -> ExprRef:
    global curr_genvar, type_sort
    curr_genvar += 1

    return type_sort.T(curr_genvar)


def create_tyvar_from_ast(node: Union[expr, arg]) -> ExprRef:
    return Const(f"T({unparse(node)})", type_sort)


def generate_subscript_ast(target: str, slice: str) -> ast.Subscript:
    return ast.Subscript(value=ast.Name(id=target), slice=ast.Name(id=slice))


GENVAR_PATTERN = re.compile(r"T\d+")  # todo


def normalize_genvars(sol: Solution):
    # make totally sure order is deterministic otherwise none of this makes sense
    keys = sorted(list(sol.keys()), key=hash)

    curr_genvar_normalized = 1
    normalized_genvars = {}
    for key in keys:
        tree = sol[key].annot
        for node in ast.walk(tree):
            if isinstance(node, ast.Name) and GENVAR_PATTERN.match(node.id):
                if node.id not in normalized_genvars:
                    normalized_genvars[node.id] = f"T{curr_genvar_normalized}"
                    curr_genvar_normalized += 1
                node.id = normalized_genvars[node.id]


def create_type_sort():
    global type_sort, types
    type_sort = type_sort.create()
    for ty in ATOMIC_TYPES:
        types[ty[0].upper() + ty[1:]] = getattr(type_sort, ty)
    types['List'] = type_sort.list
    types['Tuple'] = type_sort.tuple
    types['Dict'] = type_sort.dict
    types['Union'] = type_sort.union
    types['Callable0'] = type_sort.callable0
    types['Callable1'] = type_sort.callable1
    types['Callable2'] = type_sort.callable2


def create_z3_from_ast(tree: ast.expr) -> ExprRef:
    # Yes, I know it's a mess that the opposite function is in variables.py, but circular imports :/
    if isinstance(tree, ast.Subscript):
        if tree.value.id in ["List", "Tuple", "Dict", "union"]:
            return types[tree.value.id](create_z3_from_ast(tree.slice))
        if tree.value.id == "Callable":
            raise NotImplementedError("TODO")
    if isinstance(tree, ast.Name):
        if tree.id.startswith("T"):
            return types["T"](int(tree.id[1:]))
        return types[tree.id] if tree.id in types else types[tree.id[0].upper() + tree.id[1:]]
    raise NotImplementedError(f"Cannot convert {ast.unparse(tree)} to z3")
