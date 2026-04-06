import ast
from dataclasses import dataclass
from utils import CVC5

if CVC5:
    from cvc5.pythonic import ExprRef
else:
    from z3 import ExprRef


# from utils import create_tyvar_from_ast


@dataclass
class TypeVariable:
    var: ExprRef
    tree: ast.expr

    @property
    def unparsed(self):
        return ast.unparse(self.tree)

    def __hash__(self):
        return hash(ast.unparse(self.tree))

    def __eq__(self, other):
        return ast.unparse(self.tree) == ast.unparse(other.tree)

    def __repr__(self):
        return f"T({self.unparsed})"

    # def apply(self, tree_trans: Callable[[ast.expr], ast.expr]) -> 'TypeVar':
    #     new_tree = tree_trans(self.tree)
    #     return TypeVar(create_tyvar_from_ast(new_tree), new_tree)


@dataclass
class TypeSolution:
    typ: ExprRef
    annot: ast.expr

    @staticmethod
    def from_simple_exp(typ: ExprRef):
        return TypeSolution(typ, create_ast_from_z3(typ))


    def __hash__(self):
        return hash(self.unparsed)

    def __eq__(self, other):
        return self.unparsed == other.unparsed

    @property
    def unparsed(self):
        return ast.unparse(self.annot)


def create_ast_from_z3(exp: ExprRef) -> ast.expr:
    # Yes, I know it's a mess that the opposite function is in utils.py, but circular imports :/
    if exp.decl().name() == "list":
        return ast.Subscript(
            value=ast.Name(id="List", ctx=ast.Load()),
            slice=create_ast_from_z3(exp.children()[0]),
            ctx=ast.Load()
        )
    if exp.decl().name() == "tuple":
        return ast.Subscript(
            value=ast.Name(id="Tuple", ctx=ast.Load()),
            slice=create_ast_from_z3(exp.children()[0]),
            ctx=ast.Load()
        )
    if exp.decl().name().startswith("callable"):
        return ast.Subscript(
            value=ast.Name(id="Callable", ctx=ast.Load()),
            slice=ast.Tuple(elts=[create_ast_from_z3(exp.children()[0]),
                                  ast.List([create_ast_from_z3(child) for child in exp.children()[1:]])]),
            ctx=ast.Load()
        )
    if exp.decl().name() == "T":
        return ast.Name(id=f"T{exp.children()[0]}", ctx=ast.Load())
    return ast.Name(id=exp.decl().name(), ctx=ast.Load())
