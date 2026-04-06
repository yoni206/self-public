import functools
import random
import re
import time
from collections import defaultdict

from unionfind import unionfind

from utils import *
from utils import _
from frozendict import frozendict
import typing as t
import ast as a
if True:
    import cvc5.pythonic as s
else:
    import z3 as s

import utils
import variables
from state import SearchState
from tactics import MyTactic
from variables import TypeVariable


# TODO:
# Why is the type of the return value of a function not returned?
# Assignment to a list index or a field
# Built in functions
# Iterable, Decide, Unify tactics
# Extend the call graph inference for mutual recursion
# Mypyvy (mypy + ivy)
# Model core from CVC5

Int, Str, Bool, Float, List, Tuple, Dict, Union, Callable0, Callable1, Callable2 = [None] * 11

module_names = set()

sub = None


def create_constraint_for_call(fields):
    name = fields['_func']
    if isinstance(name, a.Attribute):
        return s.BoolVal(True)
    if len(fields['args']) == 0:
        return fields['func'] == Callable0(create_tyvar_from_ast(a.Name(f"__return_{name}__")))
    if len(fields['args']) == 1:
        return fields['func'] == Callable1(create_tyvar_from_ast(a.Name(f"__return_{name}__")), fields['args'][0])
    if len(fields['args']) == 2:
        return fields['func'] == Callable2(create_tyvar_from_ast(a.Name(f"__return_{name}__")), fields['args'][0],
                                           fields['args'][1])


def create_constraint_for_arg(fields):
    if fields['arg'] != "self":
        return s.BoolVal(True)

    # find declaring class
    node = fields['_parent']
    while not isinstance(node, a.ClassDef) and node is not None:
        node = node._parent
    if node is None:
        return s.BoolVal(True)
    return create_tyvar_from_ast(fields['node']) == types[node.name]


def create_constraint_for_return(fields):
    node = fields['_parent']
    while not isinstance(node, a.FunctionDef) and node is not None:
        node = node._parent
    assert node is not None
    return fields['value'] == create_tyvar_from_ast(a.Name(f"__return_{node.name}__"))


def create_constraint_for_listcomp(fields):
    clauses = [fields['node'] == List(fields['elt'])]
    for comp in fields['generators']:
        ifs = [create_tyvar_from_ast(it) == Bool for it in comp.ifs]
        target = s.Or(List(create_tyvar_from_ast(comp.target)) == create_tyvar_from_ast(comp.iter),
                      Tuple(create_tyvar_from_ast(comp.target)) == create_tyvar_from_ast(comp.iter))
        clauses.append(s.And(target, *ifs))
    return s.And(*clauses)


def create_constraint_for_compare(fields):
    clauses = [fields['left'] == fields['comparators'][0]]
    for comp in fields['comparators']:
        clauses.append(fields['left'] == comp)
    if not all(isinstance(it, (a.Eq, a.NotEq)) for it in fields['_ops']):
        clauses.append(s.Or(fields['left'] == Int, fields['left'] == Str, fields['left'] == Float))
    clauses.append(fields['node'] == Bool)
    return s.And(*clauses)


# noinspection PyTypeChecker
CONSTRAINT_GENERATORS: t.Dict[type, t.Callable] = {
    a.BinOp: lambda fields: (
        _((fields['left'] == Int, fields['right'] == Int, fields['node'] == Int),
          (fields['left'] == Float, fields['right'] == Float, fields['node'] == Float),
          (fields['left'] == Str, fields['right'] == Str, fields['node'] == Str)) if isinstance(fields['op'], a.Add)
        else _((fields['left'] == Int, fields['right'] == Int, fields['node'] == Int),
               (lambda tyvar: (fields['left'] == List(tyvar), fields['right'] == Int, fields['node'] == List(tyvar)))(
                       fresh_tyvar()),
               (lambda tyvar: (fields['left'] == Int, fields['right'] == List(tyvar), fields['node'] == List(tyvar)))(
                       fresh_tyvar()),
               (fields['left'] == Int, fields['right'] == Str, fields['node'] == Str),
               (fields['left'] == Str, fields['right'] == Int, fields['node'] == Str)) if isinstance(fields['op'],
                                                                                                     a.Mult)
        else _((fields['left'] == Int, fields['right'] == Int, fields['node'] == Int)) if isinstance(fields['op'],
                                                                                                     a.Sub)
        else print(fields['op']) or s.BoolVal(True)  # todo
    ),
    a.Constant: lambda fields: fields['node'] == {int: Int, str: Str, float: Float, bool: Bool}[type(fields['value'])]
    if fields['value'] not in [None, ...] else s.BoolVal(True),
    a.Assign: lambda fields: fields['value'] == fields['targets'][0],  # todo
    a.AnnAssign: lambda fields: s.And(fields['value'] == fields['target'],
                                      fields['value'] == create_z3_from_ast(fields['annotation'])),  # super todo
    a.Subscript: lambda fields: _((fields['value'] == List(fields['node']), fields['slice'] == Int),
                                  (fields['value'] == Tuple(fields['node']), fields['slice'] == Int)),
    a.List: lambda fields: fields['node'] == List(fields['elts'][0]),
    a.Tuple: lambda fields: fields['node'] == Tuple(fields['elts'][0]),
    a.Call: create_constraint_for_call,
    arg: create_constraint_for_arg,
    a.Attribute: lambda fields: s.Function(f"has_{fields['_node'].attr}", utils.type_sort, s.BoolSort())
    (create_tyvar_from_ast(fields['_node'].value)),
    a.If: lambda fields: fields['test'] == Bool,
    a.IfExp: lambda fields: s.And(fields['test'] == Bool, fields['body'] == fields['orelse'],
                                  fields['orelse'] == fields['node'], ),
    a.Return: create_constraint_for_return,
    a.For: lambda fields: _((fields['iter'] == List(fields['target']),),
                            (fields['iter'] == Tuple(fields['target']),)),
    a.ListComp: create_constraint_for_listcomp,
    a.Compare: create_constraint_for_compare,
    a.Assert: lambda fields: s.And(fields['test'] == Bool,
                                   fields['msg'] == Str if fields['msg'] is not None else True),
    a.Raise: lambda fields: s.And(s.Function(f"is_Exception", utils.type_sort, s.BoolSort())(fields['exc'])
                                  if fields['exc'] is not None else s.BoolVal(True),
                                  s.Function(f"is_Exception", utils.type_sort, s.BoolSort())(fields['cause'])
                                  if fields['cause'] is not None else s.BoolVal(True)),  # todo
    a.arg: lambda fields: create_z3_from_ast(fields['_annotation']) == create_tyvar_from_ast(a.Name(id=fields['arg']))
    if fields['_annotation'] is not None else s.BoolVal(True)
}


def create_tyvars(tree: a.AST) -> t.Dict[expr, s.ExprRef]:
    vars = {}
    ignore = set()
    for node in a.walk(tree):
        if isinstance(node, t.Hashable) and (node in vars or node in ignore):
            continue
        if isinstance(node, expr):
            vars[node] = create_tyvar_from_ast(node)
        if isinstance(node, a.arguments):
            for arg in node.args:
                namearg = a.Name(id=arg.arg)
                vars[namearg] = create_tyvar_from_ast(namearg)
                if arg.annotation is not None:
                    ignore |= set(a.walk(arg.annotation))
    return vars


def generate_constraints(tree: a.AST, vars: t.Dict[expr, s.ExprRef]) -> t.Generator[s.ExprRef, None, None]:
    def abstractify(node: a.AST):
        if isinstance(node, t.Hashable) and node in vars:
            return vars[node]
        if isinstance(node, Iterable) and not isinstance(node, str):
            return [abstractify(it) for it in node]
        return node

    # add parent information to each node
    work_queue = [(tree, None, False)]
    while work_queue:
        node, parent, annot = work_queue.pop(0)
        if parent is not None:
            node._parent = parent
        node._annot = annot or (parent is not None and parent._annot)
        work_queue.extend([(it, node, fieldname == "annotation") for fieldname, it in a.iter_fields(node) if
                           isinstance(it, a.AST)])
        for fieldname, lst in a.iter_fields(node):
            if isinstance(lst, list):
                work_queue.extend([(it, node, fieldname == "annotation") for it in lst])

    for node in a.walk(tree):
        abstractified = {descript: abstractify(val) for descript, val in a.iter_fields(node)} | \
                        {f'_{descript}': val for descript, val in a.iter_fields(node)} | \
                        {'node': abstractify(node), '_node': node} | \
                        ({'_parent': node._parent} if hasattr(node, '_parent') else {})
        if not node._annot and type(node) in CONSTRAINT_GENERATORS:
            if DEBUG:
                print(f"DEBUG Generating constraint for {node} of type {type(node)}: "
                      f"{CONSTRAINT_GENERATORS[type(node)](abstractified)}")
            yield CONSTRAINT_GENERATORS[type(node)](abstractified)


TACTICS = [MyTactic]


def _all_smt(state: SearchState, vars: t.Set[TypeVariable]) -> t.Set[frozendict[TypeVariable, TypeSolution]]:
    sols = set()
    while state.has_next():
        model = next(state)
        sol: Solution = {k: TypeSolution.from_simple_exp(model.eval(k.var, model_completion=True)) for k in vars}
        normalize_genvars(sol)
        sols.add(frozendict(sol))
    return sols


def _cmp_subexpression(exp1: a.AST, exp2: a.AST) -> int:
    """
    Return -1 if a is a subexpression of b, 1 if b is a subexpression of a, 0 otherwise.
    """
    a_subs = {it for it in a.walk(exp1) if isinstance(it, expr)}
    b_subs = {it for it in a.walk(exp2) if isinstance(it, expr)}
    return -1 if a_subs < b_subs else 1 if b_subs < a_subs else 0


def _get_all_exprs(tree: a.AST) -> t.List[TypeVariable]:
    """
    Return all expressions in the tree.
    :return: A list of all expressions in the tree in an unspecified order that respects subexpressions.
    """
    exprs = [TypeVariable(create_tyvar_from_ast(it), it) for it in a.walk(tree) if isinstance(it, expr)]

    # Can't use `sorted` because of transitivity which causes a problem with the partial order.
    # return sorted(exprs, key=functools.cmp_to_key(comparator))

    # Min Sort
    ret = []
    while exprs:
        curr_min = min(exprs, key=functools.cmp_to_key(lambda x, y: _cmp_subexpression(x.tree, y.tree)))
        ret.append(curr_min)
        exprs.remove(curr_min)
    return ret


def tactical_all_smt(constraints: t.Set[s.ExprRef], vars: t.Set[TypeVariable], tree: a.AST,
                     type_equiv_classes: t.Set[t.Tuple[TypeVariable, ...]]) -> t.Set[Solution]:
    work_queue = [SearchState(constraints)]
    all_states = [work_queue[0]]
    sols = set()
    while work_queue:
        time_start = time.time()
        state = work_queue.pop(0)
        if DEBUG:
            print(f"DEBUG Entering state {state.leading_tactics}")
        for tactic in TACTICS:
            foci_applied = set()
            for expr in _get_all_exprs(tree):
                clazz = [clazz for clazz in type_equiv_classes if expr in clazz][0]
                if any(it.leading_tactics == state.applied_tactics | {(tactic, clazz)} for it in all_states):
                    # state.solver.add(tactic.generate_blocking_clause(expr))
                    continue
                if any(_cmp_subexpression(focus.tree, itt.tree) == 1 for it in foci_applied for itt in it
                       for focus in clazz):
                    continue
                new_state = state.try_branch_with_tactic(tactic, clazz)
                if new_state is not None:
                    work_queue.append(new_state)
                    all_states.append(new_state)
                    foci_applied.add(clazz)
        if DEBUG:
            print(f"DEBUG Done applying tactics in {time.time() - time_start} seconds")
        sols |= _all_smt(state, vars)
        time_end = time.time()
        if DEBUG:
            print(f"DEBUG Finished state {state.leading_tactics} in {time_end - time_start} seconds")
    return sols


def create_call_graph(file: a.AST) -> t.Generator[t.Tuple[str, a.AST], None, None]:
    methods = [(method.name, method) for method in list(a.walk(file)) if isinstance(method, a.FunctionDef)]
    calls = {method: [] for method in methods}  # better than defaultdict because it's more explicit
    for method in methods:
        for node in a.walk(method[1]):
            if isinstance(node, a.Call):
                name = node.func.id if isinstance(node.func, a.Name) else node.func.attr
                methods = [it for it in methods if it[0] == name]
                for called_method in methods:
                    # overapproximation of the call graph
                    calls[method].append(called_method)
    while calls:
        assert any(len(v) == 0 for v in calls.values())  # currently assuming DAG
        leaf_method = [k for k, v in calls.items() if len(v) == 0][0]
        yield leaf_method
        del calls[leaf_method]
        for k, v in calls.items():
            if leaf_method in v:
                v.remove(leaf_method)


known_methods = {}

known_fields = {}


def _add_method_signature(method: a.FunctionDef):
    pass


def _add_class_fields(clazz: a.ClassDef):
    pass


def analyze_classes(file: a.AST) -> t.Tuple[t.Callable[[], s.ExprRef], t.List[str]]:
    classes = [(clazz.name, clazz) for clazz in file.body if isinstance(clazz, a.ClassDef)]
    classes_for_method_name = defaultdict(set)
    for class_name, clazz in classes:
        methods = [(method.name, method) for method in clazz.body if isinstance(method, a.FunctionDef)]
        for method_name, method in methods:
            classes_for_method_name[method_name].add(class_name)
            method._parent = clazz
            _add_method_signature(method)
        _add_class_fields(clazz)
        # todo: __init__
    method_preds = []
    for method_name, method_classes in classes_for_method_name.items():
        method_pred = lambda method_name=method_name: s.Function(f"has_{method_name}",
                                                                 utils.type_sort, *[], s.BoolSort())
        constraint = lambda method_classes=method_classes, method_pred=method_pred: (
            s.ForAll(tmp := fresh_tyvar(), method_pred()(tmp) == s.Or(*[tmp == getattr(utils.type_sort, clazz)
                                                                        for clazz in method_classes])))
        method_preds.append(constraint)
    # todo: if a method isn't in any class, it is not constrained
    return ((lambda: s.And(*[it() for it in method_preds]) if method_preds else s.BoolVal(True)),
            [clazz for clazz, _ in classes])

RETVAL_REGEX = re.compile(r"__return_(?:\w+?)__")

def _prettify_sol(sol, names):
    return {k.unparsed: sol[k].unparsed for k in sol if k in names or RETVAL_REGEX.fullmatch(k.unparsed)}


def _compute_type_equivalence_classes(constraints, vars: t.List[TypeVariable]) -> t.Set[t.Tuple[TypeVariable, ...]]:
    solver = s.Solver()
    for constraint in constraints:
        solver.add(constraint)
    solver.check()  # for lemmas
    uf = unionfind(len(vars))
    for v1, v2 in {frozenset({x1, x2}) for x1 in vars for x2 in vars if x1 != x2}:
        solver.push()
        solver.add(v1.var != v2.var)
        if solver.check() == s.unsat:
            uf.unite(vars.index(v1), vars.index(v2))
        solver.pop()
    ret = {tuple(vars[it] for it in group) for group in uf.groups()}
    return ret

def infer_types(file_name: str) -> t.Dict[str, t.List[t.Dict[str, str]]]:
    file_contents = """def need_to_infer(x, y):
    return x + y
    """
    #open(file_name).read()
    file = a.parse(file_contents)
    call_graph = create_call_graph(file)
    global module_names
    for node in a.walk(file):
        if isinstance(node, a.Import):
            module_names |= {it.name for it in node.names}
        if isinstance(node, a.ImportFrom):
            module_names |= {node.module, *node.names}
    class_formula, classes_to_define = analyze_classes(file)
    for clazz in classes_to_define:
        type_sort.declare(clazz)
    create_type_sort()
    sub = s.Function("subtype", utils.type_sort, utils.type_sort, s.BoolSort())  # todo
    for clazz in classes_to_define:
        types[clazz] = getattr(utils.type_sort, clazz)
    global Int, Str, Bool, Float, List, Tuple, Dict, Union, Callable0, Callable1, Callable2
    Int, Str, Bool, Float, List, Tuple, Dict, Union, Callable0, Callable1, Callable2 = [getattr(utils.type_sort, clazz)
                                                                                        for clazz in
                                                                                        ["int", "str", "bool", "float",
                                                                                         "list", "tuple", "dict",
                                                                                         "union", "callable0",
                                                                                         "callable1", "callable2"]]
    class_formula = class_formula()
    ret: Dict[str, t.List[Dict[str, str]]] = defaultdict(list)
    for method, tree in call_graph:
        vars = create_tyvars(tree)
        constraints = set(generate_constraints(tree, vars)) | {class_formula}
        tyvars = [variables.TypeVariable(vars[it], it) for it in vars]
        type_equiv_classes = _compute_type_equivalence_classes(constraints, tyvars)
        sols = tactical_all_smt(constraints, {variables.TypeVariable(vars[it], it) for it in vars}, tree,
                                type_equiv_classes)
        names = {it for it in tyvars if isinstance(it.tree, a.Name) and it.tree.id not in module_names}
        for i, sol in enumerate(sols):
            sol = _prettify_sol(sol, names)
            ret[method].append(sol)
    return ret


def main():
    types = infer_types("examples/example25.py")
    for method, sols in types.items():
        print(f"--- Type Inference Results for {method} ---")
        for i, sol in enumerate(sols):
            print(f"Solution #{i + 1}: \n{sol}")


if __name__ == "__main__":
    main()
