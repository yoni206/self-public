from cvc5.pythonic import *
sort = Datatype("Sort")
sort.declare("nullary")
sort.declare("unary", ("param", sort))
sort = sort.create()
Unary = sort.unary
Nullary = sort.nullary

curr_var = 0


def fresh_var() -> ExprRef:
    global curr_var
    curr_var += 1
    return Const(f"v{curr_var}", sort)

f1, f2 = Function("f1", sort, sort), Function("f2", sort, sort)
formula = ForAll([param := fresh_var(), x := fresh_var()], 
                          Implies(x == Unary(param), 
                                  And(f1(param) == Nullary, x == Unary(f2(param)))))
# Why isn't f1 = [else -> Nullary], f2 = [else -> Var(0)] a model?

s = Solver()
s.set("sygus-inference", "true")
s.set("incremental", "false")
if s.__module__ == "z3.z3":
    s.set(timeout=120)
else:
    s.set(tlimit=120)
s.add(formula)
print(res := s.check(), s.reason_unknown() if res == unknown else s.model())
