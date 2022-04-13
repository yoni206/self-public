from pysmt.shortcuts import Solver
from pysmt.shortcuts import Symbol, And, Equals, Implies
from pysmt.shortcuts import Plus, Minus, Times, GE
from pysmt.shortcuts import REAL
from pysmt.shortcuts import Real, TRUE

steps = 5

solver = Solver("z3")

x_vars = []
y_vars = []
t_vars = []

for i in range(0, steps):
  x_vars += [Symbol("x_" + str(i), REAL)]
  y_vars += [Symbol("y_" + str(i), REAL)]
  t_vars += [Symbol("t_" + str(i), REAL)]

x_start = 0
y_start = 0
t_start = 0

x_end = 2
y_end = 2

# Don't continue after you are there
for i in range(0, steps):
  got_there1 = Equals(x_vars[i], Real(x_start))
  got_there2 = Equals(y_vars[i], Real(y_start))
  got_there = And([got_there1, got_there2])
  stay_there_constraints = []
  for j in range(i+1, steps):
    stay_there_constraint_x = Equals(x_vars[j], Real(x_end))
    stay_there_constraint_y = Equals(y_vars[j], Real(y_end))
    stay_there_constraint = And(stay_there_constraint_x, stay_there_constraint_y)
    stay_there_constraints += [stay_there_constraint]
  if len(stay_there_constraints) > 0:
    stay_there = And(stay_there_constraints)
  else:
    stay_there = TRUE()
  solver.add_assertion(Implies(got_there, stay_there))

# start at start
solver.add_assertion(Equals(x_vars[0], Real(x_start)))
solver.add_assertion(Equals(y_vars[0], Real(y_start)))

# times are non-decreasing and non-negative
solver.add_assertion(GE(t_vars[0], Real(0)))
for i in range(0, steps - 1):
  solver.add_assertion(GE(t_vars[i+1], t_vars[i]))

# don't go too fast
for i in range(0, steps):
  for j in range(i+1, steps):
    xi = x_vars[i]
    yi = y_vars[i]
    ti = t_vars[i]
    xj = x_vars[j]
    yj = y_vars[j]
    tj = t_vars[j]
    delta = Minus(ti, tj)
    delta_sq = Times(delta, delta)
    distance_sq = Plus(Times(Minus(xi, xj), Minus(xi, xj)), Times(Minus(yi, yj), Minus(yi, yj)))
    solver.add_assertion(GE(delta_sq, distance_sq))

#check sat
sat = solver.check_sat()
if sat:
  model = solver.get_model()
  for i in range(0, steps):
    print(model[t_vars[i]], ": (", model[x_vars[i]], ", ", model[y_vars[i]], ")")




