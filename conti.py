from pysmt.shortcuts import Solver
from pysmt.shortcuts import Symbol, And, Equals, Implies
from pysmt.shortcuts import Plus, Minus, Times, GE, LE, GT, LT
from pysmt.shortcuts import REAL
from pysmt.shortcuts import Real, TRUE

steps = 5

# blocks are circles and are defined using their center and radius, and the time in which they are blocked
blocks = {((0, 0), 1): (1, 2),
          ((1, 1), 1): (0, 3),
          ((3, 3), 0.5): (0, 4)
          }

x_start = 0
y_start = 0
t_start = 0

x_end = 10
y_end = 10

solver = Solver("z3")

x_vars = []
y_vars = []
t_vars = []

for i in range(0, steps):
  x_vars += [Symbol("x_" + str(i), REAL)]
  y_vars += [Symbol("y_" + str(i), REAL)]
  t_vars += [Symbol("t_" + str(i), REAL)]

# TODO need to make the lines not to cross
# don't cross blocks
for block in blocks:
    point = block[0]
    radius = block[1]
    time_range = blocks[block]
    x = point[0]
    y = point[1]
    start_time = time_range[0]
    end_time = time_range[1]

    for i in range(0, steps):
      xi = x_vars[i]
      yi = y_vars[i]
      ti = t_vars[i]
      cond = And(LE(Real(start_time), ti), LE(ti, Real(end_time)))
      distance_from_point_sq = Plus(Times(Minus(xi, Real(x)), Minus(xi, Real(x))), Times(Minus(yi, Real(y)), Minus(yi, Real(y))))
      distant = GT(distance_from_point_sq, Times(Real(radius), Real(radius)))
      solver.add_assertion(Implies(cond, distant))


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




