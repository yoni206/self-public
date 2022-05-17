from pysmt.shortcuts import Solver, UnsatCoreSolver
from pysmt.shortcuts import Symbol, And, Equals, Implies, Not
from pysmt.shortcuts import Plus, Minus, Times, GE, LE, GT, LT, Div
from pysmt.shortcuts import REAL
from pysmt.shortcuts import Real, TRUE

# number of steps in the plan
steps = 3

# blocks are circles and are defined using their center and radius
blocks = [
          ((3, 3), 1)]

# start location and time
x_start = 0
y_start = 0
t_start = 0

# end location (goal)
x_end = 10
y_end = 10

#create a solver
solver = UnsatCoreSolver("z3")
solver.set_option("produce-unsat-cores", "true")

# for each step we have x,y,t variables.
# There are stored in lists for x_vars, y_vars and t_vars
x_vars = []
y_vars = []
t_vars = []

# creating the variables
for i in range(0, steps):
  x_vars += [Symbol("x_" + str(i), REAL)]
  y_vars += [Symbol("y_" + str(i), REAL)]
  t_vars += [Symbol("t_" + str(i), REAL)]

# TODO need to make the lines not to cross
# don't cross blocks
distances_sq = []
for block in blocks:
    point = block[0]
    radius = block[1]
    x = point[0]
    y = point[1]

    for i in range(1, steps):
      xi = x_vars[i]
      yi = y_vars[i]
      xxii = x_vars[i-1]
      yyii = y_vars[i-1]

      x0 = Real(x)
      y0 = Real(y)
      x1 = xi
      y1 = yi
      x2 = xxii
      y2 = yyii


      numerator = Minus(Times(Minus(x2, x1), Minus(y1, y0)), Times(Minus(x1, x0), Minus(y2, y1)))
      numerator_sq = Times(numerator, numerator)
      tmp1 = Minus(x2, x1)
      tmp2 = Minus(y2, y1)
      denominator_sq = Plus(Times(tmp1, tmp1), Times(tmp2, tmp2)) 
      distance_sq = Div(numerator_sq, denominator_sq)
      distant = GT(distance_sq, Times(Real(radius), Real(radius)))
      condition = Implies(And(Not(Equals(x1, x2)), Not(Equals(y1, y2))), distant)
      solver.add_assertion(condition)
      distances_sq += [distance_sq]

# Don't continue after you are there
# for i in range(0, steps):
#   got_there1 = Equals(x_vars[i], Real(x_end))
#   got_there2 = Equals(y_vars[i], Real(y_end))
#   got_there = And([got_there1, got_there2])
#   stay_there_constraints = []
#   for j in range(i+1, steps):
#     stay_there_constraint_x = Equals(x_vars[j], Real(x_end))
#     stay_there_constraint_y = Equals(y_vars[j], Real(y_end))
#     stay_there_constraint = And(stay_there_constraint_x, stay_there_constraint_y)
#     stay_there_constraints += [stay_there_constraint]
#   if len(stay_there_constraints) > 0:
#     stay_there = And(stay_there_constraints)
#   else:
#     stay_there = TRUE()
#   solver.add_assertion(Implies(got_there, stay_there))

# start at start
solver.add_assertion(Equals(x_vars[0], Real(x_start)))
solver.add_assertion(Equals(y_vars[0], Real(y_start)))

#end at end
solver.add_assertion(Equals(x_vars[steps - 1], Real(x_end)))
solver.add_assertion(Equals(y_vars[steps - 1], Real(y_end)))

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
  print("there is a solution")
  model = solver.get_model()
  for i in range(0, steps):
    print(model[t_vars[i]], ": (", model[x_vars[i]], ", ", model[y_vars[i]], ")")
  print("distances_sq:")
  for distant in distances_sq:
    print(solver.get_value(distant))
  
else:
  print("no solution")
  unsat_core = solver.get_unsat_core()
  print("size of unsat core: ", len(unsat_core))
  print("unsat core:")
  for formula in unsat_core:
    print(formula)



