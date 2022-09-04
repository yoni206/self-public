from cvc5.pythonic import *
# nice drawings don't work on my new machine :(
# import matplotlib.pyplot as plt
# import numpy as np
# plt.style.use('seaborn-whitegrid')

# number of steps in the plan
steps = 3

# blocks are circles and are defined using their center and radius
blocks = [
          ((3, 3), 1)
          ]

# start location and time
x_start = 0
y_start = 0
t_start = 0

# end location (goal)
x_end = 10
y_end = 10

#create a solver
solver = Solver()
solver.setOption("nl-cov-force", "true")

# for each step we have x,y,t variables.
# There are stored in lists for x_vars, y_vars and t_vars
x_vars = []
y_vars = []
t_vars = []

# creating the variables
for i in range(0, steps):
  x_vars += Reals("x_" + str(i))
  y_vars += Reals("y_" + str(i))
  t_vars += Reals("t_" + str(i))

# constraints for not crossing blocks
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

      x0 = x
      y0 = y
      x1 = xi
      y1 = yi
      x2 = xxii
      y2 = yyii
      
      numerator = ((x2 - x1) * (y1 - y0)) - ((x1 - x0) * (y2 - y1)) 
      numerator_sq = numerator * numerator
      tmp1 = x2 - x1
      tmp2 = y2 - y1
      denominator_sq = (tmp1 * tmp1) + tmp2 * tmp2
      distance_sq = numerator_sq / denominator_sq
      distant = distance_sq > radius * radius
      condition = Implies(And(Not(x1 == x2), Not(y1 == y2)), distant)
      condition = Implies(And(Not(x1 == x2), Not(y1 == y2)), distant)
      solver.add(condition)
      distances_sq += [distance_sq]

# Don't continue after you are there -- temporarilly removed
# for i in range(0, steps):
#   got_there1 = x_vars[i] == Real(x_end)
#   got_there2 = y_vars[i] == Real(y_end)
#   got_there = And([got_there1, got_there2])
#   stay_there_constraints = []
#   for j in range(i+1, steps):
#     stay_there_constraint_x = x_vars[j] == Real(x_end)
#     stay_there_constraint_y = y_vars[j] == Real(y_end)
#     stay_there_constraint = And(stay_there_constraint_x, stay_there_constraint_y)
#     stay_there_constraints += [stay_there_constraint]
#   if len(stay_there_constraints) > 0:
#     stay_there = And(stay_there_constraints)
#   else:
#     stay_there = TRUE()
#   solver.add_assertion(Implies(got_there, stay_there))

# start at start
solver.add(x_vars[0] == x_start)
solver.add(y_vars[0] == y_start)

#end at end
solver.add(x_vars[steps - 1] == x_end)
solver.add(y_vars[steps - 1] == y_end)

# times are non-decreasing and non-negative
solver.add((t_vars[0] >= 0))
for i in range(0, steps - 1):
  solver.add((t_vars[i+1] >= t_vars[i]))

# don't go too fast
for i in range(0, steps):
  for j in range(i+1, steps):
    xi = x_vars[i]
    yi = y_vars[i]
    ti = t_vars[i]
    xj = x_vars[j]
    yj = y_vars[j]
    tj = t_vars[j]
    delta = (ti - tj)
    delta_sq = (delta * delta)
    distance_sq = Plus(((xi - xj) * (xi - xj)), ((yi - yj) * (yi - yj)))
    solver.add((delta_sq >= distance_sq))

#check sat
print("about to check sat")
print("assertions:", solver.assertions())
if sat == solver.check():
  print("there is a solution")
  model = solver.model()
  model = solver.model()
  for i in range(0, steps):
    model[t_vars[i]]
    print(model[t_vars[i]], ": (", model[x_vars[i]], ", ", model[y_vars[i]], ")")
 
# can't do nice graphs on new machine 
#   x = [float(str(model[xx])) for xx in x_vars]
#   y = [float(str(model[yy])) for yy in y_vars]
#   labels = [str(model[tt]) for tt in t_vars]
#   fig, ax = plt.subplots()
#   ax.scatter(x,y)
# 
#   ax.plot(x,y,color='black')
# 
#   for i, txt in enumerate(labels):
#     ax.annotate(txt, (x[i], y[i]))
# 
#   for block in blocks:
#     point = block[0]
#     radius = block[1]
#     circle = plt.Circle(point, radius)
#     ax.add_patch(circle)
#   fig.savefig('plotcircles.png')
else:
  print("no solution")
#   unsat_core = solver.get_unsat_core()
#   print("size of unsat core: ", len(unsat_core))
#   print("unsat core:")
#   for formula in unsat_core:
#     print(formula)



