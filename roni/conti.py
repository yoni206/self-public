from cvc5.pythonic import *
# nice drawings don't work on my new machine :(
# import matplotlib.pyplot as plt
# import numpy as np
# plt.style.use('seaborn-whitegrid')

# number of steps in the plan
steps = 3

# blocks are squares and are defined using their center and size of side
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
base = main_ctx().solver
f = solver.add(x_end == y_end)
base.addSygusConstraint(f)


# a relatively recent option which is good
solver.setOption("nl-cov-force", "true")
solver.setOption("sygus", "true")

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
    sidze = block[1]
    x = point[0]
    y = point[1]
    
    # x axis value of left side
    left = x - (0.5 * sidze)
    
    # x axis value of right side
    right = x + (0.5 * sidze)
    
    # y axis value of top side
    top = y + (0.5 * sidze)

    # y axis value of bottom side
    bottom = y - (0.5 * sidze)

    for i in range(1, steps):
        # from previous step to this step -- line equation mx+n
        xi = x_vars[i]
        xii = x_vars[i-1]
        yi = y_vars[i]
        yii = y_vars[i-1]
        mi = (yi - yii) / (xi - xii) 
        ni = (mi * xi) - yi

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
f = solver.add(y_vars[steps - 1] == y_end)
realSort = base.getRealSort()
base.declareSygusVar("a", realSort)
base.addSygusConstraint(f)

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



