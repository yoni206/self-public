from cvc5 import *

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

zero = solver.mkReal(0)
one = solver.mkReal(1)
real_sort = solver.getRealSort()

# a relatively recent option which is good
solver.setOption("nl-cov-force", "true")

# for each step we have x,y,t variables.
# There are stored in lists for x_vars, y_vars and t_vars
x_vars = []
y_vars = []
t_vars = []

# creating the variables
for i in range(0, steps):
  x_vars += solver.mkConst(real_sort, "x_" + str(i))
  y_vars += solver.mkConst(real_sort, "y_" + str(i))
  t_vars += solver.mkConst(real_sort, "t_" + str(i))

# points are not in blocks
for block in blocks:
    point = block[0]
    sidze = block[1]
    x = point[0]
    y = point[1]
    
    # x axis value of left side
    left = solver.mkReal(x - (0.5 * sidze))
    
    # x axis value of right side
    right = solver.mkReal(x + (0.5 * sidze))
    
    # y axis value of top side
    top = solver.mkReal(y + (0.5 * sidze))

    # y axis value of bottom side
    bottom = solver.mkReal(y - (0.5 * sidze))

    for i in range(0, steps):
        ir = solver.mkReal(i)
        left_ok = solver.mkTerm(Kind.LT, ir, left)
        right_ok = solver.mkTerm(Kind.GT, ir, right)
        top_ok = solver.mkTerm(Kind.GT, ir, top)
        bottom_ok = solver.mkTerm(Kind.LT, ir, bottom)
        ok = solver.mkTerm(Kind.OR, *[left_ok, right_ok, top_ok, bottom_ok])
        solver.assertFormula(ok)

# times are non-decreasing and non-negative
solver.assertFormula(solver.mkTerm(Kind.GEQ, t_vars[0], zero))
for i in range(0, steps - 1):
  solver.add(solver.mkTerm(Kind.GEQ, t_vars[i+1], t_vars[i]))

# don't go too fast
for i in range(0, steps):
  for j in range(i+1, steps):
    xi = x_vars[i]
    yi = y_vars[i]
    ti = t_vars[i]
    xj = x_vars[j]
    yj = y_vars[j]
    tj = t_vars[j]
    delta = solver.mkTerm(MINUS, ti, tj)
    delta_sq = solver.mkTerm(MULT, delta, delta)
    xij = solver.mkTerm(xi, xj)
    yij = solver.mkTerm(yi, yj)
    xijxij = solver.mkTerm(MULT, xij, xij)
    yijyij = solver.mkTerm(MULT, yij, yij)
    distance_sq = solver.mkTerm(PLUS, xijxij, yijyij)
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
