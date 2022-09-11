from cvc5 import *

def synth_curve(start, end, blocks):


# def gen_dist_sqrd(point1, point2):
#     p1x = point1[0]
#     p1y = point1[1]
#     p2x = point2[0]
#     p2y = point2[1]
#     
#     x_diff = solver.mkTerm(Kind.SUB, p1x, p2x)
#     y_diff = solver.mkTerm(Kind.SUB, p1y, p2y)
#     x_diff_sqrd = solver.mkTerm(Kind.MULT, x_diff, x_diff)
#     y_diff_sqrd = solver.mkTerm(Kind.MULT, y_diff, y_diff)
#     dist_sqrd = solver.mkTerm(Kind.ADD, x_diff_sqrd, y_diff_sqrd)
#     return dist_sqrd



# number of steps in the plan

# blocks are squares and are defined using their center and size of side, start time and end time
blocks = [
          ((0, 0), 1, 1, 3),
          ((3, 3), 1, 2, 5),
          ((4, 4), 1, 4, 8),
          ]

# heuristic -- #steps is number of segment points
segment_points = [block[2] for block in blocks]
segment_points += [block[3] for block in blocks]
segment_points = [0] + segment_points
segment_points = set(segment_points)
segment_points = list(segment_points)
segment_points = sorted(segment_points)
steps = len(segment_points)

# start location and time
x_start = 0
y_start = 0
t_start = 0

# end location (goal)
x_end = 10
y_end = 10

#create a solver
solver = Solver()
solver.setOption("nl-cov", "true")
# solver.setOption("nl-ext-tplanes", "true")
solver.setOption("produce-models", "true")
solver.setOption("dag-thresh", "0")

zero = solver.mkReal(0)
one = solver.mkReal(1)
real_sort = solver.getRealSort()

# a relatively recent option which is good
solver.setOption("nl-cov-force", "true")

# produce models for sat formulas
solver.setOption("produce-models", "true")

# for each step we have x,y,t variables.
# There are stored in lists for x_vars, y_vars and t_vars
x_vars = []
y_vars = []
t_vars = []

# creating the variables
for i in range(0, steps):
  x_vars += [solver.mkConst(real_sort, "x_" + str(i))]
  y_vars += [solver.mkConst(real_sort, "y_" + str(i))]
  t_vars += [solver.mkConst(real_sort, "t_" + str(i))]

# points are not in blocks
for block in blocks:
    point = block[0]
    sidze = block[1]
    x = point[0]
    y = point[1]
    start_time = solver.mkReal(block[2])
    end_time = solver.mkReal(block[3])
    
    # x axis value of left side
    left = solver.mkReal(x - (0.5 * sidze))
    
    # x axis value of right side
    right = solver.mkReal(x + (0.5 * sidze))
    
    # y axis value of top side
    top = solver.mkReal(y + (0.5 * sidze))

    # y axis value of bottom side
    bottom = solver.mkReal(y - (0.5 * sidze))

    for i in range(0, steps):
        left_ok = solver.mkTerm(Kind.LT, x_vars[i], left)
        right_ok = solver.mkTerm(Kind.GT, x_vars[i], right)
        top_ok = solver.mkTerm(Kind.GT, y_vars[i], top)
        bottom_ok = solver.mkTerm(Kind.LT, y_vars[i], bottom)
        ok = solver.mkTerm(Kind.OR, *[left_ok, right_ok, top_ok, bottom_ok])
        time_holds_1 = solver.mkTerm(Kind.LEQ, start_time, t_vars[i])
        time_holds_2 = solver.mkTerm(Kind.LEQ, t_vars[i], end_time)
        time_holds = solver.mkTerm(Kind.AND, time_holds_1, time_holds_2)
        block_constraint = solver.mkTerm(Kind.IMPLIES, time_holds, ok)
        solver.assertFormula(block_constraint)

# start at start, end at end
solver.assertFormula(solver.mkTerm(Kind.EQUAL, x_vars[0], solver.mkReal(x_start)))
solver.assertFormula(solver.mkTerm(Kind.EQUAL, y_vars[0],  solver.mkReal(y_start)))
solver.assertFormula(solver.mkTerm(Kind.EQUAL, x_vars[steps - 1],  solver.mkReal(x_end)))
solver.assertFormula(solver.mkTerm(Kind.EQUAL, y_vars[steps - 1],  solver.mkReal(y_end)))

# times non-negative and increasoing
solver.assertFormula(solver.mkTerm(Kind.EQUAL, t_vars[0], zero))
for i in range(0, steps - 1):
  noneg = solver.mkTerm(Kind.GT, t_vars[i+1], t_vars[i])
  solver.assertFormula(noneg)

# just to make things more interesting -- some movement in each step
for i in range(0, steps - 1):
    x_mvmt = solver.mkTerm(Kind.LT, x_vars[i], x_vars[i+1])
    y_mvmt = solver.mkTerm(Kind.LT, y_vars[i], y_vars[i+1])
    mvmt = solver.mkTerm(Kind.OR, x_mvmt, y_mvmt)
    solver.assertFormula(mvmt)

# just to make things even more interesting -- each step gets you closer
# for i in range(0, steps - 1):
#     x_end_expr = solver.mkReal(x_end)
#     y_end_expr = solver.mkReal(y_end)
#     dist_i = gen_dist_sqrd((x_vars[i], y_vars[i]), (x_end_expr, y_end_expr))
#     dist_ii = gen_dist_sqrd((x_vars[i+1], y_vars[i+1]), (x_end_expr, y_end_expr))
#     closer = solver.mkTerm(Kind.GT, dist_i, dist_ii)
#     solver.assertFormula(closer)

# just to make things super interesting -- each start-time and end-time of the blocks separates steps
# no two consecutive steps in the same segment
for i in range(0, len(segment_points) - 1):
  segment_left = solver.mkReal(segment_points[i])
  segment_right = solver.mkReal(segment_points[i+1])
    
  t_i_in_segment_1 = solver.mkTerm(Kind.GEQ, t_vars[i], segment_left)
  t_i_in_segment_2 = solver.mkTerm(Kind.GEQ, segment_right, t_vars[i])
  t_i_in_segment = solver.mkTerm(Kind.AND, t_i_in_segment_1, t_i_in_segment_2)
  solver.assertFormula(t_i_in_segment)
  
last_t_in_last_segment = solver.mkTerm(Kind.GEQ, t_vars[steps-1], solver.mkReal(segment_points[steps-1]))
solver.assertFormula(last_t_in_last_segment)
# # no two consecutive steps in the last (open) segment
# last_segment_point = solver.mkReal(segment_points[len(segment_points) - 1])
# for j in range(0, steps - 1):
#   t_j = t_vars[j]
#   t_jj = t_vars[j+1]
#   
#   t_j_in_last_segment = solver.mkTerm(Kind.GT, t_j, last_segment_point)
#   t_jj_in_last_segment = solver.mkTerm(Kind.GT, t_jj, last_segment_point)
#  
#   not_both = solver.mkTerm(Kind.IMPLIES, t_jj_in_last_segment, solver.mkTerm(Kind.NOT, t_jj_in_last_segment))
#   print("panda", not_both)
#   solver.assertFormula(not_both)



# don't go too fast
# TODO strangly linearizing
for i in range(0, steps):
   for j in range(i+1, steps):
     xi = x_vars[i]
     yi = y_vars[i]
     ti = t_vars[i]
     xj = x_vars[j]
     yj = y_vars[j]
     tj = t_vars[j]
     delta = solver.mkTerm(Kind.SUB, ti, tj)
     # delta_sq = solver.mkTerm(Kind.MULT, delta, delta)
     xij = solver.mkTerm(Kind.SUB, xi, xj)
     yij = solver.mkTerm(Kind.SUB, yi, yj)
     # xijxij = solver.mkTerm(Kind.MULT, xij, xij)
     # yijyij = solver.mkTerm(Kind.MULT, yij, yij)
     # distance_sq = solver.mkTerm(Kind.ADD, xijxij, yijyij)
     distance = solver.mkTerm(Kind.ADD, xij, yij)
     # not_too_fast = solver.mkTerm(Kind.GEQ, delta_sq, distance_sq)
     # TODO this is bulshit, not even abs
     not_too_fast = solver.mkTerm(Kind.GEQ, delta, distance)
     solver.assertFormula(not_too_fast)

sketch = []

#check sat
print("about to check sat")
# for a in solver.getAssertions():
#   print("panda:", a)
sat = solver.checkSat()
print(sat)
if sat.isSat():
  print("there is a solution")
  for i in range(0, steps):
    sketch += [((solver.getValue(x_vars[i]), solver.getValue(y_vars[i])) ,solver.getValue(t_vars[i]))]
  for p in sketch:
    xp = "{:.2f}".format(float(p[0][0].getRealValue()))
    yp = "{:.2f}".format(float(p[0][1].getRealValue()))
    tp = "{:.2f}".format(float(p[1].getRealValue()))
    print((xp, yp), tp)


# synthesize parts
for i in range(0, steps - 1):
  pp = sketch[i]
  xi = p[0][0]
  yi = p[0][1]
  ti = p[1]

  ii = i + 1
  pp = sketch[ii]
  xii = pp[0][0]
  yii = pp[0][1]
  tii = pp[1]

  f = synth_curve(((xi, yi), ti), ((xii, yii), tii))
  print("curve":, f)


