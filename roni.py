# import an smt-solver from pysmt
from pysmt.shortcuts import Solver

# import Real constants from pysmt
from pysmt.shortcuts import Real

# import variables from pysmt (they are called symbols)
from pysmt.shortcuts import Symbol

# import operators from pysmt
from pysmt.shortcuts import And, Or, Implies, LT, GT, GE, Equals, Not

# import the type "REAL" from pysmt of real numbers
from pysmt.typing import REAL

# grid of 8 x 8
# that is, 64 nodes of the form (x,y) with 0 <= x,y <= 7 and 
# most (x,y) are connected to (x-1,y), (x+1,y), (x,y+1), (x,y-1) 
# except for the top and bottom rows and left and right columns

# fix grid size
n = 3

# fix max visits per node
max_visits_per_node = 1

# create graph
V = set([(i,j) for i in range(0,n) for j in range(0,n)])
E = set([])
graph = (V, E)
for i in range(0, n):
  for j in range(0, n):
    if i < n - 1:
      E.add(((i, j), (i+1, j)))
    if j < n - 1:
      E.add(((i,j), (i, j+1)))
    if i > 0:
        E.add(((i,j), (i-1, j)))
    if j > 0:
      E.add(((i,j), (i, j-1)))

# print graph
print("graph:")
for (i,j) in V:
    for (ii,jj) in V:
        if ((i,j), (ii, jj)) in E:
          print("(", i, ", ", j, ") -- (", ii, ", ", jj, ")")
      
# fix start and end nodes
start = (2,2)
end = (0,0)

# print start and end
print()
print("start:", start)
print("end:", end)

# dis-allowed visits:
# blocks[(x,y)] = (a,b) means that you cannot be at (x,y) 
# starting from time a until time b (inclusive)
# in this example we block an entire line
blocks = {}
for i in range(0, n):
  blocks[(1,i)] = (0,5.5)

# print blocks
print()
print("blocks:")
for block in blocks:
  print(block, ":", blocks[block])

# Define the variables.
# "x-(i,j)-k" is the time-stamp in which the agent was at point (i,j) for the kth time
# convention: if the agent didn't visit (i,j) for the kth time, then the value is negative.
variables = {}
for (i,j) in V:
  for k in range(0, max_visits_per_node):
    if (i,j) not in variables:
      variables[(i,j)] = {}
    variables[(i,j)][k] = Symbol("x-(" + str(i) + "," + str(j) + ")-" + str(k), REAL)

# define the graph constraints:
# if you are at point (i,j) for the kth time before you are at point (ii,jj)
# for the kkth time,
# but these points are not connected in the graph,
# then there must be some other point (iii, jjj) in the graph in which you visit
# for the kkkth time between your kth visit to (i,j) and you kkth visit
# to (ii, jj)
graph_constraints = []
# iterate over all nodes in the graph
for (i,j) in V:
  for (ii,jj) in V:
    # only consider different nodes
    if (i,j) != (ii,jj):
      # only consider nodes that are not connected
      if ((i,j), (ii,jj)) not in E:
        # iterate over the number of visits in (i,j) and in (ii,jj)
        # (these are k and kk, respectively)
        for k in range(0, max_visits_per_node):
          for kk in range(0, max_visits_per_node):
            # go over all other points in the graph and their possible visits
            # (iii, jjj), kkk
            # One of these must be between the kth visit to (i,j) and the
            # kkth visit to (ii,jj)
            clause = []
            for (iii, jjj) in V:
              if (iii, jjj) != (i, j) and (iii, jjj) != (ii, jj):
                for kkk in range(0, max_visits_per_node):
                  between = And([
                    LT(variables[(i,j)][k], variables[(iii,jjj)][kkk]),
                    LT(variables[(iii,jjj)][kkk], variables[(ii,jj)][kk]),
                    ])
                  clause += [between]
            # the above needs to hold only when we actually visited (i,j) and (ii,jj),
            # that is, if their time stamps are non-negative.
            occurred1 = GE(variables[(i,j)][k], Real(0))
            occurred2 = GT(variables[(ii,jj)][kk], variables[(i,j)][k])
            occurred = And(occurred1, occurred2)
            # separated means that one of the other points is between them
            separated = Or(clause)
            graph_constraint = Implies(occurred, separated)
            # print(graph_constraint)
            graph_constraints += [graph_constraint]


# assert that you cannot visit the blocked nodes at their blocked times
block_constraints = []
for node  in blocks:
  interval = blocks[node]
  low = interval[0]
  high = interval[1]
  for k in range(0, max_visits_per_node):
    outside1 = LT(variables[node][k], Real(low))
    outside2 = GT(variables[node][k], Real(high))
    outside = Or(outside1, outside2)
    block_constraints += [outside]

# source and target constraints
# your 0th visit to the start node must be at time 0
# and you must have some visit to the end node with non-negative time
source_constraint = Equals(variables[start][0], Real(0))
clause = []
for k in range(0, max_visits_per_node):
  target_constraint_k = GE(variables[end][k], Real(0))
  clause += [target_constraint_k]
target_constraint = Or(clause)

# all-different -- you cannot be in two places at the same time.
# that is, your kth visit to (i,j) must be at a different time from your
# kkth visit to (ii, jj)
distinct_constraints = []
for (i,j) in V:
  for (ii, jj) in V:
    for k in range(0, max_visits_per_node):
      for kk in range(0, max_visits_per_node):
        if ((i,j), k) != ((ii, jj), kk):
          distinct = Not(Equals(variables[(i,j)][k], variables[(ii,jj)][kk]))
          distinct_constraints += [distinct]
distinct_constraint = And(distinct_constraints)

# you cannot visit a node for the second time before you visited it
# for the first time, etc.
second_visit_constraints = []
for (i,j) in V:
  for k in range(0, max_visits_per_node - 1):
    # if u visited this node for the k+1 time, then it must have occurred after
    # your kth visit to it, and that kth visit must have happend (in a non-negative time)
    second_visit_constraint = Implies(GE(variables[(i,j)][k+1], Real(0)), And(LT(variables[(i,j)][k], variables[(i,j)][k+1]), GE(variables[(i,j)][k], Real(0))))
    second_visit_constraints += [second_visit_constraint]

# collect all the constraints
constraint = And(
       graph_constraints + 
       block_constraints + 
       second_visit_constraints +
        [ source_constraint, 
            target_constraint, 
            distinct_constraint
        ])

# create a solver
solver = Solver(name="z3")

# check satisfaibility
r = solver.is_sat(constraint)

# get a model (will fail if unsat)
m = solver.get_model()

# print the path nicely
print()
print("path (time: node)")
reverse_m = {solver.get_py_value(v):k for (k,v) in m}
times = [k for k in reverse_m]
times.sort()
for time in times:
  if time >= 0:
    print(str(time) + ": ", reverse_m[time])
