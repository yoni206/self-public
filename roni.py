from pysmt.shortcuts import Symbol, And, Or, LT
from pysmt import Solver
from pysmt.typing import REAL

# grid of 8 x 8
# that is, 64 nodes of the form (x,y) with 0 <= x,y <= 7 and 
# most (x,y) are connected to (x-1,y), (x+1,y), (x,y+1), (x,y-1) 
# except for the top and bottom rows and left and right columns

# fix grid size
n = 3

# fix max visits per node
max_visits_per_node = 2

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
for (i,j) in V:
    for (ii,jj) in V:
        if ((i,j), (ii, jj)) in E:
          print("(", i, ", ", j, ") -- (", ii, ", ", jj, ")")
      
# fix start and end nodes
# start node: (3, 2) 
# end node: (7,0)
start = (3,2)
end = (7,0)

# dis-allowed visits:
# the entire row 4 is blocked from time 0 to time 5.5
# (4,0): (0, 5.5) (can't visit (4,0) between the times 0 and 5.5)
# (4,1): (0, 5.5) (can't visit (4,1) between the times 0 and 5.5)
# (4,2): (0, 5.5) (can't visit (4,2) between the times 0 and 5.5)
# (4,3): (0, 5.5) (can't visit (4,3) between the times 0 and 5.5)
# (4,4): (0, 5.5) (can't visit (4,4) between the times 0 and 5.5)
# (4,5): (0, 5.5) (can't visit (4,5) between the times 0 and 5.5)
# (4,6): (0, 5.5) (can't visit (4,6) between the times 0 and 5.5)
# (4,7): (0, 5.5) (can't visit (4,7) between the times 0 and 5.5)
blocks = {}
blocks[(4,0)] = (0, 5.5)
blocks[(4,1)] = (0, 5.5)
blocks[(4,2)] = (0, 5.5)
blocks[(4,3)] = (0, 5.5)
blocks[(4,4)] = (0, 5.5)
blocks[(4,5)] = (0, 5.5)
blocks[(4,6)] = (0, 5.5)
blocks[(4,7)] = (0, 5.5)

# "x-(i,j)-k" is the time-stamp in which the agent was at point (i,j) for the kth time
variables = {}
for (i,j) in V:
  for k in range(0, max_visits_per_node):
    if (i,j) not in variables:
      variables[(i,j)] = {}
    variables[(i,j)][k] = Symbol("x-(" + str(i) + "," + str(j) + ")-" + str(k), REAL)

constraints = []
for (i,j) in V:
  for (ii,jj) in V:
    if ((i,j), (ii,jj)) not in E:
      clause = []
      for (iii, jjj) in V:
        for k in range(0, max_visits_per_node):
          for kk in range(0, max_visits_per_node):
            for kkk in range(0, max_visits_per_node):
              between = And([
                LT(variables[(i,j)][k], variables[(iii,jjj)][k]),
                LT(variables[(i,j)][k], variables[(iii,jjj)][kk]),
                LT(variables[(i,j)][k], variables[(iii,jjj)][kkk]),
                LT(variables[(i,j)][kk], variables[(iii,jjj)][k]),
                LT(variables[(i,j)][kk], variables[(iii,jjj)][kk]),
                LT(variables[(i,j)][kk], variables[(iii,jjj)][kkk]),
                LT(variables[(i,j)][kkk], variables[(iii,jjj)][k]),
                LT(variables[(i,j)][kkk], variables[(iii,jjj)][kk]),
                LT(variables[(i,j)][kkk], variables[(iii,jjj)][kkk]),
                LT(variables[(i,j)][k], variables[(iii,jjj)][k]),
                LT(variables[(iii,jjj)][k], variables[(ii,jj)][kk]),
                LT(variables[(iii,jjj)][k], variables[(ii,jj)][kkk]),
                LT(variables[(iii,jjj)][kk], variables[(ii,jj)][k]),
                LT(variables[(iii,jjj)][kk], variables[(ii,jj)][kk]),
                LT(variables[(iii,jjj)][kk], variables[(ii,jj)][kkk]),
                LT(variables[(iii,jjj)][kkk], variables[(ii,jj)][k]),
                LT(variables[(iii,jjj)][kkk], variables[(ii,jj)][kk]),
                LT(variables[(iii,jjj)][kkk], variables[(ii,jj)][kkk])])
              clause += [between]
        constraints += Or([clause])
solver = Solver(name="z3")
for constraint in constraints:
  solver.assertTrue(constraint)
solver.checkSat()
print("end loop")
print(constraints)
