from cvc5.pythonic import *

num_of_state_variables = 2

# state variables
f = {}
for i in range(num_of_state_variables):
  f[i] = Bool("f" + str(i))

# actions
a = {}
a[0] = Not(f[1])

#
preconditions = {}
for i in range(len(a)):
  preconditions[i] = {}
  for j in range(num_of_state_variables):
    preconditions[i][j] = Bool("f" + str(j) + "_in_precon_of_action_" + str(i))

# A set of trajectories. Each trajectory is a list. 
# But here we do a list of trajectories becausei lists are not hashable.
trajectories = [
# first trajectory
[And(f[0], f[1]), a[0], And(f[0], a[0]), a[0], And(f[0], a[0])],

# ...

# last trajectory
[f[1], a[0], And(f[0], a[0]), a[0], And(f[0], a[0])]
]


solver = Solver()

# the action model given by the preconditions is safe for plans that have n steps
def safe(n, preconditions, trajectories):
  steps = {}
  for i in range(0, n):
    steps[i] = Bool("step" + str(i))
  is_safe = Forall(steps, Implies(consistent(steps, preconditions), Forall(... bbaaaa)))
