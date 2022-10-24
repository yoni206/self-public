from cvc5.pythonic import *

num_of_state_variables = 2




# effects
effects = {}
effects[0] = {}
effects[0][1] = False
effects[1] = {}
effects[1][1] = False


# mapping from preconditions to state variables
precon_to_states = {}

# preconditions
preconditions = {}
for i in range(len(effects)):
  preconditions[i] = []
  for j in range(num_of_state_variables):
    new_precon_var = Bool("f" + str(j) + "_in_precon_of_action_" + str(i))
    preconditions[i] += [new_precon_var]
    precon_to_states[new_precon_var] = j


print(precon_to_states)

# A set of trajectories. Each trajectory is a list. 
# But here we do a list of trajectories becausei lists are not hashable.
trajectories = [
# first trajectory
[[True, True], 0, [True, False], 0, [True, False]],
# ...
# last trajectory
[False, True], 0, [False, False], 0, [False, False]
]


solver = Solver()


def consistent(preconditions, trajectories):
  state_variable_in_trajectory_step = {}
  for i in range(num_of_state_variables):
    for j, trajectory in enumerate(trajectories):
      for k in range(int((len(trajectory) - 1) / 2)):
        state_variable_in_trajectory_step[(i,j,k)] = Bool("state_var_" + str(i) + "_in_traj_" + str(j) + "_on_step_" + str(k))
  print(state_variable_in_trajectory_step)

  is_state = True
  axiom1_instances = []
  for i, elem in enumerate(trajectory):
    if not is_state:
      # is_state is False, we are in action
      # axiom 1:
      assert(i > 0)
      pre_state = trajectory[i-1]
      for lit in preconditions[elem]:
         axiom1 = Implies(lit, precon_to_states[lit])
         axiom1_instances += [axiom1]
      
      # # axiom 2:
      # assert(i < len(trajectory) - 1)
      # post_state = trajectory[i+1]
      # eff = e[elem]
      # axiom2 = Implies(post_state, eff)

      # # axiom 3:
      # # TODO
    is_state = not is_state
  return And(axiom1_instances)

# the action model given by the preconditions is safe for plans that have n steps
# def safe(n, preconditions, trajectories):
#   steps = {}
#   for i in range(0, n):
#     steps[i] = Bool("step" + str(i))
#   is_safe = Forall(steps, Implies(consistent(steps, preconditions), Forall(... bbaaaa)))

solver = Solver()
cons = []
result = consistent(preconditions, trajectories)
cons += [result]
cons = And(cons)
solver.add(cons)
print("constraints:", cons)
result = solver.check()
while result == sat:
  print(result)
  model = solver.model()
#   print("**********************\n", model)
#   print("action model:", model)
#   print("trajectories:", trajectories)
#   print("effects:", effects)
  model_values = []
  for i in range(0, len(preconditions)):
    for j in range(0, len(preconditions[i])):
      model_val = model[preconditions[i][j]]
      if model_val == True:
        model_values += [preconditions[i][j]]
      else:
        model_values += [Not(preconditions[i][j])]
  block_model = Not(And(model_values))
  solver.add(block_model)
  result = solver.check()

