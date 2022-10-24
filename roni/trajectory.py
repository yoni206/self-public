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
  for s in range(num_of_state_variables):
    new_precon_var = Bool("f" + str(s) + "_in_precon_of_action_" + str(i))
    preconditions[(i,s)] = new_precon_var


print(precon_to_states)

# A set of trajectories. Each trajectory is a list. 
# But here we do a list of trajectories becausei lists are not hashable.
trajectories = [
# first trajectory
[[True, True], 0, [True, False], 0, [True, False]],
# ...
# last trajectory
[[False, True], 0, [False, False], 0, [False, False]]
]


solver = Solver()


def consistent(preconditions, trajectories):
  axiom1_instances = []
  state_variable_in_trajectory_step = {}
  for i in range(num_of_state_variables):
    for j, trajectory in enumerate(trajectories):
      print("panda j: ", str(j))
      print("panda trajectory: ", str(trajectory))
      for k in range(int((len(trajectory) - 1) / 2)):
        state_variable_in_trajectory_step[(i,j,k)] = Bool("state_var_" + str(i) + "_in_traj_" + str(j) + "_on_step_" + str(k))
        action = trajectory[2*k+1]
        precondition_var = preconditions[action, i]
        axiom1 = Implies(state_variable_in_trajectory_step[(i,j,k)], preconditions[action,i])
        axiom1_instances += [axiom1]
      
      # # axiom 2:
      # assert(i < len(trajectory) - 1)
      # post_state = trajectory[i+1]
      # eff = e[elem]
      # axiom2 = Implies(post_state, eff)

      # # axiom 3:
      # # TODO
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
solver.add(result)
print("constraints:", result)
result = solver.check()
while result == sat:
  print(result)
  model = solver.model()
  print("**********************\n", model)
  print("action model:", model)
  print("trajectories:", trajectories)
  print("effects:", effects)
  model_values = []
  for p in preconditions.values():
      model_val = model[p]
      if model_val == True:
        model_values += [p]
      else:
        model_values += [Not(p)]
  block_model = Not(And(model_values))
  solver.add(block_model)
  result = solver.check()

