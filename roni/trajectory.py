from cvc5.pythonic import *
import pprint

num_of_state_variables = 2
num_of_actions = 2

# effects
# effects[i][j]
# the effect of action i on state var j
effects = {}
effects[0] = {}
effects[0][1] = False
effects[1] = {}
effects[1][1] = False


# mapping from preconditions to state variables

# preconditions
preconditions = {}
for i in range(num_of_actions):
  for s in range(num_of_state_variables):
    new_precon_var = Bool("f" + str(s) + "_in_precon_of_action_" + str(i))
    preconditions[(i,s)] = new_precon_var


# A set of trajectories. Each trajectory is a list. 
# But here we do a list of trajectories becausei lists are not hashable.
trajectories = [
# first trajectory
[[True, True], 0, [True, False], 0, [True, False]],
[[True, True], 1, [True, False], 1, [True, False]],
# ...
# last trajectory
[[False, True], 0, [False, False], 0, [False, False]]
]

def consistent(preconditions, trajectories):
  axiom1_instances = []
  state_variable_in_trajectory_step = {}
  for i in range(num_of_state_variables):
    # j is index, trajectory is trajectory
    for j, trajectory in enumerate(trajectories):
      for k in range(int((len(trajectory) - 1) / 2)):
        state_variable_in_trajectory_step[(i,j,k)] = Bool("state_var_" + str(i) + "_in_traj_" + str(j) + "_on_step_" + str(k))
        action = trajectory[2*k+1]
        precondition_var = preconditions[(action, i)]
        axiom1 = Implies(precondition_var, trajectory[2*k][i])
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

def count_trues(action_model):
  result = 0
  for i in range(len(action_model.decls())):
    if action_model[action_model[i]] == True:
      result += 1
  return result

solver = Solver()
cons = []
result = consistent(preconditions, trajectories)
solver.add(result)
result = solver.check()
action_models_and_num_of_trues = []
while result == sat:
  model = solver.model()
  dict_model = {decl:model[decl] for decl in model}
  action_models_and_num_of_trues += [(dict_model, count_trues(model))]
  print("**********************\n")
  print("action model:")
  print("\n".join(str(model).split(",")))
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

safe_models = []
max_trues = max(amanoft[1] for amanoft in action_models_and_num_of_trues)
safe_models = [amanoft[0] for amanoft in action_models_and_num_of_trues if amanoft[1]==max_trues]
for safe_model in safe_models:
  print("***********")
  print("safe model:")
  print("\n".join(str(safe_model).split(",")))

