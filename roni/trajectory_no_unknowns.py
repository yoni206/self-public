from cvc5.pythonic import *
import pprint

num_of_state_variables = 2
num_of_actions = 2

# effects
# effects[i][j]
# the effect of action i on state var j
add_effects = {}
del_effects = {}
for i in range(num_of_actions):
  for s in range(num_of_state_variables):
    new_add_eff_var = Bool("f" + str(s) + "_in_add_eff_of_action_" + str(i))
    new_del_eff_var = Bool("f" + str(s) + "_in_del_eff_of_action_" + str(i))
    add_effects[(i,s)] = new_add_eff_var
    del_effects[(i,s)] = new_del_eff_var

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

def consistent(preconditions, add_effects, del_effects, trajectories):
  axiom1_instances = []
  axiom2_instances = []
  for i in range(num_of_state_variables):
    # j is index, trajectory is trajectory
    for j, trajectory in enumerate(trajectories):
      for k in range(int((len(trajectory) - 1) / 2)):
        action = trajectory[2*k+1]
        precondition_var = preconditions[(action, i)]
        axiom1 = Implies(precondition_var, trajectory[2*k][i])
        axiom1_instances += [axiom1]
      
      # axiom 2:
      # if fi is in add effect of action, then fi must be true in the next state
      # if fi is in del effect of action, then fi must be false in the next state
      # if fi is neither in add nor del effect of action, then fi stays the same as in the previous state (closed world)
        add_effect_var = add_effects[(action, i)]
        del_effect_var = del_effects[(action, i)]
        post_value = trajectory[2*k+2][i]
        pre_value = trajectory[2*k][i]
        axiom2_part1 = Implies(add_effect_var, post_value)
        axiom2_part2 = Implies(del_effect_var, not(post_value))
        axiom2_part3 = Implies(Not(Or(add_effect_var, del_effect_var)), pre_value==post_value)
        axiom2 = And(axiom2_part1, axiom2_part2, axiom2_part3)
        axiom2_instances += [axiom2]


  return And(axiom1_instances + axiom2_instances)

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
result = consistent(preconditions, add_effects, del_effects, trajectories)

solver.add(result)
result = solver.check()
action_models_and_num_of_trues = []
num_of_models = 0
while result == sat:
  num_of_models += 1
  print("panda", num_of_models)
  model = solver.model()
  dict_model = {decl:model[decl] for decl in model}
  action_models_and_num_of_trues += [(dict_model, count_trues(model))]
  print("**********************\n")
  print("action model:")
  print("\n".join(str(model).split(",")))
  model_values = []
  variables = []
  for p in preconditions.values():
    variables += [p]
  for p in add_effects.values():
    variables += [p]
  for p in del_effects.values():
    variables += [p]
  for p in variables:
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
assert(len(safe_models) == 1)
for safe_model in safe_models:
  print("***********")
  print("safe model:")
  print("\n".join(str(safe_model).split(",")))



# action model: preconditions, add effects, del effects
# traj: sequence of state action state action
# traj consistent with action model: axioms 1 and 2
# action model is safe if: every trajectory that is consistent with it, is consistent with all action models that are consistent with the original trajectories.

