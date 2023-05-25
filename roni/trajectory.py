from cvc5.pythonic import *
import pprint


UNKNOWN="unknown"
unknowns = {}

###################### BEGIN-INPUT-1 ####################
num_of_state_variables = 2
num_of_actions = 2
trajectories = [
 [[True, True], 0, [True, True], 0, [True, True]],
 [[True, True], 1, [True, True], 1, [True, True]],
 [[True, True], 0, [True, True], 0, [True, True]]
]
###################### END-INPUT-1 ####################

# ###################### BEGIN-INPUT-1 ####################
# num_of_state_variables = 2
# num_of_actions = 2
# trajectories = [
#  [[True, True], 0, [True, UNKNOWN], 0, [True, False]],
#  [[True, True], 1, [True, False], 1, [True, False]],
#  [[False, True], 0, [False, False], 0, [False, False]]
# ]
# ###################### END-INPUT-1 ####################

# ###################### BEGIN-INPUT-2 ####################
# num_of_state_variables = 1
# num_of_actions = 1
# trajectories = [
#   [[True],0,[UNKNOWN]],
#   [[False],0,[UNKNOWN]]
# ]
# ###################### END-INPUT-2 ####################



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


def key_to_str(key):
  return str(key[0]) + "_" + str(key[1]) + "_" + str(key[2])

def consistent(preconditions, add_effects, del_effects, trajectories):
  axiom1_instances = []
  axiom2_instances = []
  for i in range(num_of_state_variables):
    # j is index, trajectory is trajectory
    for j, trajectory in enumerate(trajectories):
      for k in range(int((len(trajectory) - 1) / 2)):
        action = trajectory[2*k+1]
        post_value = trajectory[2*k+2][i]
        pre_value = trajectory[2*k][i]
        precondition_var = preconditions[(action, i)]
        pre_value_term = None
        post_value_term = None
        if pre_value == UNKNOWN:
          key = (j,k,i)
          if key not in unknowns:
            unknowns[key] = Bool("unknown_var_of_traj_step_var" + key_to_str(key))
          pre_value_term = unknowns[key]
        else:
          pre_value_term = pre_value

        if post_value == UNKNOWN:
          key = (j,k+1,i)
          if key not in unknowns:
            unknowns[key] = Bool("unknown_var_of_traj_step_var" + key_to_str(key))
          post_value_term = unknowns[key]
        else:
          post_value_term = post_value

        axiom1 = Implies(precondition_var, pre_value_term)
        axiom1_instances += [axiom1]
      
      # axiom 2:
      # if fi is in add effect of action, then fi must be true in the next state
      # if fi is in del effect of action, then fi must be false in the next state
      # if fi is neither in add nor del effect of action, then fi stays the same as in the previous state (closed world)
        add_effect_var = add_effects[(action, i)]
        del_effect_var = del_effects[(action, i)]
        axiom2_part1 = Implies(add_effect_var, post_value_term)
        axiom2_part2 = Implies(del_effect_var, Not(post_value_term))
        print("pre_value_term", pre_value_term)
        print("post_value_term", post_value_term)
        iff = And(Implies(pre_value_term, post_value_term), Implies(post_value_term, pre_value_term))
        axiom2_part3 = Implies(Not(Or(add_effect_var, del_effect_var)), iff)
        axiom2 = And(axiom2_part1, axiom2_part2, axiom2_part3)
        axiom2_instances += [axiom2]


  return And(axiom1_instances + axiom2_instances)



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
models = []
while result == sat:
  m = {}
  model = solver.model()
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
        m[p] = model_val
        if model_val == True:
          model_values += [p]
        else:
          model_values += [Not(p)]
  models.append(m)
  model_formula = And(model_values)
  block_model = Not(model_formula)
  print("number of models: ", len(models))
  solver.add(block_model)
  result = solver.check()

# safety: preconditions
safe_model = {}
ambiguous_actions = set([])
for i in range(num_of_actions):
  for j in range(num_of_state_variables):
    precon_var = preconditions[(i,j)]
    add_effect_var = add_effects[(i,j)]
    del_effect_var = del_effects[(i,j)]
    safe_model[precon_var] = False
    for m in models:
      if m[precon_var] == True:
        safe_model[precon_var] = True
        break
    expected_value_add = None
    expected_value_del = None
    for m in models:
      if expected_value_add == None:
          expected_value_add = m[add_effect_var]
      if expected_value_del == None:
          expected_value_del = m[del_effect_var]
      if str(m[add_effect_var]) != str(expected_value_add):
        ambiguous_actions.add(i)
      else:
        safe_model[add_effect_var] = expected_value_add
      if str(m[del_effect_var]) != str(expected_value_del):
        ambiguous_actions.add(i)
      else:
        safe_model[del_effect_var] = expected_value_del
        break
    
print("safe model: ", safe_model)
print("ambiguous_actions", ambiguous_actions)
# safety: actions




# action model: preconditions, add effects, del effects
# traj: sequence of state action state action
# traj consistent with action model: axioms 1 and 2
# action model is safe if: every trajectory that is consistent with it, is consistent with all action models that are consistent with the original trajectories.

