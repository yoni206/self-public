from cvc5.pythonic import *
import pprint


UNKNOWN="unknown"
unknowns = {}

# ###################### BEGIN-INPUT-1 ####################
# num_of_state_variables = 2
# num_of_actions = 2
# trajectories = [
#  [[UNKNOWN, UNKNOWN], 0, [True, UNKNOWN], 0, [UNKNOWN, UNKNOWN]],
#  [[UNKNOWN, False], 1, [UNKNOWN, UNKNOWN], 1, [UNKNOWN, True]],
#  [[UNKNOWN, UNKNOWN], 0, [UNKNOWN, UNKNOWN], 0, [UNKNOWN, UNKNOWN]]
# ]
# ###################### END-INPUT-1 ####################

#################### BEGIN-INPUT-1 ####################
num_of_state_variables = 2
num_of_actions = 2
trajectories = [
 [[True, True], 0, [True, UNKNOWN], 0, [True, False]],
 [[True, True], 1, [True, False], 1, [True, False]],
 [[False, True], 0, [False, False], 0, [False, False]]
]
#################### END-INPUT-1 ####################

# ####################### BEGIN-INPUT-2 ####################
# num_of_state_variables = 1
# num_of_actions = 1
# trajectories = [
#   [[True],0,[UNKNOWN]],
#   [[False],0,[UNKNOWN]]
# ]
###################### END-INPUT-2 ####################






##################################################
##### HELPER FUNCTIONS ###########################
###################################################
def naive_safe_model(models):
  # find a safe model manually
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
          break
        else:
          safe_model[add_effect_var] = expected_value_add
        if str(m[del_effect_var]) != str(expected_value_del):
          ambiguous_actions.add(i)
          break
        else:
          safe_model[del_effect_var] = expected_value_del
  return safe_model, ambiguous_actions



# M -- the safe model candidate
# Mprimt -- one of the consistent models
def complicated_check(Mprime, M, ambiguous_actions):
  for i in range(num_of_actions):
    if i in ambiguous_actions:
      continue
    for j in range(num_of_state_variables):
      precon_var = preconditions[(i,j)]
      add_effect_var = add_effects[(i,j)]
      del_effect_var = del_effects[(i,j)]
      is_in_precon_of_m = M[precon_var]
      is_in_precon_of_mprime = Mprime[precon_var]
      is_in_add_effect_of_m = M[add_effect_var] 
      is_in_add_effect_of_mprime = Mprime[add_effect_var] 
      is_in_del_effect_of_m = M[del_effect_var] 
      is_in_del_effect_of_mprime = Mprime[del_effect_var] 

      second_if = is_in_add_effect_of_m and is_in_del_effect_of_mprime

      if not is_in_precon_of_m and is_in_precon_of_mprime:
          return True

      if is_in_add_effect_of_m and is_in_del_effect_of_mprime:
          return True

      if is_in_add_effect_of_m and not is_in_add_effect_of_mprime:
          if is_in_precon_of_mprime:
            print("no worries")
          else: 
            return True
      
      if is_in_add_effect_of_mprime and not is_in_add_effect_of_m:
          if is_in_precon_of_m:
            print("no worries")
          else:
            return True

  return False



def is_safe(consistent_models, model, ambiguos_actions):
    if consistent_models == None:
        consistent_models = compute_all_consistent_models()
    result = True
    for cm in consistent_models:
        if complicated_check(cm, model, ambiguos_actions):
            result = False
            break
    return result

def compute_all_consistent_models():
  result = consistent(preconditions, add_effects, del_effects, trajectories, unknowns)
  
  solver.add(result)
  result = solver.check()
  if result != sat:
      print("no consistent models")
      exit()
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
  return models

def relatively_brute_force():
  models = compute_all_consistent_models()
  safe_model, ambiguous_actions = naive_safe_model(models)
  if is_safe(models, safe_model, ambiguous_actions):
    print("indeed safe")
  else:
    print("reported safe but is not safe")
  
  print("safe model:")
  print("\n".join(str(safe_model).split(",")))
  print("ambiguous_actions", ambiguous_actions)




def qbf_safe_model():
    # new variables for safe model (for each i,j):
    #  - add_eff, del_eff, precon
    # forall action and state variable, if there is a model
    # for which the state variable is in the precon for 
    # the action, then the state variable is also a precon
    # to the action in the safe model

  existential_add_effects = {}
  existential_del_effects = {}
  for i in range(num_of_actions):
    for s in range(num_of_state_variables):
      new_add_eff_var = Bool("existsential_f" + str(s) + "_in_add_eff_of_action_" + str(i))
      new_del_eff_var = Bool("existential_f" + str(s) + "_in_del_eff_of_action_" + str(i))
      existential_add_effects[(i,s)] = new_add_eff_var
      existential_del_effects[(i,s)] = new_del_eff_var

  # preconditions
  existential_preconditions = {}
  for i in range(num_of_actions):
    for s in range(num_of_state_variables):
      new_precon_var = Bool("existential_f" + str(s) + "_in_precon_of_action_" + str(i))
      existential_preconditions[(i,s)] = new_precon_var

  
  # unkowns
  existential_unknowns = {}
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
          if key not in existential_unknowns:
            existential_unknowns[key] = Bool("unknown_var_of_traj_step_var" + key_to_str(key))
          pre_value_term = existential_unknowns[key]
        else:
          pre_value_term = pre_value

        if post_value == UNKNOWN:
          key = (j,k+1,i)
          if key not in existential_unknowns:
            existential_unknowns[key] = Bool("unknown_var_of_traj_step_var" + key_to_str(key))
          post_value_term = existential_unknowns[key]
        else:
          post_value_term = post_value



  bound_vars = list(existential_add_effects.values()) + list(existential_del_effects.values()) + list(existential_preconditions.values()) + list(existential_unknowns.values())
  for i in range(num_of_actions):
    for s in range(num_of_state_variables):
      exists_precon = Exists(bound_vars, And(consistent(existential_preconditions, existential_add_effects, existential_del_effects, trajectories, existential_unknowns), existential_preconditions[(i,s)]))
      eq1 = preconditions[(i,s)]
      # exists m' . m' is consistent and in it, s is a precon of i ===> s is a precon of i in the (safe)  model that we are searching for. 
      formula_precon = And(Implies(exists_precon, eq1), Implies(eq1, exists_precon))

      forall_add_eff = ForAll(bound_vars, Implies(consistent(existential_preconditions, existential_add_effects, existential_del_effects, trajectories, existential_unknowns), existential_add_effects[(i,s)]))
      eq2 = add_effects[(i,s)]
      formula_add_eff = And(Implies(forall_add_eff, eq2), Implies(eq2, forall_add_eff))


      forall_del_eff = ForAll(bound_vars, Implies(consistent(existential_preconditions, existential_add_effects, existential_del_effects, trajectories, existential_unknowns), existential_del_effects[(i,s)]))
      eq3 = del_effects[(i,s)]
      formula_del_eff = And(Implies(forall_del_eff, eq3), Implies(eq3, forall_del_eff))

      never_add_eff = ForAll(bound_vars, Implies(consistent(existential_preconditions, existential_add_effects, existential_del_effects, trajectories, existential_unknowns), Not(existential_add_effects[(i,s)])))
      
      never_del_eff = ForAll(bound_vars, Implies(consistent(existential_preconditions, existential_add_effects, existential_del_effects, trajectories, existential_unknowns), Not(existential_del_effects[(i,s)])))
      
      or_add = Or(forall_add_eff, never_add_eff)
      or_del = Or(forall_del_eff, never_del_eff)
      and_or = And(or_add, or_del)

      formula_good_actions = And(Implies(is_good_action[(i,s)], and_or), Implies(and_or, is_good_action[(i,s)]))

      solver.add(formula_precon)
      solver.add(formula_add_eff)
      solver.add(formula_del_eff)
      solver.add(formula_good_actions)
  result = solver.check()
  if result != sat:
      print("no consistent models")
      exit()
  model = solver.model()
  print("\n".join(str(model).split(",")))
  if is_safe(None, model, ambiguous_actions):
    print("indeed safe")
  else:
    print("reported safe but is not safe")





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

is_good_action = {}
for i in range(num_of_actions):
  for s in range(num_of_state_variables):
    is_good_action[(i,s)] = Bool("a" + str(i) + "_is_a_good_action_for_f" + str(s))


def key_to_str(key):
  return str(key[0]) + "_" + str(key[1]) + "_" + str(key[2])

def consistent(preconditions, add_effects, del_effects, trajectories, local_unknowns):
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
          if key not in local_unknowns:
            local_unknowns[key] = Bool("unknown_var_of_traj_step_var" + key_to_str(key))
          pre_value_term = local_unknowns[key]
        else:
          pre_value_term = pre_value

        if post_value == UNKNOWN:
          key = (j,k+1,i)
          if key not in local_unknowns:
            local_unknowns[key] = Bool("unknown_var_of_traj_step_var" + key_to_str(key))
          post_value_term = local_unknowns[key]
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
        iff = And(Implies(pre_value_term, post_value_term), Implies(post_value_term, pre_value_term))
        axiom2_part3 = Implies(Not(Or(add_effect_var, del_effect_var)), iff)
        axiom2 = And(axiom2_part1, axiom2_part2, axiom2_part3)
        axiom2_instances += [axiom2]


  return And(axiom1_instances + axiom2_instances)




solver = Solver()
# relatively_brute_force()
qbf_safe_model()
# relatively_brute_force()
