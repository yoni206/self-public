import pysat
from pysat.solvers import Glucose3
from pysat.formula import CNF, CNFPlus
from pysat.card import CardEnc
from pysat.pb import *
import itertools
import sys

def validate(donors, recipients, edges):
    # no duplicates is a given since we are using sets
    assert(True)

    # check that donors and recipients are disjoint
    for d in donors:
        for r in recipients:
            assert(d != r)

    # check that edges are pairs of existing nodes
    for e in edges:
        node1 = e[0]
        node2 = e[1]
        assert(node1 in donors)
        assert(node2 in recipients)

solver = Glucose3()

donors_csv = sys.argv[1]
recipients_csv = sys.argv[2]
edges_csv = sys.argv[3]
donor_bound = int(sys.argv[4])

label = {}
edges = set([])
donors = set([])
recipients = set([])

with open(donors_csv, 'r') as f:
    lines = f.readlines()
    lines = [l.strip() for l in lines]
    lines = [l for l in lines if not l.startswith("#")]
    for l in lines:
        node, weight = l.split(",")
        node = "donor_" + node.strip()
        weight = weight.strip()
        donors.add(node)
        label[node] = int(weight)

with open(recipients_csv, 'r') as f:
    lines = f.readlines()
    lines = [l.strip() for l in lines]
    lines = [l for l in lines if not l.startswith("#")]
    for l in lines:
        node, weight = l.split(",")
        node = "recipient_" + node.strip()
        weight = weight.strip()
        recipients.add(node)
        label[node] = int(weight)

with open(edges_csv, 'r') as f:
    lines = f.readlines()
    lines = [l.strip() for l in lines]
    lines = [l for l in lines if not l.startswith("#")]
    for l in lines:
        edge, weight = l.split(",")
        node1, node2 = edge.split(";")
        node1 = "donor_" + node1.strip()
        node2 = "recipient_" + node2.strip()
        edge = (node1, node2)
        edges.add(edge)
        weight = weight.strip()
        label[edge] = int(weight)
    validate(donors, recipients, edges)
print("debug: number of edges: ", len(edges))

# map recipients to edges
recipients_to_edges = {}
donors_to_edges = {}
for e in edges:
    donor = e[0]
    recipient = e[1]
    if recipient not in recipients_to_edges:
        recipients_to_edges[recipient] = set([])
    recipients_to_edges[recipient].add(e)
    if donor not in donors_to_edges:
        donors_to_edges[donor] = set([])
    donors_to_edges[donor].add(e)

# create variables for edges and donors
counter = 1
variables = {}
variables_to_edges = {}
for e in edges:
    variables[e] = counter
    variables_to_edges[counter] = e
    counter += 1
largest_index_for_edges = counter - 1
assert(counter - 1 == len(variables))

for d in donors:
    assert d not in variables
    variables[d] = counter 
    counter += 1

assert(counter - 1 == len(variables))
print("debug: number of variables: ", len(variables))
largest_index = counter - 1

# create a formula (cnf + carindality constraints)
cnfp = CNFPlus()

# Every recipient node appears at most once
for recipient in recipients_to_edges:
    edges_to_recipient = recipients_to_edges[recipient]
    edges_vars = [variables[e] for e in edges_to_recipient]
    at_most_one_cnfp = CardEnc.atmost(lits=edges_vars, bound=1, top_id=largest_index)
    cnfp.extend(at_most_one_cnfp)

print("debug: computed and asserted at most one constraint for recipients")

# if donor is on edge that was selected, the donor is selected. and only if
for donor in donors_to_edges:
    edges_from_donor = donors_to_edges[donor]
    variables_for_edges = [variables[e] for e in edges_from_donor]
    some_edge_selected = variables_for_edges
    if_direction_cnf = [variables_for_edges] + [[-variables[donor]]]
    only_if_direction_cnf = [[-v, variables[donor]] for v in variables_for_edges]
    iff_cnf = if_direction_cnf + only_if_direction_cnf
    print("panda", iff_cnf)
    iff_cnfp = CNF(from_clauses=iff_cnf)
    cnfp.extend(iff_cnfp)


print("debug: computed and asserted edge to donor constraints")


# Number of donors is bounded by k
at_most_k_cnfp = CardEnc.atmost(lits=[variables[d] for d in donors], bound=donor_bound, top_id=cnfp.nv)
print("debug: computed at most k constraints")
cnfp.extend(at_most_k_cnfp)
print("debug: added at most k constraints")

lits_to_weights = {variables[e]:label[e]*label[e[1]] for e in edges}

lits = []
weights = []
for k in lits_to_weights.keys():
    v = lits_to_weights[k]
    lits += [k]
    weights += [v]

# check sat
print("debug: about to call check-sat for the first time")
solver.append_formula(cnfp)
sat = solver.solve()

if not sat:
    print("unsat")
    exit()

print("debug: largest index for edges: ", largest_index_for_edges)
# optimize
goal_val = -1
iteration = 1
while sat:
    print("debug: *****************************")
    print("debug: iteration:", iteration)
    iteration += 1
    print("debug: asking for the current value of the goal")
    model = solver.get_model()
    goal_val = 0
    selected_edges = []
    for lit in model:
        if lit > 0 and lit <= largest_index_for_edges:
            print("debug: lit: ", lit)
            weight = lits_to_weights[lit]
            goal_val += weight
            selected_edges += [variables_to_edges[lit]]
    print("debug: got the current value of the goal")
    
    # print("candidate edges: ", selected_edges)
    # print("candidate goal: ", goal_val)

    print("debug: creating the new bound: ", goal_val)
    bound_cnf = pysat.pb.PBEnc.atleast(lits=lits, weights=weights, bound=goal_val+1)
    print("debug: about to assert the bound to the solver")
    solver.append_formula(bound_cnf)
    print("debug: about to call check-sat")
    sat = solver.solve()


print("chosen edges: ", selected_edges)
print("chosen donors: ", set([d for (d,r) in selected_edges]))
print("maximal score: ", goal_val)


# gurobi
# front end similar to smt
# bv instead of int
# --int-to-bv --bool-to-bv
# --eager-bit-blasting
