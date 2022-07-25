import cvc5
from cvc5 import Kind
import itertools
import sys

def validate(donors, recipients, edges):
    # no duplicates is a given since we are using sets

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

def gen_at_most_one(vars, solver):
    result = solver.mkTrue()
    for v in vars:
        for u in vars:
            if v != u:
                both = solver.mkTerm(Kind.AND, v, u)
                not_both = solver.mkTerm(Kind.NOT, both)
                result = solver.mkTerm(Kind.AND, result, not_both)
    return result

def gen_at_most_k(vars, solver, k):
    result = solver.mkTrue()
    for I in itertools.combinations(vars, k+1):
        disj = solver.mkFalse()
        for x in I:
            neg_x = solver.mkTerm(Kind.NOT, x)
            disj = solver.mkTerm(Kind.OR, disj, neg_x)
        result = solver.mkTerm(Kind.AND, result, disj)
    return result

def mk_nry_term(kind, terms):
    assert kind in [Kind.OR, Kind.AND]
    if kind == Kind.OR:
        result = solver.mkFalse()
    if kind == Kind.AND:
        result = solver.mkTrue()
    for t in terms:
        result = solver.mkTerm(kind, t, result)
    return result
    
solver = cvc5.Solver()
solver.setOption("produce-models", "true")

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


# bool sort
bool_sort = solver.getBooleanSort()

# create variables for edges
variables = {}
for e in edges:
    variables[e] = solver.mkConst(bool_sort, str(e))
for d in donors:
    assert d not in variables
    variables[d] = solver.mkConst(bool_sort, str(d))

# Every recipient node appears at most once
for recipient in recipients_to_edges:
    edges_to_recipient = recipients_to_edges[recipient]
    edges_vars = [variables[e] for e in edges_to_recipient]
    at_most_one = gen_at_most_one(edges_vars, solver)
    solver.assertFormula(at_most_one)

# if donor is on edge that was selected, the donor is selected
for donor in donors_to_edges:
    edges_from_donor = donors_to_edges[donor]
    variables_for_edges = [variables[e] for e in edges_from_donor]
    some_edge_selected = mk_nry_term(Kind.OR, variables_for_edges)
    equivalence = solver.mkTerm(Kind.EQUAL, variables[donor], some_edge_selected)
    solver.assertFormula(equivalence)
    

# Number of donors is bounded by k
at_most_k = gen_at_most_k([variables[d] for d in donors], solver, donor_bound)
solver.assertFormula(at_most_k)


# construct goal node
zero = solver.mkInteger(0)
goal = zero
for e in edges:
    recipient = e[1]
    variable = variables[e]
    mult = solver.mkInteger(label[e]*label[recipient])
    ite = solver.mkTerm(Kind.ITE, variable, mult, zero)
    goal = solver.mkTerm(Kind.ADD, goal, ite)

# check sat
sat = solver.checkSat()

if not sat.isSat():
    print("unsat")
    exit()

# optimize
goal_val = -1
while sat.isSat():
    goal_val = solver.getValue(goal)
    selected_edges = [e for e in edges if solver.getValue(variables[e]).getBooleanValue()]    
    
    # print("candidate edges: ", selected_edges)
    # print("candidate goal: ", goal_val)


    bound = solver.mkTerm(Kind.GT, goal, goal_val)
    solver.assertFormula(bound)
    sat = solver.checkSat()


print("chosen edges: ", selected_edges)
print("maximal score: ", goal_val)


# gurobi
# front end similar to smt
# bv instead of int
# --int-to-bv --bool-to-bv
# --eager-bit-blasting