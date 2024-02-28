import copy
import cvc5
from cvc5 import Kind

# ###########################################
# Functions copied from 
# https://github.com/cvc5/cvc5/blob/main/examples/api/python/utils.py
# ##########################################
def define_fun_to_string(f, params, body):
    sort = f.getSort()
    if sort.isFunction():
        sort = f.getSort().getFunctionCodomainSort()
    result = "(define-fun " + str(f) + " ("
    for i in range(0, len(params)):
        if i > 0:
            result += " "
        result += "(" + str(params[i]) + " " + str(params[i].getSort()) + ")"
    result += ") " + str(sort) + " " + str(body) + ")"
    return result

def print_synth_solutions(terms, sols):
    result = "(\n"
    for i in range(0, len(terms)):
        params = []
        body = sols[i]
        if sols[i].getKind() == Kind.LAMBDA:
            params += sols[i][0]
            body = sols[i][1]
        result += "  " + define_fun_to_string(terms[i], params, body) + "\n"
    result += ")"
    print(result)

###########################################
# Real Example
###########################################

slv = cvc5.Solver()

# required options
slv.setOption("sygus", "true")
slv.setOption("incremental", "false")

# set the logic
slv.setLogic("ALL")

nullary = slv.mkDatatypeConstructorDecl("nullary")
unary = slv.mkDatatypeConstructorDecl("unary")
unary.addSelectorSelf("param")
sort = slv.declareDatatype("Sort", nullary, unary)


y = slv.mkVar(sort, "y")

f1 = slv.synthFun("f1", [y], sort)
f2 = slv.synthFun("f2", [y], sort)
  

# declare universal variables.
varX = slv.declareSygusVar("x", sort)
varParam = slv.declareSygusVar("param", sort)



# add semantic constraints
unary_cons = sort.getDatatype().getConstructor("unary").getTerm()
nullary_cons = sort.getDatatype().getConstructor("nullary").getTerm()
up = slv.mkTerm(Kind.APPLY_CONSTRUCTOR, unary_cons, varParam)
left = slv.mkTerm(Kind.EQUAL, varX, up)
f1p = slv.mkTerm(Kind.APPLY_UF, f1, varParam)
n = slv.mkTerm(Kind.APPLY_CONSTRUCTOR, nullary_cons)
right1 = slv.mkTerm(Kind.EQUAL, f1p, n)
f2p = slv.mkTerm(Kind.APPLY_UF, f2, varParam)
uf2p = slv.mkTerm(Kind.APPLY_CONSTRUCTOR, unary_cons, f2p)
right2 = slv.mkTerm(Kind.EQUAL, varX, uf2p)
right = slv.mkTerm(Kind.AND, right1, right2)
constraint = slv.mkTerm(Kind.IMPLIES, left, right)
slv.addSygusConstraint(constraint)

# print solutions if available
if (slv.checkSynth().hasSolution()):
  terms = [f1, f2]
  print_synth_solutions(terms, slv.getSynthSolutions(terms))
