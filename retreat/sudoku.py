import cvc5
from cvc5 import Kind

# load sudoku problem and parse it
with open("sudoku1.txt", "r") as f:
    content = f.read()
lines = content.splitlines()
i = 1
hints = {}
for line in lines:
  for j in range(0,9):
    if line[j] != '0':
      hints[(i,j+1)] = line[j]
  i = i+1

# get solver and enable models
slv = cvc5.Solver()
slv.setOption("produce-models", "true")

# get integer sort and some constants
intSort = slv.getIntegerSort()
one = slv.mkInteger("1")
nine = slv.mkInteger("9")

# define the variables: variables[(i,j)] stands for 
# the number in the ith row and jth column
variables = {}
for i in range(1, 10):
  for j in range(1, 10):
    variables[(i,j)] = slv.mkConst(intSort, "x_" + str(i) + "_" + str(j))

# all variables are between 1 and 9
for i in range(1, 10):
  for j in range(1, 10):
    slv.assertFormula(slv.mkTerm(Kind.LEQ, one, variables[(i,j)]))
    slv.assertFormula(slv.mkTerm(Kind.LEQ, variables[(i,j)], nine))

# all variables in the same row are different
for i in range(1, 10):
  for j in range(1,10):
    for k in range(j+1, 10):
      slv.assertFormula(slv.mkTerm(Kind.DISTINCT, variables[(i,j)], variables[(i,k)]))

# all variables in the same column are different
for j in range(1, 10):
  for i in range(1,10):
    for k in range(i+1, 10):
      slv.assertFormula(slv.mkTerm(Kind.DISTINCT, variables[(i,j)], variables[(k,j)]))

# all variables in the same square are different
for top_left in [(1,1), (1,4), (1,7), (4,1), (4,4), (4,7), (7,1), (7,4), (7,7)]:
  places_in_cube = [(top_left[0] + a, top_left[1] + b) for a in range(0,3) for b in range(0,3)]
  for i in range(0,9):
    for j in range(i+1,9):
      slv.assertFormula(slv.mkTerm(Kind.DISTINCT, variables[places_in_cube[i]], variables[places_in_cube[j]]))
 
# the values from the input problem
for key in hints.keys():
  val = slv.mkInteger(hints[key])
  slv.assertFormula(slv.mkTerm(Kind.EQUAL, variables[key], val))

# check if there is a solution
result = slv.checkSat()
print("there is a solution" if result.isSat() else "there is no solution")
if result.isSat():
  print("solution:")
  for i in range(1,10):
    print(" ".join([str(slv.getValue(variables[(i,j)])) for j in range(1,10)]))
  
  # check if there is another solution
  slv.blockModel(cvc5.BlockModelsMode.VALUES)
  result = slv.checkSat()
  print("there is another solution" if result.isSat() else "there are no more solutions")
