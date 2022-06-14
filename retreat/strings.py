# Are there non-empty strings x,y,z such that x.ab.y == abc.z ?

import cvc5
from cvc5 import Kind

# get solver and enable models
slv = cvc5.Solver()
slv.setOption("produce-models", "true")

# String type and values
string = slv.getStringSort()
ab  = slv.mkString("ab")
abc = slv.mkString("abc")

# String variables
x = slv.mkConst(string, "x")
y = slv.mkConst(string, "y")
z = slv.mkConst(string, "z")

# x.ab.y
lhs = slv.mkTerm(Kind.STRING_CONCAT, x, ab, y)

# abc.z
rhs = slv.mkTerm(Kind.STRING_CONCAT, abc, z)

# x.ab.y = abc.z
formula1 = slv.mkTerm(Kind.EQUAL, lhs, rhs)

# Lengths of x,y,z
lenx = slv.mkTerm(Kind.STRING_LENGTH, x)
leny = slv.mkTerm(Kind.STRING_LENGTH, y)
lenz = slv.mkTerm(Kind.STRING_LENGTH, z)

# |x|,|y|,|z| >= 1
formula2 = slv.mkTerm(Kind.GEQ, lenx, slv.mkInteger(1))
formula3 = slv.mkTerm(Kind.GEQ, leny, slv.mkInteger(1))
formula4 = slv.mkTerm(Kind.GEQ, lenz, slv.mkInteger(1))

# Assert formulas
slv.assertFormula(slv.mkTerm(Kind.AND, formula1, formula2, formula3, formula4))

# check and print result
result = slv.checkSat()
print("cvc5 reports:", result)

# print model if sat
if result.isSat():
    print("x = ", slv.getValue(x))
    print("y = ", slv.getValue(y))
    print("z = ", slv.getValue(z))
