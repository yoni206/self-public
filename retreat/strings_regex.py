# Are there non-empty strings x,y,z such that x.y.z is in the regular language
# defined by (ab[c-e]*f)|g|h

import cvc5
from cvc5 import Kind

# get solver and enable models
slv = cvc5.Solver()
slv.setOption("produce-models", "true")
slv.setOption("strings-exp", "true")

# String type
string = slv.getStringSort()

# String variables
x = slv.mkConst(string, "x")
y = slv.mkConst(string, "y")
z = slv.mkConst(string, "z")

# Lengths of x,y,z
lenx = slv.mkTerm(Kind.STRING_LENGTH, x)
leny = slv.mkTerm(Kind.STRING_LENGTH, y)
lenz = slv.mkTerm(Kind.STRING_LENGTH, z)

# |x|,|y|,|z| >= 1
formula1 = slv.mkTerm(Kind.GEQ, lenx, slv.mkInteger(1))
formula2 = slv.mkTerm(Kind.GEQ, leny, slv.mkInteger(1))
formula3 = slv.mkTerm(Kind.GEQ, lenz, slv.mkInteger(1))

# Regular expression: (ab[c-e]*f)|g|h
r = slv.mkTerm(Kind.REGEXP_UNION,
               slv.mkTerm(Kind.REGEXP_CONCAT,
                          slv.mkTerm(Kind.STRING_TO_REGEXP,
                                     slv.mkString("ab")),
                          slv.mkTerm(Kind.REGEXP_STAR,
                                     slv.mkTerm(Kind.REGEXP_RANGE,
                                     slv.mkString("c"),
                                     slv.mkString("e"))),
                        slv.mkTerm(Kind.STRING_TO_REGEXP,
                                   slv.mkString("f"))),
             slv.mkTerm(Kind.STRING_TO_REGEXP, slv.mkString("g")),
             slv.mkTerm(Kind.STRING_TO_REGEXP, slv.mkString("h")))

# String concatenation: x.y.z
s = slv.mkTerm(Kind.STRING_CONCAT, x, y, z)

# s in (ab[c-e]*f)|g|h
formula4 = slv.mkTerm(Kind.STRING_IN_REGEXP, s, r)

# Make a query
slv.assertFormula(slv.mkTerm(Kind.AND, formula1, formula2, formula3, formula4))

# check sat
result = slv.checkSat()
print("cvc5 reports:", result)

# print model if sat
if result.isSat():
    print("x = ", slv.getValue(x))
    print("y = ", slv.getValue(y))
    print("z = ", slv.getValue(z))
