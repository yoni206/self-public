from io import StringIO
from pysmt.smtlib.parser import SmtLibParser
import pysmt.operators as op
from pysmt.shortcuts import Symbol, Or, ForAll, GE, LT, Real, Plus
from pysmt.walkers import IdentityDagWalker
from pysmt import walkers
import sys
from pysmt import operators

numbers = {}


class CountingWalker(IdentityDagWalker):
    @walkers.handles(set(op.ALL_TYPES) - op.QUANTIFIERS)
    def walk_all(self, formula, args, **kwargs):
        o = operators.op_to_str(formula.node_type())
        if o not in numbers:
          numbers[o] = 1
        else:
          numbers[o] += 1
        return formula

path = sys.argv[1]
with open(path, 'r') as f:
  smtlib_string = f.read()

parser = SmtLibParser()
script = parser.get_script(StringIO(smtlib_string))
formula = script.get_last_formula()
walker = CountingWalker()
walker.walk(formula)
print(numbers)
