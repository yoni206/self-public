import pysmt.operators as op
from translators_k import *
from pysmt.shortcuts import Symbol, Or, ForAll, GE, LT, Real, Plus
from pysmt.walkers import IdentityDagWalker

numbers = {}


class CountingWalker(IdentityDagWalker):
    @walkers.handles(set(op.ALL_TYPES) - op.QUANTIFIERS)
    def walk_all(self, formula, args, **kwargs):
        o = formula.get_op()
        if o not in numbers:
          numbers[o] = 1
        else:
          numbers[o] += 1
        return formula

path = sys.args[1]
with open(path, 'r') as f:
  smtlib_string = f.read()

parser = SmtLibParser()
script = parser.get_script(StringIO(smtlib_string))
formula = script.get_last_formula()
walker = CountingWalker()
walker.walk(formula)
print(numbers)
