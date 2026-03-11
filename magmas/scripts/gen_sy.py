import pprint as pp
import subprocess
import os

binary_pred_syms = ["=", "distinct", "bvult", "bvule", "bvugt", "bvuge", "bvslt", "bvsle", "bvsgt", "bvsge"]
# nullary_fun_syms = ["(_ bv0 4)", "(_ bv1 4)", "(_ bv8 4)", "(_ bv15 4)"]
nullary_fun_syms = []
# unary_fun_syms = ["bvneg", "bvnot"]
unary_fun_syms = ["bvnot"]
# binary_fun_syms = ["bvmul", "bvurem", "bvudiv", "bvand", "bvor", "bvshl", "bvlshr", "bvashr"]
binary_fun_syms = ["bvand", "bvor", "bvshl", "bvlshr", "bvxor"]

template = """
(set-logic BV)
<SYNTH-FUN>
  ((BV (_ BitVec 4)))
    (
     (BV (_ BitVec 4)  (
       <BV-VARIABLES> 
       <BV-CONSTANTS>
       <BV-UNARIES>
       <BV-BINARIES>
     ))
    )
)
<DECLARATIONS>
<CONSTRAINT>
(check-synth)

"""
template = template.replace("<BV-LITERALS>", " ".join(["(" + x +  " BV " + " BV)" for x in binary_pred_syms]))
template = template.replace("<BV-CONSTANTS>", " ".join([x for x in nullary_fun_syms]))
template = template.replace("<BV-UNARIES>", " ".join(["(" + x + " BV)" for x in unary_fun_syms]))
template = template.replace("<BV-BINARIES>", " ".join(["(" + x +  " BV " + " BV)" for x in binary_fun_syms]))

constraint = "(= x (op x (op y (op (op z x) y))))"
# constraint = "(= x (op x (op y (op z (op x z)))))"

constraint = "(and (distinct (op #b0010 #b0011) #b0010)" + constraint + ")"

benchmark = template
benchmark = benchmark.replace("<SYNTH-FUN>", "(synth-fun op ((x (_ BitVec 4)) (y (_ BitVec 4))) (_ BitVec 4)")
benchmark = benchmark.replace("<CONSTRAINT>", "(constraint " + constraint + ")")
benchmark = benchmark.replace("<DECLARATIONS>", "\n".join(["(declare-var x (_ BitVec 4))", "(declare-var y (_ BitVec 4))", "(declare-var z (_ BitVec 4))"]))
benchmark = benchmark.replace("<BV-VARIABLES>", "x y")




filename = "magma1.sy"

# save
os.makedirs("tmp", exist_ok=True)
path = "tmp/" + filename
with open(path, 'w') as file:
  file.write(benchmark)

# check parsing
subprocess.run(["cvc5", "--parse-only", path], check=True)
