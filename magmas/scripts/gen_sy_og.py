import pprint as pp
import subprocess
import os


def get_template():
    template = """
(set-logic BV)
<SYNTH-FUN>
  ((B Bool) (BV (_ BitVec 4)))
    ((B Bool (
     true
     false
     <BV-LITERALS>
     ))
     (BV (_ BitVec 4)  (
       <BV-VARIABLES> 
       <BV-CONSTANTS>
       <BV-UNARIES>
       <BV-BINARIES>
     ))
    )
)
<DECLARATIONS>
<DEFINE-LIT>
<CONSTRAINT>
(check-synth)

"""
    template = template.replace("<BV-LITERALS>", " ".join(["(" + x +  " BV " + " BV)" for x in binary_pred_syms]))
    template = template.replace("<BV-CONSTANTS>", " ".join([x for x in nullary_fun_syms]))
    template = template.replace("<BV-UNARIES>", " ".join(["(" + x + " BV)" for x in unary_fun_syms]))
    template = template.replace("<BV-BINARIES>", " ".join(["(" + x +  " BV " + " BV)" for x in binary_fun_syms]))
    return template



binary_pred_syms = ["=", "distinct", "bvult", "bvule", "bvugt", "bvuge", "bvslt", "bvsle", "bvsgt", "bvsge"]
nullary_fun_syms = ["(_ bv0 4)", "(_ bv1 4)", "(_ bv8 4)", "(_ bv15 4)"]
unary_fun_syms = ["bvneg", "bvnot"]
binary_fun_syms = ["bvmul", "bvurem", "bvudiv", "bvand", "bvor", "bvshl", "bvlshr", "bvashr"]
lits = {}
for bp in binary_pred_syms:
  for bf in binary_fun_syms:
    lits[(bp, bf)] = {}
    lits[(bp, bf)]["1"] = " ".join(["(", bp, "(", bf, "x", "s", ")", "t", ")"]).replace("( ", "(").replace(" )", ")")
    lits[(bp, bf)]["12"] = " ".join(["(", bp, "(", bf, "x", "x", ")", "t", ")"]).replace("( ", "(").replace(" )", ")")
    lits[(bp, bf)]["13"] = " ".join(["(", bp, "(", bf, "x", "s", ")", "x", ")"]).replace("( ", "(").replace(" )", ")")
    lits[(bp, bf)]["23"] = " ".join(["(", bp, "(", bf, "s", "x", ")", "x", ")"]).replace("( ", "(").replace(" )", ")")
    lits[(bp, bf)]["123"] = " ".join(["(", bp, "(", bf, "x", "x", ")", "x", ")"]).replace("( ", "(").replace(" )", ")")


sygus = {}
suffixes = ["1", "12", "13", "23", "123"]

os.makedirs("tmp", exist_ok=False)

# generate
for bp in binary_pred_syms:
  for bf in binary_fun_syms:
    print("*****")
    print(bp)
    print(bf)
    print(lits[(bp,bf)].keys())
    assert(suffixes == list(lits[(bp, bf)].keys()))
    template = get_template()
    
    # 1
    filename = bp + "_" + bf + "1.sy"
    benchmark = template
    benchmark = benchmark.replace("<SYNTH-FUN>", "(synth-fun ic ((s (_ BitVec 4)) (t (_ BitVec 4))) Bool")
    benchmark = benchmark.replace("<DEFINE-LIT>", "(define-fun ell ((x (_ BitVec 4)) (s (_ BitVec 4)) (t (_ BitVec 4))) Bool " + lits[(bp, bf)]["1"] + ")")
    benchmark = benchmark.replace("<CONSTRAINT>", "(constraint (= (ic s t) (exists ((x (_ BitVec 4))) (ell x s t))))")
    benchmark = benchmark.replace("<BV-VARIABLES>", "s t")
    benchmark = benchmark.replace("<DECLARATIONS>", "\n".join(["(declare-var s (_ BitVec 4))", "(declare-var t (_ BitVec 4))"]))
    filename = filename.replace("=", "eq")
    sygus[filename] = benchmark

    # 12
    filename = bp + "_" + bf + "12.sy"
    benchmark = template
    benchmark = benchmark.replace("<SYNTH-FUN>", "(synth-fun ic ((t (_ BitVec 4))) Bool")
    benchmark = benchmark.replace("<DEFINE-LIT>", "(define-fun ell ((x (_ BitVec 4)) (t (_ BitVec 4))) Bool " + lits[(bp, bf)]["12"] + ")")
    benchmark = benchmark.replace("<CONSTRAINT>", "(constraint (= (ic t) (exists ((x (_ BitVec 4))) (ell x t))))")
    benchmark = benchmark.replace("<BV-VARIABLES>", "t")
    benchmark = benchmark.replace("<DECLARATIONS>", "\n".join(["(declare-var t (_ BitVec 4))"]))
    filename = filename.replace("=", "eq")
    sygus[filename] = benchmark

    # 13
    filename = bp + "_" + bf + "13.sy"
    benchmark = template
    benchmark = benchmark.replace("<SYNTH-FUN>", "(synth-fun ic ((s (_ BitVec 4))) Bool")
    benchmark = benchmark.replace("<DEFINE-LIT>", "(define-fun ell ((x (_ BitVec 4)) (s (_ BitVec 4))) Bool " + lits[(bp, bf)]["13"] + ")")
    benchmark = benchmark.replace("<CONSTRAINT>", "(constraint (= (ic s) (exists ((x (_ BitVec 4))) (ell x s))))")
    benchmark = benchmark.replace("<BV-VARIABLES>", "s")
    benchmark = benchmark.replace("<DECLARATIONS>", "\n".join(["(declare-var s (_ BitVec 4))"]))
    filename = filename.replace("=", "eq")
    sygus[filename] = benchmark

    # 23
    filename = bp + "_" + bf + "23.sy"
    benchmark = template
    benchmark = benchmark.replace("<SYNTH-FUN>", "(synth-fun ic ((s (_ BitVec 4))) Bool")
    benchmark = benchmark.replace("<DEFINE-LIT>", "(define-fun ell ((x (_ BitVec 4)) (s (_ BitVec 4))) Bool " + lits[(bp, bf)]["23"] + ")")
    benchmark = benchmark.replace("<CONSTRAINT>", "(constraint (= (ic s) (exists ((x (_ BitVec 4))) (ell x s))))")
    benchmark = benchmark.replace("<BV-VARIABLES>", "s")
    benchmark = benchmark.replace("<DECLARATIONS>", "\n".join(["(declare-var s (_ BitVec 4))"]))
    filename = filename.replace("=", "eq")
    sygus[filename] = benchmark

    # 123
    filename = bp + "_" + bf + "123.sy"
    benchmark = template
    benchmark = benchmark.replace("<SYNTH-FUN>", "(synth-fun ic () Bool")
    benchmark = benchmark.replace("<DEFINE-LIT>", "(define-fun ell ((x (_ BitVec 4))) Bool " + lits[(bp, bf)]["123"] + ")")
    benchmark = benchmark.replace("<CONSTRAINT>", "(constraint (= ic (exists ((x (_ BitVec 4))) (ell x))))")
    benchmark = benchmark.replace("<BV-VARIABLES>", "")
    benchmark = benchmark.replace("<DECLARATIONS>", "\n".join([""]))
    filename = filename.replace("=", "eq")
    sygus[filename] = benchmark


# save
for filename in sygus:
    path = "tmp/" + filename
    with open(path, 'w') as file:
      file.write(sygus[filename])

# check parsing
for filename in sygus:
    path = "tmp/" + filename
    subprocess.run(["cvc5", "--parse-only", path], check=True)

# check duplicates
for filename1 in sygus:
  for filename2 in sygus:
    if filename1 != filename2:
      assert(sygus[filename1] != sygus[filename2])
