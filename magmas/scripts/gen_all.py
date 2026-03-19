import csv
import os
import re
import subprocess
import sys

from tqdm import tqdm

# --- SyGuS symbol config ---

bv_unary_syms  = ["bvnot", "bvneg"]
bv_binary_syms = ["bvand", "bvor", "bvshl", "bvlshr", "bvxor", "bvadd", "bvmul", "bvsub", "bvudiv", "bvurem"]

bv_sy_template = """
(set-logic BV)
(synth-fun op ((x0 (_ BitVec 4)) (x1 (_ BitVec 4))) (_ BitVec 4)
  ((BV (_ BitVec 4)))
  (
   (BV (_ BitVec 4) (
     x0 x1
     {unaries}
     {binaries}
   ))
  )
)
{declarations}
(constraint {constraint})
(check-synth)
"""

int_sy_template = """
(set-logic NIA)
(synth-fun op ((x0 Int) (x1 Int)) Int
  ((I Int))
  (
   (I Int (
     x0 x1
     0 1
     (- I)
     (+ I I) (- I I) (* I I)
   ))
  )
)
{declarations}
(constraint {constraint})
(check-synth)
"""

real_sy_template = """
(set-logic NRA)
(synth-fun op ((x0 Real) (x1 Real)) Real
  ((R Real))
  (
   (R Real (
     x0 x1
     0.0 1.0
     (- R)
     (+ R R) (- R R) (* R R)
   ))
  )
)
{declarations}
(constraint {constraint})
(check-synth)
"""


# --- Helpers ---

def get_vars(formula):
    return sorted(set(re.findall(r'\bx\d+\b', formula)), key=lambda v: int(v[1:]))


def make_forall(formula, sort="U"):
    vars_ = get_vars(formula)
    bindings = " ".join(f"({v} {sort})" for v in vars_)
    return f"(forall ({bindings}) {formula})"


def make_sy_bv(constraint):
    vars_ = get_vars(constraint)
    declarations = "\n".join(f"(declare-var {v} (_ BitVec 4))" for v in vars_)
    unaries  = " ".join(f"({op} BV)" for op in bv_unary_syms)
    binaries = " ".join(f"({op} BV BV)" for op in bv_binary_syms)
    return bv_sy_template.format(
        unaries=unaries, binaries=binaries,
        declarations=declarations, constraint=constraint)


def make_sy_nia(constraint):
    vars_ = get_vars(constraint)
    declarations = "\n".join(f"(declare-var {v} Int)" for v in vars_)
    return int_sy_template.format(declarations=declarations, constraint=constraint)


def make_sy_nra(constraint):
    vars_ = get_vars(constraint)
    declarations = "\n".join(f"(declare-var {v} Real)" for v in vars_)
    return real_sy_template.format(declarations=declarations, constraint=constraint)


UF_HEADER = """\
(set-logic UF)
(declare-sort U 0)
(declare-fun op (U U) U)
"""

PROJ1_FORMULA = "(forall ((x U) (y U)) (= (op x y) x))"
PROJ2_FORMULA = "(forall ((x U) (y U)) (= (op x y) y))"


def make_imp(pos, neg):
    return UF_HEADER + f"""\
(assert {make_forall(pos)})
(assert (not {make_forall(neg)}))
(check-sat)
"""


def make_eq(pos, neg):
    fp = make_forall(pos)
    fn = make_forall(neg)
    return UF_HEADER + f"""\
(assert (not (= {fp} {fn})))
(check-sat)
"""


def make_proj(formula, proj):
    proj_formula = PROJ1_FORMULA if proj == 1 else PROJ2_FORMULA
    return UF_HEADER + f"""\
(assert {make_forall(formula)})
(assert (not {proj_formula}))
(check-sat)
"""


def make_bvop_check(formula, bw, op_sym):
    bv_sort = f"(_ BitVec {bw})"
    vars_ = get_vars(formula)
    bindings = " ".join(f"({v} {bv_sort})" for v in vars_)
    target = f"(forall ((x {bv_sort}) (y {bv_sort})) (= (op x y) ({op_sym} x y)))"
    return f"""\
(set-logic UFBV)
(declare-fun op ({bv_sort} {bv_sort}) {bv_sort})
(assert (forall ({bindings}) {formula}))
(assert (not {target}))
(check-sat)
"""


def write(path, content):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, 'w') as f:
        f.write(content)
    subprocess.run(["cvc5", "--parse-only", path], check=True)


def write_unique(path, content, seen):
    """Write only if content not seen before. Returns True if written."""
    if content in seen:
        return False
    seen.add(content)
    write(path, content)
    return True


def write_no_dup(path, content, seen):
    """Write and assert content is not a duplicate."""
    assert content not in seen, f"Duplicate content generated for {path}"
    seen.add(content)
    write(path, content)


# --- Main ---

if len(sys.argv) < 2:
    print(f"Usage: {sys.argv[0]} <benchmarks.csv>")
    sys.exit(1)

csv_path = sys.argv[1]

with open(csv_path) as f:
    rows = list(csv.DictReader(f))

seen_sy    = set()
seen_imp   = set()
seen_eq    = set()
seen_proj  = set()
seen_bvxor = set()
seen_bvnor = set()

for row in tqdm(rows):
    name = row['filename']
    pos  = row['positive']
    neg  = row['negative']

    # 1. sy/ — deduplicate
    for i, constraint in enumerate([pos, neg], 1):
        write_unique(f"tmp/sy/{name}_{i}_bv.sy",  make_sy_bv(constraint),  seen_sy)
        write_unique(f"tmp/sy/{name}_{i}_nia.sy", make_sy_nia(constraint), seen_sy)
        write_unique(f"tmp/sy/{name}_{i}_nra.sy", make_sy_nra(constraint), seen_sy)

    # 2. imp/ — assert no duplicates
    write_no_dup(f"tmp/imp/{name}.smt2", make_imp(pos, neg), seen_imp)

    # 3. eq/ — assert no duplicates
    write_no_dup(f"tmp/eq/{name}.smt2", make_eq(pos, neg), seen_eq)

    # 4. proj/ — deduplicate
    for formula, tag in [(pos, "pos"), (neg, "neg")]:
        for proj in [1, 2]:
            write_unique(f"tmp/proj/{name}_{tag}_proj{proj}.smt2", make_proj(formula, proj), seen_proj)

    # 5. bvxor/ and bvnor/ — deduplicate
    for formula, tag in [(pos, "pos"), (neg, "neg")]:
        for bw in range(1, 11):
            write_unique(f"tmp/bvxor/{name}_{tag}_{bw}.smt2", make_bvop_check(formula, bw, "bvxor"), seen_bvxor)
            write_unique(f"tmp/bvnor/{name}_{tag}_{bw}.smt2", make_bvop_check(formula, bw, "bvnor"), seen_bvnor)

print(f"Done. Processed {len(rows)} benchmarks.")
