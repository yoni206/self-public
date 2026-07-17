#!/usr/bin/env python3
"""Generate SyGuS files, one per binary operation.

The constraints are the "programming by examples" tables from Section 7 of
paper.pdf (Subercaseaux & Przybocki, "A SAT Attack on Tarski's High School
Algebra Problem").  Each table gives, for a 12-element domain 1..12, the
value of one operation on every pair of elements.  Free-parameter cells
(alpha/beta for +, gamma/delta/epsilon for ^) become disjunctions.

Two theories are supported: integers ("int") and bit-vectors ("bv").
Element k of the domain is rendered as the integer k, or as the width-4
bit-vector k.  Edit THEORIES to change the grammar (the syntax the
synthesizer may use) for all generated files of that theory at once.

Usage:
    python3 gen.py --theory int
    python3 gen.py --theory bv
"""

import argparse
import os

# ---------------------------------------------------------------------------
# Theories: the sort, the grammar (syntax) offered to the synthesizer, and how
# a domain element k is written as a term.
# ---------------------------------------------------------------------------
THEORIES = {
    "int": {
        "logic": "ALL",
        "sort": "Int",
        "elem": lambda k: str(k),
        "grammar": [
            "a", "b", "0", "1",
            "(+ Start Start)",
            "(- Start Start)",
            "(div Start Start)",
            "(mod Start Start)",
        ],
    },
    "bv": {
        "logic": "ALL",
        "sort": "(_ BitVec 4)",
        "elem": lambda k: f"(_ bv{k} 4)",
        "grammar": [
            "a", "b", "(_ bv0 4)", "(_ bv1 4)",
            "(bvneg Start)",
            "(bvnot Start)",
            "(bvadd Start Start)",
            "(bvsub Start Start)",
            "(bvmul Start Start)",
            "(bvshl Start Start)",
            "(bvlshr Start Start)",
            "(bvashr Start Start)",
            "(bvand Start Start)",
            "(bvor Start Start)",
            "(bvxor Start Start)",
        ],
    },
}

# ---------------------------------------------------------------------------
# The tables from Section 7.  A grid entry is either an int (a concrete domain
# element) or a string token naming a free parameter.  grid[r-1][c-1] is the
# value of  op(r, c).
# ---------------------------------------------------------------------------

# 7.1 Addition.  alpha cells (a1..a5) have three joint options; beta cells
# (b1..b8) are each independently 8 or 12.
PLUS_GRID = [
    ["a1", "a2", "a3", "b1", "b2", "b3", 12, 12, "a4", "a5",  8, 12],
    ["a2",  11,  11, "b4", "b5", "b6", 12, 12,   8,    8,   12, 12],
    ["a3",  11,  11,   7, "b7", "b8", 12, 12,   8,    8,   12, 12],
    ["b1", "b4",  7,  12,   7,    8,  12, 12,  12,   12,   12, 12],
    ["b2", "b5", "b7", 7,  12,    8,  12, 12,  12,   12,   12, 12],
    ["b3", "b6", "b8", 8,   8,   12,  12, 12,  12,   12,   12, 12],
    [  12,  12,  12,  12,  12,   12,  12, 12,  12,   12,   12, 12],
    [  12,  12,  12,  12,  12,   12,  12, 12,  12,   12,   12, 12],
    ["a4",   8,   8,  12,  12,   12,  12, 12,  12,   12,   12, 12],
    ["a5",   8,   8,  12,  12,   12,  12, 12,  12,   12,   12, 12],
    [   8,  12,  12,  12,  12,   12,  12, 12,  12,   12,   12, 12],
    [  12,  12,  12,  12,  12,   12,  12, 12,  12,   12,   12, 12],
]

# 7.2 Multiplication.  No free parameters.
TIMES_GRID = [
    [ 1,  2,  3,  4,  5,  6,  7,  8,  9, 10, 11, 12],
    [ 2,  2,  2, 12, 12, 12, 12, 12, 11, 11, 11, 12],
    [ 3,  2,  2,  7, 12, 12, 12, 12, 11, 11, 11, 12],
    [ 4, 12,  7, 12,  7, 12, 12, 12, 12, 12, 12, 12],
    [ 5, 12, 12,  7, 12, 12, 12, 12, 12, 12, 12, 12],
    [ 6, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12],
    [ 7, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12],
    [ 8, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12],
    [ 9, 11, 11, 12, 12, 12, 12, 12, 12, 12, 12, 12],
    [10, 11, 11, 12, 12, 12, 12, 12, 12, 12, 12, 12],
    [11, 11, 11, 12, 12, 12, 12, 12, 12, 12, 12, 12],
    [12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12],
]

# 7.3 Exponentiation.  gamma cells (g1..g5) have three joint options; delta
# cells (d1..d5) are each independently 6, 7 or 12; epsilon cells (e1..e4)
# satisfy the relational constraint below.
EXPO_GRID = [
    [ 1,  1,   1,   1,   1,   1,  1,  1,  1,  1,  1,  1],
    [ 2,  2,   2,   2,   2,   2,  2,  2,  2,  2,  2,  2],
    [ 3, "g1","g1",  2,   2,   2,  2,  2,  2,  2,  2,  2],
    [ 4, 12, "g2","g3","g2", 12, 12, 12, 12, 12, 12, 12],
    [ 5, 12, "g3","g2","g3", 12, 12, 12, 12, 12, 12, 12],
    [ 6, 12,  12,  12,  12,  12, 12, 12, 12, 12, 12, 12],
    [ 7, 12,  12,  12,  12,  12, 12, 12, 12, 12, 12, 12],
    [ 8, 12, "g4","g5","g4","d1", 7, 12, 12, 12, 12, 12],
    [ 9, 12, "e1","e2","d2","d3", 12, 12, 12, 12, 12, 12],
    [10, 12, "e3","e4","d4","d5", 12, 12, 12, 12, 12, 12],
    [11, 12,  12,  12,  12,  12, 12, 12, 12, 12, 12, 12],
    [12, 12,  12,  12,  12,  12, 12, 12, 12, 12, 12, 12],
]

# Joint options for the alpha / gamma cells (one option chosen for the table).
PLUS_OPTIONS = [
    {"a1":  9, "a2":  9, "a3": 10, "a4":  8, "a5":  8},
    {"a1": 11, "a2":  9, "a3": 10, "a4": 12, "a5": 12},
    {"a1":  9, "a2": 10, "a3":  9, "a4":  8, "a5":  8},
]
EXPO_OPTIONS = [
    {"g1": 3, "g2":  7, "g3": 12, "g4": 5, "g5": 4},
    {"g1": 2, "g2": 12, "g3":  7, "g4": 4, "g5": 5},
    {"g1": 2, "g2":  7, "g3": 12, "g4": 5, "g5": 4},
]

TABLES = {
    "plus": {
        "grid": PLUS_GRID,
        "options": {"tokens": ["a1", "a2", "a3", "a4", "a5"],
                    "choices": PLUS_OPTIONS},
        "indep": {"tokens": ["b1", "b2", "b3", "b4", "b5", "b6", "b7", "b8"],
                  "domain": [8, 12]},
    },
    "times": {
        "grid": TIMES_GRID,
    },
    "expo": {
        "grid": EXPO_GRID,
        "options": {"tokens": ["g1", "g2", "g3", "g4", "g5"],
                    "choices": EXPO_OPTIONS},
        "indep": {"tokens": ["d1", "d2", "d3", "d4", "d5"],
                  "domain": [6, 7, 12]},
        # epsilon: with A={(6,6)}, B={(6,7),(6,12)}, C={(7,6),(12,7)},
        # enforce ((e1,e3),(e2,e4)) in (A u B u C)^2 \ (A^2 u B^2 u C^2).
        "epsilon": {
            "P": ("e1", "e3"),   # first pair  = (op-value at e1, at e3)
            "Q": ("e2", "e4"),   # second pair = (op-value at e2, at e4)
            "A": [(6, 6)],
            "B": [(6, 7), (6, 12)],
            "C": [(7, 6), (12, 7)],
        },
    },
}

# ---------------------------------------------------------------------------
# SMT-LIB helpers
# ---------------------------------------------------------------------------


def sand(parts):
    parts = list(parts)
    return parts[0] if len(parts) == 1 else "(and " + " ".join(parts) + ")"


def sor(parts):
    parts = list(parts)
    return parts[0] if len(parts) == 1 else "(or " + " ".join(parts) + ")"


def positions(grid):
    """Map each parameter token to the list of (row, col) cells holding it."""
    pos = {}
    for r in range(12):
        for c in range(12):
            v = grid[r][c]
            if isinstance(v, str):
                pos.setdefault(v, []).append((r + 1, c + 1))
    return pos


def build_constraints(theory, name, spec):
    t = THEORIES[theory]
    elem = t["elem"]
    grid = spec["grid"]
    pos = positions(grid)

    def cell(r, c):
        return f"({name} {elem(r)} {elem(c)})"

    def eq(rc, val):
        r, c = rc
        return f"(= {cell(r, c)} {elem(val)})"

    lines = []

    # Concrete cells: one equality each.
    for r in range(1, 13):
        for c in range(1, 13):
            v = grid[r - 1][c - 1]
            if not isinstance(v, str):
                lines.append(f"(constraint {eq((r, c), v)})")

    # Joint-option cells (alpha / gamma): pick one option for all of them.
    if "options" in spec:
        disj = []
        for choice in spec["options"]["choices"]:
            conj = []
            for tok, val in choice.items():
                for rc in pos[tok]:
                    conj.append(eq(rc, val))
            disj.append(sand(conj))
        lines.append(f"(constraint {sor(disj)})")

    # Independent finite-domain cells (beta / delta): shared cells stay equal.
    if "indep" in spec:
        dom = spec["indep"]["domain"]
        for tok in spec["indep"]["tokens"]:
            disj = [sand([eq(rc, v) for rc in pos[tok]]) for v in dom]
            lines.append(f"(constraint {sor(disj)})")

    # Epsilon: the relational constraint over pairs P and Q.
    if "epsilon" in spec:
        e = spec["epsilon"]
        pcx, pcy = pos[e["P"][0]][0], pos[e["P"][1]][0]
        qcx, qcy = pos[e["Q"][0]][0], pos[e["Q"][1]][0]

        def in_block(cx, cy, block):
            return sor([sand([eq(cx, p), eq(cy, q)]) for (p, q) in block])

        pA, pB, pC = (in_block(pcx, pcy, e[k]) for k in ("A", "B", "C"))
        qA, qB, qC = (in_block(qcx, qcy, e[k]) for k in ("A", "B", "C"))
        parts = [
            sor([pA, pB, pC]),
            sor([qA, qB, qC]),
            f"(not (and {pA} {qA}))",
            f"(not (and {pB} {qB}))",
            f"(not (and {pC} {qC}))",
        ]
        lines.append(f"(constraint {sand(parts)})")

    return lines


def render(theory, name):
    t = THEORIES[theory]
    sort = t["sort"]
    prods = "\n".join(" " * 15 + p for p in t["grammar"])
    constraints = "\n".join(build_constraints(theory, name, TABLES[name]))
    return f"""(set-logic {t["logic"]})

(synth-fun {name} ((a {sort}) (b {sort})) {sort}
  ((Start {sort}))
  ((Start {sort} (
{prods}))))

{constraints}

(check-synth)
"""


# The operations to synthesize: (function name, output-file base name).
OPS = [
    ("plus",  "plus"),
    ("times", "times"),
    ("expo",  "expo"),
]


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--theory", choices=sorted(THEORIES), default="int",
                   help="which theory to generate for (default: int)")
    args = p.parse_args()

    outdir = "sy"
    os.makedirs(outdir, exist_ok=True)
    for name, base in OPS:
        filename = os.path.join(outdir, f"{base}_{args.theory}.sy")
        with open(filename, "w") as f:
            f.write(render(args.theory, name))
        print(f"wrote {filename}")


if __name__ == "__main__":
    main()
