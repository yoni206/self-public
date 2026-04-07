# Magmas

Benchmarks and tools for reasoning about magma equations — universal algebraic identities over a binary operation `op`. Each benchmark encodes an implication between two magma equations and asks whether the first equation entails the second.

This is related to the [Equational Theories Project](https://teorth.github.io/equational_theories/).

## Repository Structure

```
magmas/
├── benchmarks/
│   ├── p/          # TPTP format (.p files)
│   │   ├── input1/
│   │   ├── input2/
│   │   └── ...
│   └── smt2/       # SMT-LIB format (.smt2 files)
│       ├── input1/
│       ├── input2/
│       └── ...
└── scripts/
    ├── prep.py        # Parse .smt2 benchmarks into a CSV
    ├── gen_all.py     # Generate various benchmark encodings from CSV
    └── decompose.py   # Decompose implications via intermediate properties
```

## Benchmarks

Each benchmark file represents a conjecture of the form **"Equation A implies Equation B"** for magma equations. For example, `Equation102_implies_Equation1029.p` asks whether any magma satisfying equation 102 must also satisfy equation 1029.

- **TPTP format** (`benchmarks/p/`): First-order logic using `fof` declarations, suitable for ATP systems like Vampire and E.
- **SMT-LIB format** (`benchmarks/smt2/`): Uses an uninterpreted sort and function `op`, suitable for SMT solvers like cvc5 and Z3. A result of `unsat` means the implication holds.

The benchmarks are split across numbered subdirectories (`input1`, `input2`, ...) for batch processing.

## Scripts

### `prep.py` — Extract formulas from SMT-LIB benchmarks

Parses `.smt2` benchmark files and extracts the positive (axiom) and negative (negated conjecture) formulas into a CSV file.

```bash
python scripts/prep.py <input_dir> <output.csv>
```

**Example:**
```bash
python scripts/prep.py benchmarks/smt2/ formulas.csv
```

The output CSV has columns: `filename`, `positive`, `negative`.

### `gen_all.py` — Generate benchmark encodings

Takes the CSV produced by `prep.py` and generates multiple encoding variants in a `tmp/` directory:

```bash
python scripts/gen_all.py <benchmarks.csv>
```

**Generated encodings:**

| Directory | Description |
|---|---|
| `tmp/imp/` | Implication checks (does the positive formula imply the negative?) in UF logic |
| `tmp/eq/` | Equivalence checks between the two formulas |
| `tmp/sy/` | SyGuS synthesis problems — synthesize a concrete operation satisfying each formula (BV, NIA, NRA variants) |
| `tmp/verification/proj/` | Check if a formula forces `op` to be a projection (left or right) |
| `tmp/verification/constant/` | Check if a formula forces `op` to be a constant function |
| `tmp/verification/nia/` | Check if a formula forces `op` to be a specific integer arithmetic expression |
| `tmp/verification/nra/` | Check if a formula forces `op` to be a specific real arithmetic expression |
| `tmp/verification/bvxor/` | Check if a formula forces `op` to be `bvxor` (bit-widths 1–10) |
| `tmp/verification/bvnor/` | Check if a formula forces `op` to be `bvnor` (bit-widths 1–10) |

**Requirements:** `cvc5` must be on your `PATH` (used to validate generated files). Python package `tqdm` is needed for progress display.

### `decompose.py` — Decompose implications via intermediate properties

For each `.p` benchmark claiming "Equation A implies Equation B", generates 3 pairs of files that decompose the implication through an intermediate property:

1. **Constant**: `∃C. ∀X,Y. op(X,Y) = C`
2. **Left projection**: `∀X,Y. op(X,Y) = X`
3. **Right projection**: `∀X,Y. op(X,Y) = Y`

Each pair consists of:
- Axiom → intermediate property
- Intermediate property → original conjecture

If both halves of a pair are provable, the original implication follows by transitivity.

```bash
python scripts/decompose.py <p_dir> <output_dir>
```

**Example:**
```bash
python scripts/decompose.py benchmarks/p tmp
```

For each input file like `Equation102_implies_Equation1029.p`, generates 6 files:
- `Equation102_implies_Equation1029_constant_1.p` / `_constant_2.p`
- `Equation102_implies_Equation1029_proj1_1.p` / `_proj1_2.p`
- `Equation102_implies_Equation1029_proj2_1.p` / `_proj2_2.p`

Input files that fail Vampire's parse check are skipped and listed in the report at the end.

**Requirements:** `vampire` must be on your `PATH` (used to parse-check generated files). Python package `tqdm` is needed for progress display.

## Typical Workflow

```bash
# 1. Extract formulas from the SMT-LIB benchmarks
python scripts/prep.py benchmarks/smt2/ formulas.csv

# 2. Generate all encoding variants
python scripts/gen_all.py formulas.csv

# 3. Run a solver on the generated files
cvc5 tmp/imp/input1/Equation102_implies_Equation1029.smt2
```
