"""
Decompose magma implication benchmarks via intermediate properties.

For each .p file of the form:
    fof(_, axiom, AXIOM).
    fof(_, conjecture, CONJECTURE).

Generates 3 pairs of files, decomposing the implication through:
  1. Constant function:  ∃C. ∀X,Y. op(X,Y) = C
  2. Left projection:    ∀X,Y. op(X,Y) = X
  3. Right projection:   ∀X,Y. op(X,Y) = Y

Each pair consists of:
  - axiom → intermediate property   (conjecture)
  - intermediate property → original conjecture

Runs Vampire in clausify mode on each generated file to check for parse errors.
"""

import glob
import os
import re
import subprocess
import sys

from tqdm import tqdm

CONSTANT = "? [C] : (! [X, Y] : (op(X, Y) = C))"
PROJ1 = "! [X, Y] : (op(X, Y) = X)"
PROJ2 = "! [X, Y] : (op(X, Y) = Y)"

INTERMEDIATES = [
    ("constant", CONSTANT),
    ("proj1", PROJ1),
    ("proj2", PROJ2),
]


def parse_fof_blocks(text):
    """Extract fof blocks from TPTP text. Returns list of (name, role, formula)."""
    blocks = []
    # Match fof(...). allowing nested parens in the formula
    i = 0
    while i < len(text):
        m = re.search(r'fof\s*\(', text[i:])
        if not m:
            break
        start = i + m.start()
        # Find matching closing paren then ).
        depth = 0
        j = start
        while j < len(text):
            if text[j] == '(':
                depth += 1
            elif text[j] == ')':
                depth -= 1
                if depth == 0:
                    break
            j += 1
        # j is at the closing ) of fof(...)
        inner = text[start + m.end() - m.start() - 1 + 1:j]  # content between outer parens
        # inner is: name, role, formula
        # Split on first two commas (outside parens) to get name, role, formula
        parts = split_top_commas(inner, 2)
        if len(parts) == 3:
            name = parts[0].strip()
            role = parts[1].strip()
            formula = parts[2].strip()
            blocks.append((name, role, formula))
        i = j + 1
    return blocks


def split_top_commas(s, max_splits):
    """Split string on commas at depth 0, up to max_splits times."""
    parts = []
    depth = 0
    current = []
    for ch in s:
        if ch == '(' or ch == '[':
            depth += 1
        elif ch == ')' or ch == ']':
            depth -= 1
        if ch == ',' and depth == 0 and len(parts) < max_splits:
            parts.append(''.join(current))
            current = []
        else:
            current.append(ch)
    parts.append(''.join(current))
    return parts


def make_fof(name, role, formula):
    return f"fof({name}, {role},\n    {formula}\n).\n"


def check_parse(filepath):
    """Run Vampire in clausify mode to check for parse errors. Returns True if OK."""
    result = subprocess.run(
        ["vampire", "--mode", "clausify", filepath],
        capture_output=True, text=True, timeout=10,
    )
    return result.returncode == 0


def main():
    if len(sys.argv) < 3:
        print(f"Usage: {sys.argv[0]} <p_dir> <output_dir>")
        sys.exit(1)

    p_dir = sys.argv[1]
    out_dir = sys.argv[2]

    p_files = sorted(glob.glob(os.path.join(p_dir, "**/*.p"), recursive=True))
    if not p_files:
        print(f"No .p files found in {p_dir}")
        sys.exit(1)

    print(f"Found {len(p_files)} .p files")

    skipped_parse = []
    skipped_shape = 0
    total_generated = 0

    # Phase 1: validate input files
    print("Checking input files...")
    valid_files = []
    for filepath in tqdm(p_files, desc="Validating"):
        if not check_parse(filepath):
            skipped_parse.append(filepath)
            continue

        with open(filepath) as f:
            text = f.read()

        blocks = parse_fof_blocks(text)
        axioms = [(n, r, fm) for n, r, fm in blocks if r == "axiom"]
        conjectures = [(n, r, fm) for n, r, fm in blocks if r == "conjecture"]

        if len(axioms) != 1 or len(conjectures) != 1:
            skipped_shape += 1
            continue

        valid_files.append((filepath, axioms[0][2], conjectures[0][2]))

    print(f"{len(valid_files)} valid, {len(skipped_parse)} parse errors, "
          f"{skipped_shape} wrong shape")

    # Phase 2: generate and check output files
    for filepath, axiom_formula, conjecture_formula in tqdm(valid_files, desc="Generating"):
        rel = os.path.relpath(filepath, p_dir)
        base, _ = os.path.splitext(rel)

        for inter_name, inter_formula in INTERMEDIATES:
            f1_content = make_fof("a1", "axiom", axiom_formula)
            f1_content += "\n"
            f1_content += make_fof("c1", "conjecture", inter_formula)

            f2_content = make_fof("a1", "axiom", inter_formula)
            f2_content += "\n"
            f2_content += make_fof("c1", "conjecture", conjecture_formula)

            f1_path = os.path.join(out_dir, f"{base}_{inter_name}_1.p")
            f2_path = os.path.join(out_dir, f"{base}_{inter_name}_2.p")

            os.makedirs(os.path.dirname(f1_path), exist_ok=True)

            with open(f1_path, 'w') as f:
                f.write(f1_content)
            with open(f2_path, 'w') as f:
                f.write(f2_content)

            total_generated += 2

            # Sanity-check generated files
            assert check_parse(f1_path), f"Parse error in generated file: {f1_path}"
            assert check_parse(f2_path), f"Parse error in generated file: {f2_path}"

    # Report
    print(f"\n{'=' * 60}")
    print(f"REPORT")
    print(f"{'=' * 60}")
    print(f"Input files:            {len(p_files)}")
    print(f"Skipped (parse err):    {len(skipped_parse)}")
    print(f"Skipped (wrong shape):  {skipped_shape}")
    print(f"Valid input:            {len(valid_files)}")
    print(f"Generated files:        {total_generated}")

    if skipped_parse:
        print(f"\nSkipped input files (parse errors):")
        for p in skipped_parse:
            print(f"  {p}")


if __name__ == "__main__":
    main()
