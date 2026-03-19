import csv
import glob
import os
import re
import sys


def find_matching_paren(s, start):
    depth = 0
    for i in range(start, len(s)):
        if s[i] == '(':
            depth += 1
        elif s[i] == ')':
            depth -= 1
            if depth == 0:
                return i
    raise ValueError("No matching paren")


def extract_forall_body(s):
    s = s.strip()
    assert s.startswith('(forall'), f"Expected forall, got: {s[:30]}"
    bindings_start = s.index('(', 1)
    bindings_end = find_matching_paren(s, bindings_start)
    body = s[bindings_end+1:].strip()
    assert body.endswith(')')
    body = body[:-1].strip()
    return body


def extract_formula(assert_line, strip_not=False):
    s = assert_line.strip()
    inner_start = s.index('(', 1)
    inner_end = find_matching_paren(s, inner_start)
    inner = s[inner_start:inner_end+1]

    if strip_not:
        forall_start = inner.index('(', 1)
        forall_end = find_matching_paren(inner, forall_start)
        inner = inner[forall_start:forall_end+1]

    body = extract_forall_body(inner)
    body = body.replace('tptp.op', 'op')
    body = re.sub(r'\bX(\d+)\b', lambda m: 'x' + m.group(1), body)
    return body


rows = []

for filepath in sorted(glob.glob("benchmarks/**/*.smt2", recursive=True)):
    with open(filepath) as f:
        assert_lines = [l.strip() for l in f if l.strip().startswith('(assert')]

    if len(assert_lines) < 2:
        continue

    parts = filepath.replace('.p.smt2', '').replace('.smt2', '').split(os.sep)
    basename = os.path.join(parts[-2], parts[-1])
    positive = extract_formula(assert_lines[0], strip_not=False)
    negative = extract_formula(assert_lines[1], strip_not=True)
    rows.append((basename, positive, negative))

if len(sys.argv) < 2:
    print(f"Usage: {sys.argv[0]} <output.csv>")
    sys.exit(1)

out = sys.argv[1]
os.makedirs(os.path.dirname(out) or ".", exist_ok=True)
with open(out, 'w', newline='') as f:
    writer = csv.writer(f)
    writer.writerow(["filename", "positive", "negative"])
    writer.writerows(rows)

print(f"Wrote {len(rows)} rows to {out}")
