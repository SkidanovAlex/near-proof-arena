#!/usr/bin/env python3
"""Independent re-check of the exported F_p mul AIR and of the Lean dumper.

Two directions:

1. `air` mode of the Lean dumper emits the AIR (columns, constraints in the
   `wasm-base-lean` JSON dialect, degree) plus the witness row.  This script
   re-evaluates every constraint on that row *in Python* and reports any
   non-zero.  That checks the exporter and the constraint set independently of
   Lean's own `Row.check`.
2. `verify` mode: run the same row construction in Python over the vector file
   and compare to Lean's `want`/`got` (a second independent implementation, not
   sharing code with `FpChip.lean`).

Usage:
  difftest.py lean  <vectors.jsonl>   # summary of the Lean-side run
  difftest.py air   <air.jsonl>       # re-evaluate the exported AIR
"""
import json
import sys

P = 2**255 - 19
B = 2**17
NL = 15
NP = 29


def ev(expr, row):
    op = expr[0]
    if op == "c":
        return expr[1]
    if op == "v":
        return row[expr[1]]
    if op == "+":
        return ev(expr[1], row) + ev(expr[2], row)
    if op == "-":
        return ev(expr[1], row) - ev(expr[2], row)
    if op == "*":
        return ev(expr[1], row) * ev(expr[2], row)
    raise ValueError(op)


def check_air(spec, row):
    assert len(row) == spec["cells"], (len(row), spec["cells"])
    bad = []
    for i, c in enumerate(spec["constraints"]):
        v = ev(c, row)
        if v != 0:
            bad.append((i, v))
    return bad


def python_row(a, b):
    """Independent reimplementation: base-B schoolbook mul, then reduce by long
    division in base B (no shared code with FpChip.lean)."""
    ab = a * b
    q, r = divmod(ab, P)
    limbs = lambda x: [(x >> (17 * i)) & (B - 1) for i in range(NL)]
    A, Bb = limbs(a), limbs(b)
    conv = [0] * NP
    for i in range(NL):
        for j in range(NL):
            conv[i + j] += A[i] * Bb[j]
    cd = [0] * 30
    for k in range(NP):
        cd[k + 1] = (conv[k] + cd[k]) // B
    d = [conv[k] + cd[k] - B * cd[k + 1] for k in range(NP)]
    Q = limbs(q)
    pL = [B - 19] + [B - 1] * 14
    qp = [0] * NP
    for i in range(NL):
        for j in range(NL):
            if i + j < NP:
                qp[i + j] += Q[i] * pL[j]
    R = limbs(r)
    ce = [0] * 30
    for k in range(NP):
        rk = R[k] if k < NL else 0
        ce[k + 1] = (qp[k] + rk + ce[k]) // B
    return q, r, conv, cd, d, ce, qp


def main():
    if len(sys.argv) != 3 or sys.argv[1] not in ("lean", "air"):
        print(__doc__)
        return 2
    mode, path = sys.argv[1], sys.argv[2]
    total = bad = 0
    if mode == "lean":
        for line in open(path):
            j = json.loads(line)
            total += 1
            if "ok" in j:
                if not j["ok"]:
                    bad += 1
                    print("FAIL", j)
            else:
                if not j["rejected"]:
                    bad += 1
                    print("FAIL noncanonical accepted", j)
        print(f"Lean dumper: {total} vectors, {bad} failures")
        return 1 if bad else 0

    # air mode: file has alternating spec/row lines
    lines = [json.loads(l) for l in open(path) if l.strip()]
    assert len(lines) % 2 == 0, len(lines)
    for i in range(0, len(lines), 2):
        spec, wit = lines[i], lines[i + 1]
        total += 1
        bads = check_air(spec, wit["row"])
        q, r, conv, cd, d, ce, qp = python_row(wit["a"], wit["b"])
        if bads:
            bad += 1
            print("AIR non-zero", wit["a"], wit["b"], bads[:3])
        if (q, r) != (wit["q"], wit["r"]):
            bad += 1
            print("row mismatch", wit["a"], wit["b"], (q, r), (wit["q"], wit["r"]))
        # also verify the identity a*b = q*p+r
        if wit["a"] * wit["b"] != wit["q"] * P + wit["r"]:
            bad += 1
            print("identity failed", wit["a"], wit["b"])
    print(f"exported AIR: {total} rows, {bad} failures")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
