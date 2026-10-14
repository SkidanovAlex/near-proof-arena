#!/usr/bin/env python3
"""Boundary sweep for the bounded D1a amendments (spec/near-chunk-validation-d1a.md): for each
case both checkers accept, and each bounded family with a positive measured value V
(A7 `w.unfolded` / --bound, A9 `e.chacha_words` / --words-bound, A10 `w.path_depth` /
--depth-bound, T1 `w.tx_count` / --tx-bound), the case must be accepted with that bound set to V
and be out of domain for exactly that family with the bound V − 1, in Lean
(`nearspec-v3-check-d1a`) and Python (`spec_check_v3_d1a.py`); the other bounds stay at their
challenge values.

usage: d1a_boundary_v3.py --lean-jsonl F [--lean EXE] [--python FILE] [--jobs J] [--limit K]
                          [--report OUT.json]
       (cases and their measured values from a nearspec-v3-check-d1a JSONL run)
"""
import argparse, collections, json, os, subprocess, sys
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
FAMS = [("unfold", "--bound", "w.unfolded"), ("chacha_words", "--words-bound", "e.chacha_words"),
        ("max_path_depth", "--depth-bound", "w.path_depth"), ("tx_count", "--tx-bound", "w.tx_count")]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--lean-jsonl", required=True)
    ap.add_argument("--lean", default=os.path.join(HERE, "../../zk-formal/.lake/build/bin/nearspec-v3-check-d1a"))
    ap.add_argument("--python", default=os.path.join(HERE, "spec_check_v3_d1a.py"))
    ap.add_argument("--jobs", type=int, default=4)
    ap.add_argument("--limit", type=int, default=0)
    ap.add_argument("--report")
    a = ap.parse_args()
    cases = [x for x in map(json.loads, open(a.lean_jsonl)) if x["verdict"] == "accept"]
    if a.limit:
        cases = cases[:a.limit]
    runs = []
    for c in cases:
        for m, flag, fam in FAMS:
            v = c[m]
            if v <= 0:
                continue
            for b, want in ((v, "accept"), (v - 1, "out_of_domain")):
                for name, cmd in (("lean", [a.lean]), ("python", [sys.executable, a.python])):
                    runs.append((c["case"], fam, b, want, name, cmd + [flag, str(b), c["case"]]))

    def one(r):
        case, fam, b, want, name, cmd = r
        out = json.loads(subprocess.run(cmd, capture_output=True, text=True).stdout.splitlines()[0])
        ok = out["verdict"] == want
        if want == "out_of_domain":
            first = out["reason"].split(",")[0]
            ok = ok and (fam in first)
        return (case, fam, b, want, name, out["verdict"], out["reason"], ok)

    with ThreadPoolExecutor(max_workers=a.jobs) as ex:
        res = list(ex.map(one, runs))
    tally = collections.Counter((r[1], r[3], r[4], r[7]) for r in res)
    bad = [r for r in res if not r[7]]
    rep = {"cases": len(cases), "runs": len(res), "failures": len(bad),
           "tally": {"%s %s %s %s" % k: n for k, n in sorted(tally.items())}, "bad": bad[:30]}
    if a.report:
        open(a.report, "w").write(json.dumps(rep, indent=1) + "\n")
    print(json.dumps({k: rep[k] for k in rep if k != "bad"}, indent=1))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
