#!/usr/bin/env python3
"""Differential test for near/pv86/chunk-validation/v0, domain D1a
(RelD1a = RelD1 ∧ A1 ∧ A2 ∧ Canon0f ∧ A7 ∧ A8 ∧ A9 ∧ A10 ∧ A12 ∧ T1, spec/near-chunk-validation-d1a.md).

Implementations compared on every case directory (claim.bin, witness.bin, optional meta.json):
  (1) Lean    — `nearspec-v3-check-d1a` (compiled `NearSpecV3.checkD1a`);
  (2) Python  — `oracle/tools/spec_check_v3_d1a.py` (D1 checker + independent amendment checks);
  (3) oracle  — optional `--oracle-jsonl F`: `near-arena-oracle-v3-d1a measure-case` output
                (nearcore borsh decoding and nearcore trie nodes: tx_count, A7 unfold on the D1
                run's tries, max path depth, A12), for the cases it measured.

A case agrees iff Lean and Python agree on acceptance, and, when Lean says out_of_domain because
of a D1a amendment, Python says out_of_domain with that family first. A reject-vs-out_of_domain
split on a case neither accepts and where Lean's reason is not a D1a amendment comes from the
unmodified D1 checkers (`checkD1` / spec_check_v3_d1.py, e.g. `c.epoch_start_flip`: Lean
`c.single_epoch`, Python a claim rejection); it is listed as `d1_class_splits`, not as a D1a
disagreement. Expectations from meta.json (all must hold for both checkers):
  * `expected_verdict_d1a` / `expected_reason_d1a` (the D1a mutants, e.g. `w.tx_count_at_bound`
    / `w.tx_count_over`): that verdict, and the reason names that family;
  * `expected_rel_d1 = false` (nearcore / D1 oracle): never accepted (D1a ⊆ D1).
Measures compared exactly (Lean vs Python, where both measured, i.e. RelD1 holds; and vs the
oracle where given): `unfold`, `chacha_words`, `max_path_depth`, `tx_count`.

The report lists, for the accepted cases, the maxima of the measures and the margins to the
bounds (B0 = 2,000,000, W0 = 770,000, Dp0 = 32, NT0 = 4,096), and how many cases nearcore /
the D1 oracle accepts (`expected_rel_d1`) are inside D1a.

usage: difftest_v3_d1a.py (--cases DIR... | --case-list FILE) [--lean EXE] [--python FILE]
         [--jobs J] [--chunk K] [--lean-jsonl F --python-jsonl F] [--oracle-jsonl F...] [--report OUT.json]
         [--label NAME]
"""
import argparse, collections, json, os, subprocess, sys, time
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
AMENDMENTS = ("c.gas_limit", "w.proof_routing", "e.sched_canonical", "w.unfolded", "c.bw_requests",
              "e.chacha_words", "w.path_depth", "c.layout_wf", "w.tx_count")
MEASURES = ("unfold", "chacha_words", "max_path_depth", "tx_count")
BOUNDS = {"unfold": 2_000_000, "chacha_words": 770_000, "max_path_depth": 32, "tx_count": 4096}


def run_checker(cmd, dirs, jobs, chunk=40):
    parts = [dirs[i:i + chunk] for i in range(0, len(dirs), chunk)]

    def one(p):
        r = subprocess.run(cmd + p, capture_output=True, text=True)
        if r.returncode != 0 and not r.stdout:
            raise SystemExit("checker failed: %s\n%s" % (cmd, r.stderr[-2000:]))
        return [json.loads(l) for l in r.stdout.splitlines() if l.strip()]

    out = {}
    with ThreadPoolExecutor(max_workers=jobs) as ex:
        for res in ex.map(one, parts):
            for x in res:
                out[os.path.normpath(x["case"])] = x
    return out


def load_jsonl(f):
    return {os.path.normpath(x["case"]): x for x in map(json.loads, open(f)) if x}


def family(reason):
    """D1a amendment family named by an out-of-domain reason (Lean: the first one), or None."""
    for a in AMENDMENTS:
        if reason.startswith("out of domain (" + a + ")"):
            return a
    return None


def find_cases(roots):
    out = []
    for r in roots:
        for dp, dn, fn in os.walk(r):
            if "claim.bin" in fn and "witness.bin" in fn:
                out.append(os.path.normpath(dp))
                dn[:] = []
    return sorted(out)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cases", nargs="*", default=[])
    ap.add_argument("--case-list")
    ap.add_argument("--lean", default=os.path.join(HERE, "../../zk-formal/.lake/build/bin/nearspec-v3-check-d1a"))
    ap.add_argument("--python", default=os.path.join(HERE, "spec_check_v3_d1a.py"))
    ap.add_argument("--jobs", type=int, default=4)
    ap.add_argument("--chunk", type=int, default=40, help="case dirs per checker process")
    ap.add_argument("--lean-jsonl")
    ap.add_argument("--python-jsonl")
    ap.add_argument("--oracle-jsonl", nargs="*", default=[])
    ap.add_argument("--report")
    ap.add_argument("--label", default="")
    ap.add_argument("--save", help="write the Lean / Python outputs to SAVE.lean.jsonl / SAVE.python.jsonl")
    a = ap.parse_args()
    dirs = find_cases(a.cases)
    if a.case_list:
        dirs += [os.path.normpath(l.strip()) for l in open(a.case_list) if l.strip()]
    t0 = time.time()
    L = load_jsonl(a.lean_jsonl) if a.lean_jsonl else run_checker([a.lean], dirs, a.jobs, a.chunk)
    P = load_jsonl(a.python_jsonl) if a.python_jsonl else run_checker([sys.executable, a.python], dirs, a.jobs, a.chunk)
    if a.save:
        for suf, X in ((".lean.jsonl", L), (".python.jsonl", P)):
            with open(a.save + suf, "w") as f:
                for x in X.values():
                    f.write(json.dumps(x) + "\n")
    O = {}
    for f in a.oracle_jsonl:
        O.update(load_jsonl(f))
    bad = []
    splits = []
    verdicts = collections.Counter()
    fams = collections.Counter()
    in_d1a_of_d1 = [0, 0]
    maxima = {m: (None, None) for m in MEASURES}
    oracle_cmp = collections.Counter()
    exp = collections.Counter()
    for d in dirs:
        l, p = L.get(d), P.get(d)
        if l is None or p is None:
            bad.append({"case": d, "why": "missing output", "lean": l, "python": p})
            continue
        meta = {}
        mp = os.path.join(d, "meta.json")
        if os.path.exists(mp):
            meta = json.load(open(mp))
        why = []
        lf = family(l["reason"]) if l["verdict"] == "out_of_domain" else None
        if l["verdict"] != p["verdict"]:
            pf_d1a = p["verdict"] == "out_of_domain" and p["reason"].split(",")[0] in AMENDMENTS
            if "accept" in (l["verdict"], p["verdict"]) or lf is not None or pf_d1a:
                why.append("verdict")
            else:
                splits.append({"case": d, "lean": l["reason"], "python": p["reason"]})
        if lf is not None:
            pf = p["reason"].split(",")[0] if p["verdict"] == "out_of_domain" else None
            if pf != lf:
                why.append("family %s vs %s" % (lf, pf))
            fams[lf] += 1
        if p["unfold"] is not None:  # Python accepted RelD1: Lean measured too
            for m in MEASURES:
                if l.get(m) != p.get(m):
                    why.append("%s %s vs %s" % (m, l.get(m), p.get(m)))
        elif p.get("tx_count") is not None and l.get("tx_count") != p["tx_count"]:
            why.append("tx_count %s vs %s" % (l.get("tx_count"), p["tx_count"]))
        ev = meta.get("expected_verdict_d1a")
        if ev is not None:
            exp[ev] += 1
            for name, x in (("lean", l), ("python", p)):
                if x["verdict"] != ev:
                    why.append("%s verdict %s, expected %s" % (name, x["verdict"], ev))
            er = meta.get("expected_reason_d1a")
            if er and er not in l["reason"]:
                why.append("lean reason lacks %s" % er)
            if er and er not in p["reason"].split(","):
                why.append("python reason lacks %s" % er)
        if meta.get("expected_rel_d1") is False and "accept" in (l["verdict"], p["verdict"]):
            why.append("accepts a case outside RelD1 (expected_rel_d1 = false)")
        if meta.get("expected_rel_d1") is True and ev is None:
            in_d1a_of_d1[1] += 1
            in_d1a_of_d1[0] += l["verdict"] == "accept"
        o = O.get(d)
        if o is not None and o.get("verdict") == "measured":
            for m in MEASURES:
                if m in o and p.get(m) is not None:
                    ok = o[m] == p[m] and o[m] == l.get(m)
                    oracle_cmp[(m, ok)] += 1
                    if not ok:
                        why.append("oracle %s %s vs lean %s python %s" % (m, o[m], l.get(m), p[m]))
        verdicts[l["verdict"]] += 1
        if l["verdict"] == "accept":
            for m in MEASURES:
                cur = maxima[m]
                if cur[0] is None or l[m] > cur[0]:
                    maxima[m] = (l[m], d)
        if why:
            bad.append({"case": d, "why": why, "lean": l, "python": p})
    margins = {m: {"max": v, "case": c, "bound": BOUNDS[m],
                   "margin": None if v is None else BOUNDS[m] - v} for m, (v, c) in maxima.items()}
    rep = {"label": a.label, "cases": len(dirs), "disagreements": len(bad), "d1_class_splits": len(splits), "verdicts": dict(verdicts),
           "lean_first_family": dict(fams),
           "expected_rel_d1_cases_in_d1a": {"in_d1a": in_d1a_of_d1[0], "expected_rel_d1": in_d1a_of_d1[1]},
           "mutant_expectations": dict(exp),
           "oracle_measures": {"%s %s" % (m, "equal" if ok else "DIFFER"): n for (m, ok), n in oracle_cmp.items()},
           "accepted_maxima": margins, "seconds": round(time.time() - t0, 1), "bad": bad[:50],
           "d1_class_split_cases": splits[:50]}
    s = json.dumps(rep, indent=1)
    if a.report:
        os.makedirs(os.path.dirname(os.path.abspath(a.report)), exist_ok=True)
        open(a.report, "w").write(s + "\n")
    print(json.dumps({k: rep[k] for k in rep if k not in ("bad", "d1_class_split_cases")}, indent=1))
    for b in bad[:10]:
        print("DISAGREE", json.dumps(b)[:600], file=sys.stderr)
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
