#!/usr/bin/env python3
"""Measure amendment A12 (`c.layout_wf`) on claim corpora.

A12: the epoch shard layout of the claim has exactly one boundary account fewer than shard ids
(len(boundary_accounts) + 1 == len(shard_ids)), spec/near-chunk-validation-v0a.md §2.9.
Claim-only, so it is measured on every case directory whose claim.bin decodes (a superset of
the accepted cases); cases are classified as honest when meta.json is absent or does not mark
them as a mutant / expected rejection.

usage: a12_measure_v3_d0a.py ROOT...   (walks ROOT for claim.bin; prints one JSON summary)
"""
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import spec_check_v3 as d0  # noqa: E402


def honest(d):
    p = os.path.join(d, "meta.json")
    if not os.path.exists(p):
        return True
    try:
        m = json.load(open(p))
    except Exception:
        return True
    if m.get("kind") == "mutant" or m.get("mutation"):
        return False
    return m.get("expected_verdict", "accept") == "accept"


def main():
    out = {}
    for root in sys.argv[1:]:
        s = dict(cases=0, decoded=0, undecodable=0, honest=0, violations=0, honest_violations=0,
                 layouts={}, violation_cases=[])
        for d, _dirs, files in os.walk(root):
            if "claim.bin" not in files:
                continue
            s["cases"] += 1
            try:
                c = d0.decode_claim(open(os.path.join(d, "claim.bin"), "rb").read())
                L = d0.decode_layout(c['epochs'][0]['layout_raw'])
            except Exception:
                s["undecodable"] += 1
                continue
            s["decoded"] += 1
            h = honest(d)
            s["honest"] += h
            key = "%d/%d" % (len(L.boundary), len(L.shard_ids))
            s["layouts"][key] = s["layouts"].get(key, 0) + 1
            if len(L.boundary) + 1 != len(L.shard_ids):
                s["violations"] += 1
                s["honest_violations"] += h
                if len(s["violation_cases"]) < 20:
                    s["violation_cases"].append(d)
        out[root] = s
    print(json.dumps(out, indent=1, sort_keys=True))


if __name__ == "__main__":
    main()
