#!/usr/bin/env python3
"""Inputs for the D1a oracle's offline measures (`near-arena-oracle-v3-d1a measure-case --dump
FILE`), the D1 analogue of dump_a7_store_v3_d0a.py.

Per case one JSON line: the main pre-state root (the claim's B2 own-slot `prev_state_root`), the
blobs the D1 run wrote (post nodes and values: preimages only — the oracle stores each under its
own SHA-256 and walks from the witness's post-state roots, so they cannot steer its count), and
the Python D1a checker's main-transition keys (read keys plus every transaction's signer
account and access key); the oracle derives its own from nearcore types and reports whether
they are equal. Cases the D1 checker does not accept are skipped (no measure is defined).

usage: dump_a7_store_v3_d1a.py CASE_DIR... > dump.jsonl
"""
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import spec_check_v3_d1a as d1a  # noqa: E402

d0a = d1a.d0a


def main():
    for d in sys.argv[1:]:
        v = d1a.check_case(d)
        tries = list(d0a._TRIES)
        if v[2] is None or not tries:
            continue  # not in RelD1: no measure
        blobs = set()
        for t in tries:
            blobs.update(val for h, val in t.store.items() if h not in t.pre_store)
        print(json.dumps({"case": d, "pre_root": tries[0].pre_root.hex(),
                          "blobs": sorted(b.hex() for b in blobs),
                          "main_keys": sorted(k.hex() for k in tries[0].keys)}))
        sys.stdout.flush()


if __name__ == "__main__":
    main()
