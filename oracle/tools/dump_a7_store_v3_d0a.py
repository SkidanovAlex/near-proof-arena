#!/usr/bin/env python3
"""Inputs for the oracle's offline A7 (`near-arena-oracle-v3-d0a unfold-case --dump FILE`) on
constructed D0a cases that nearcore cannot judge (their blocks are in no node's store), e.g.
examples/np-udr-stark-v2/conformance/fixtures-extra.

Per case one JSON line: the main pre-state root the D0 checker starts from (the claim's B2
own-slot `prev_state_root`), the blobs its transitions wrote (post nodes and values: preimages
only — the oracle stores each under its own SHA-256 and walks from the witness's post-state
roots, so these blobs cannot steer its count), and the main transition's read keys (the oracle
derives its own from nearcore types and reports whether they are equal). The counting itself
is the oracle's (src/d0a.rs `unfold_native`, `unfold_pre`, `unfold_diff`).

usage: dump_a7_store_v3_d0a.py CASE_DIR... > dump.jsonl
"""
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import spec_check_v3_d0a as d0a  # noqa: E402


def main():
    for d in sys.argv[1:]:
        d0a.check_case(d)
        tries = list(d0a._TRIES)
        if not tries:
            continue  # the D0 checker never reached the main pre-state
        blobs = set()
        for t in tries:
            blobs.update(v for h, v in t.store.items() if h not in t.pre_store)
        print(json.dumps({"case": d, "pre_root": tries[0].pre_root.hex(),
                          "blobs": sorted(b.hex() for b in blobs),
                          "main_keys": sorted(k.hex() for k in tries[0].keys)}))
        sys.stdout.flush()


if __name__ == "__main__":
    main()
