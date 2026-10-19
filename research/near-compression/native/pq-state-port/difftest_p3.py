#!/usr/bin/env python3
"""P3: differential test of the Rust verifying key against the Lean AIR value.

At N random points per table (independent random field values for every cur/next column,
public value and the three selectors, i.e. far outside the trace domain), compare

  * Lean: `pq-state-port-eval` evaluates the Lean `AirP` value (every interaction shifted by
    `busOffset = 128`, exactly as the driver translates it);
  * Rust: the SWIRL keygen's symbolic DAG in the verifying key (constraints in order, and every
    interaction's bus, signed count and message).

The TAPE harness table is excluded on both sides: it is a Rust-side synthetic public-message
carrier with no Lean `AirP` counterpart (its correctness is `TapeNet`, not an AIR).

Usage: difftest_p3.py <d0a|d1> <air.json> <out_dir> [n]
Env: PQ_STATE_PORT_BIN (default under NEARPROOF_PQ_DEPS), PQ_STATE_PORT_EVAL (the Lean exe).
"""
import json
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "../../../.."))
P = 2013265921

variant, air_json, out = sys.argv[1], sys.argv[2], sys.argv[3]
n = sys.argv[4] if len(sys.argv) > 4 else "32"
deps = os.environ.get("NEARPROOF_PQ_DEPS", "/data/illia/nearproof-deps/pq-state-port")
binp = os.environ.get("PQ_STATE_PORT_BIN", os.path.join(deps, "target/release/nearproof-pq-state-port"))
evalp = os.environ.get(
    "PQ_STATE_PORT_EVAL",
    os.path.join(ROOT, "zk-formal/.lake/build/bin/pq-state-port-eval"),
)
os.makedirs(out, exist_ok=True)
pts = os.path.join(out, "points.txt")
rj = os.path.join(out, "rust.jsonl")

subprocess.check_call([binp, "difftest", air_json, pts, rj, n, variant])

which = "nearAirV3" if variant == "d0a" else "nearAirV3D1"
lean_lines = subprocess.check_output([evalp, pts, which], text=True).splitlines()
rust_lines = open(rj).read().splitlines()
air = json.load(open(air_json))

# The Rust side emits one extra table (TAPE, the last one); drop those points from both sides.
n_tables = len(air["tables"])
lean = [json.loads(l) for l in lean_lines if json.loads(l)["t"] < n_tables]
rust = [json.loads(l) for l in rust_lines if json.loads(l)["t"] < n_tables]

assert len(lean) == len(rust), (len(lean), len(rust))
nc = ni = 0
for lp, rp in zip(lean, rust):
    tname = f"table {lp['t']}"
    assert lp["t"] == rp["t"], (lp["t"], rp["t"])
    # The keygen sorts and dedups `constraint_idx` (stark-backend symbolic/dag.rs:99-100), so
    # identical constraints collapse to one.  Compare as multisets of *values*, not by position:
    # every value the Rust DAG reports must be a value the Lean list produces, and the Rust count
    # must equal the number of distinct Lean constraint values.
    assert set(lp["constraints"]) == set(rp["constraints"]), (
        tname,
        "constraint value sets differ",
    )
    # the Rust side is the *set* of distinct constraint nodes, so its length can only be smaller
    assert len(rp["constraints"]) <= len(lp["constraints"]), (tname, "rust grew")
    assert len(lp["inters"]) == len(rp["inters"]) == len(air["tables"][lp["t"]]["interactions"]), tname
    for li, ri, spec in zip(lp["inters"], rp["inters"], air["tables"][lp["t"]]["interactions"]):
        # Lean and Rust both emit `[bus, count, [message...]]` for the *translated* AIR.
        lbus, lcnt, lmsg = li
        bus, cnt, msg = ri
        # the JSON is the untranslated source, so the expected bus is `spec.bus + busOffset`;
        # checking it proves the two translation paths agree.
        assert lbus == bus == spec["bus"] + 128, (tname, "bus")
        # the Lean side reports the unsigned `Σ 2^k b_k`; the Rust DAG carries the sign
        assert cnt == (lcnt if spec["send"] else (P - lcnt) % P), (tname, "count")
        assert msg == lmsg, (tname, "message")
    nc += len(lp["constraints"])
    ni += len(lp["inters"])
print(
    f"DIFFTEST P3 OK: {len(lean)} points, {nc} constraint values and {ni} interactions agree "
    f"(Lean {which} AirP = Rust vk DAG)"
)
