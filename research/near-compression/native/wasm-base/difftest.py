#!/usr/bin/env python3
"""Differential test Lean AIR model vs Rust verifying key (BF2 (a) evidence).

At N random points per table (independent random field values for every current/next column,
public value and for the three selectors, i.e. far outside the trace domain), compare
  * Lean: `wasmbase-tool eval` evaluates `WasmBase.wasmBaseAir` (the in-memory Lean value);
  * Rust: the SWIRL keygen's symbolic DAG in the verifying key (constraints in order, and every
    interaction's bus, signed count and message).
Usage: difftest.py <nloc> <ncode> <scratch> [n]"""
import json, os, subprocess, sys
HERE = os.path.dirname(os.path.abspath(__file__))
P = 2013265921
nloc, ncode, out = sys.argv[1], sys.argv[2], sys.argv[3]
n = sys.argv[4] if len(sys.argv) > 4 else '16'
tool = os.path.join(HERE, '../../wasm-base-lean/.lake/build/bin/wasmbase-tool')
binp = os.environ.get('WASMBASE_BIN', '/data/illia/nearproof-deps/pq-wasm-base/target/release/nearproof-wasm-base')
os.makedirs(out, exist_ok=True)
airp, pts, rj = (os.path.join(out, f) for f in ('air.json', 'points.txt', 'rust.jsonl'))
open(airp, 'w').write(subprocess.check_output([tool, 'air', nloc, ncode], text=True))
subprocess.check_call([binp, 'difftest', airp, pts, rj, n], stdout=subprocess.DEVNULL)
lean = subprocess.check_output([tool, 'eval', nloc, ncode, pts], text=True).splitlines()
rust = open(rj).read().splitlines()
air = json.load(open(airp))
assert len(lean) == len(rust), (len(lean), len(rust))
nc = ni = 0
for l, r in zip(lean, rust):
    l, r = json.loads(l), json.loads(r)
    t = air['tables'][l['t']]
    assert l['t'] == r['t']
    assert l['constraints'] == r['constraints'], (t['name'], 'constraint mismatch')
    assert len(l['inters']) == len(r['inters']) == len(t['inters']), t['name']
    for li, ri, spec in zip(l['inters'], r['inters'], t['inters']):
        bus, cnt, msg = ri
        assert bus == spec['bus'], t['name']
        assert cnt == (li[0] if spec['send'] else (P - li[0]) % P), (t['name'], 'count')
        assert msg == li[1:], (t['name'], 'message')
    nc += len(l['constraints']); ni += len(l['inters'])
print(f"DIFFTEST OK: {len(lean)} points, {nc} constraint values and {ni} interactions agree "
      f"(Lean wasmBaseAir {nloc} {ncode} = Rust vk DAG)")
