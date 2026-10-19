#!/usr/bin/env python3
"""PQ-side cost of nearAirV3D1 at real heights (fixture 00-h10007-s3 of public-d1/d1, heights
from the d1dump run; the six scheduler/receipt tables and mrk are fixed-height in the classical
generators: codec/scandist/proc/mem/cmp/rcpt at 2^22 in every fixture, mrk at 2^19 here).
Work model: tools/perf-design/model.py ML/SWIRL backend as quoted by pq-wasm-base §6:
cell-eq/row = m + f*25.0 + 5.2 at E = 12 (rate 1/2).  Usage: fixture_cost.py envelope-d1.csv"""
import csv, sys, math
LOG = dict(sha_t=13, sha_r=13, node=13, head=7, val=10, walk=10, uniq=10, ups=10, chacha=1, rng=1,
           shuf=1, codec=22, scandist=22, proc=22, mem=22, cmp=22, rcpt=22, acct=7, akey=1, bnd=7,
           srcp=10, size=4, qv=4, mrk=19, sort=7, tx=10, akm=7, kib=10, plf=4, rid=1)
ALIAS = dict(sha0="sha_t", sha1="sha_r", nodeA7="node", valA7="val", upsA7="ups", rcptD1="rcpt",
             srcpDD="srcp", sizeA7="size", mrkD1="mrk")
rows = list(csv.DictReader(open(sys.argv[1])))
tot = dict(cells=0, frac=0, work=0)
fixed = dict(cells=0, frac=0, work=0)
print(f"{'table':9} {'log':>3} {'m':>4} {'f':>3} {'cells':>12} {'fractions':>12} {'cell-eq':>14}")
for r in rows:
    n = ALIAS.get(r["table"], r["table"])
    lg = max(LOG[n], 2)               # NV needs >= 2^l_skip = 4 rows
    h = 2 ** lg
    m, f = int(r["width"]), int(r["interactions"])
    c, fr, w = h * m, h * f, h * (m + 25.0 * f + 5.2)
    for k, v in (("cells", c), ("frac", fr), ("work", w)):
        tot[k] += v
        if lg >= 19:
            fixed[k] += v
    print(f"{n:9} {lg:>3} {m:>4} {f:>3} {c:>12,} {fr:>12,} {w:>14,.0f}")
print(f"TOTAL cells {tot['cells']:,} (2^{math.log2(tot['cells']):.2f}), fractions {tot['frac']:,} (2^{math.log2(tot['frac']):.2f}), "
      f"work {tot['work']:.3e} cell-eq")
print(f"  of which fixed-height tables (log >= 19): {fixed['cells']/tot['cells']:.1%} of cells, {fixed['work']/tot['work']:.1%} of work")
print(f"  stacked width at 2^24: W = {tot['cells']/2**24:.1f} (DESIGN-BASE pin W <= 24)")
print(f"  GPU time at 7.1e9 cell-eq/s/H200 (DESIGN-BASE A): {tot['work']/7.1e9:.2f} s on 1 H200, {tot['work']/7.1e9/32:.3f} s on 32")
