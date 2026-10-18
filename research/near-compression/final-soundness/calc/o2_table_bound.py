#!/usr/bin/env python3
"""Full per-layer bound (bound_mca.layer) for the real shapes under the backend's O-2 table,
reading dkt_certs_o2.json only.

Each round's agreement is the AgreementTable::canonical integer (dkt_certs.o2_agree, asserted equal
to bound_mca.agreement('F', ..)). Plans checked:
  O-2      every round first order (what the backend binds today), batching 'first-curve';
  r0=J64   round 0 at the Johnson radius of ListDecoding(64) (O-1), rounds >= 1 first order;
  all J64  O-1 alone, for reference.
A layer passes when every non-query move is <= 2^-270 (bound_mca.BUDGET); query moves sit at
2^-(236+32) by construction.

The non-WHIR parameters (log_int, msg_len, constraints, airs, degree, cols, commits) are bound.py's
for the NV final / inner / base shapes; the b7 h20 final and the b = 2 measured-chain shapes take
the NV ones with their own (log_h, b, k1, k, lf) and W. W of the b = 2 shapes is not pinned here:
141 is used (a degree-(W-1) curve certificate also covers any smaller W, see DKT-VERIFY.md 8.4).

Usage: python3 -I o2_table_bound.py
"""
import math
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import bound_mca as BM  # noqa: E402
import dkt_certs as D  # noqa: E402

BM.CERTS = D.OUT_O2
S = BM.SHAPES
NVF, NVI = S['final (layer d)'], S['inner NV (layers 1..d-1)']
SHAPES = {
    'final (extrapolation optimum) b7 h20 k1=1 k4 lf7': dict(NVF, log_h=20, b=7, k=4, lf=7, W=53),
    'final (bound.py) b8 h19 k1=1 k3 lf9': NVF,
    'inner NV b6 h19 k1=1 k4 lf6': NVI,
    'base app stress b6 h21 k1=1 k4 lf8': S['base app (layer 0, stress)'],
    'measured chain inner b2 h20 k1=1 k4 lf3': dict(NVI, log_h=20, b=2, k=4, lf=3),
    'measured chain final b2 h21 k1=1 k3 lf8': dict(NVF, log_h=21, b=2, k=3, lf=8),
}


def f_ratio(r):
    rho = r['kdim'] / r['n']
    ratio = D.a1(rho) / math.sqrt(rho) + D.O2_MARGIN_MILLI / 1000
    assert BM.agreement('F', r['n'], r['kdim'], ratio=ratio) == D.o2_agree(r['n'], r['kdim'])
    return ('F', ratio)


def main():
    for nm, s in SHAPES.items():
        rs = BM.rounds_of(s)
        plans = {'O-2': [f_ratio(r) for r in rs],
                 'r0=J64': [('J', 64)] + [f_ratio(r) for r in rs[1:]],
                 'all J64': [('J', 64)] * len(rs)}
        print(f'== {nm}  (W = {s["W"]}, commits = {s.get("commits", 1)})')
        for pn, plan in plans.items():
            res = BM.layer(dict(s), plan, 'first-curve')
            e, mv = res['worst_nonquery']
            ok = e <= BM.BUDGET
            print(f'  {pn:8s} q = {res["q"]} (sum {sum(res["q"])})  r0 list 2^{res["rounds"][0]["log_list"]:.2f}  '
                  f'worst non-query 2^{e:.2f} [{mv}]  {"PASS" if ok else "FAIL (> 2^-270)"}')


if __name__ == '__main__':
    main()
