"""Model (extrapolate_nv2 laws + ext.layer) for a measured NV FINAL shape, by component.

Usage: NV_MCA=m3|m64 python3 model_vs_measured.py <W> <b> <k1> <k> <log_h> <log_final> [L=25] [n=17]
W = stacked width of the measured final (STREAM_COMMIT width=), cells = W * 2^log_h.
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'pq-recursion-nv'))
import extrapolate_nv2 as e  # noqa: E402

W, b, k1, k, log_h, lf = map(int, sys.argv[1:7])
L = int(sys.argv[7]) if len(sys.argv) > 7 else 25   # ceil(log2(36.2M interactions)) - 1 (measured gkr 34,952)
n = int(sys.argv[8]) if len(sys.argv) > 8 else 17   # log2(tallest trace 2^19) - l_skip
P = e.ext.P(target=236, m=3, extra=e.L15, shrink=0, digest=42)
r = e.ext.layer(W * 2 ** log_h, e.COLS, b, k1, k, log_h, lf, dict(P, colb=0))
whir = r['bytes'] - (3112 + 8456 + 1840 + 861)
gkr = 48 * L * L + 192 * L + 152
rel = e.relations(n)
stk = e.stacking(log_h - 2, W)
small = whir - (r['auth'] + r['initial'] + r['codeword'] + r['final_poly'])
print(f"MODEL[{e.MCA}] W={W} b={b} k1={k1} k={k} log_h={log_h} lf={lf} q={r['q']}")
print(f"  whir {whir:,} = auth {r['auth']:,} + initial {r['initial']:,} + codeword {r['codeword']:,} "
      f"+ final_poly {r['final_poly']:,} + small {small:,}")
print(f"  gkr {gkr:,} (L={L})  relations {rel:,}  stacking {stk:,}")
print(f"  total {whir + gkr + rel + stk:,}")
