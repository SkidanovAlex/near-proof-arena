"""G2 model (lane/pq-recursion-sha384 size_g2.py final state: B1, Merkle 4 rows/level, app role
removed) for the measured chain: penultimate (7, 18, 4, 2, 6), FINAL b7 h20 k1=1 k4 lf7 (one
commitment, O-2). Prints the model fixed point and FINAL, and FINAL at a measured stacked width W
and interaction count if given.  Usage: NV_MCA=O2 python3 model_g2.py [W_meas] [interactions_meas]
"""
import math
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
NV = os.path.join(HERE, '..', 'pq-recursion-nv')
sys.path.insert(0, os.path.join(HERE, '..', 'pq-nv-preprocessed'))
sys.path.insert(0, NV)
os.chdir(NV)
import prep_model as pm  # noqa: E402
e = pm.e
pm.MODE['b1'] = True
e.P_FIXED -= e.APP_ROWS; e.APP_ROWS = 0
e.PER_LEVEL = 4
pm.tree_rows = lambda depth, k1, w: 1 + (1 << k1) * -(-w // 2) + 4 * depth + 2 + 4
e.NV_COLS, e.NV_IPR = 76, 48
e.COLS, e.ROT = e.COLS - 1, e.ROT - 1

c, pb, q = e.fixed_point(236, 236, 42, 7, 18, k1=2, k=4, lf=6)
print(f"MODEL fixed point: prog {c['prog']:,} NvAir {c['nv_rows']:,} (2^{math.log2(c['nv_rows']):.3f}) SHA {c['sha_rows']:,} "
      f"inter {c['inter']:,} (2^{math.log2(c['inter']):.3f}) pen q {q}")
print(f"MODEL FINAL: total {pb['total']:,} whir {pb['whir']:,} gkr {pb['gkr']:,} (L={pb['L']}) rel {pb['rel']:,} stk {pb['stk']:,} "
      f"W={pb['W']} shape {pb['shape']} q={pb['q']} (+73 misc, +{e.o2_reserve(len(pb['q']))} O-2 reserve)")
if len(sys.argv) > 1:
    W = int(sys.argv[1])
    inter = int(sys.argv[2]) if len(sys.argv) > 2 else c['inter']
    P = e.ext.P(target=236, m=3, extra=e.L15, shrink=0, digest=42)
    r = e.ext.layer(W * 2 ** 20, e.COLS, 7, 1, 4, 20, 7, dict(P, colb=0))
    whir = r['bytes'] - (3112 + 8456 + 1840 + 861)
    small = whir - (r['auth'] + r['initial'] + r['codeword'] + r['final_poly'])
    g, L = e.gkr(inter)
    print(f"MODEL FINAL at measured W={W}, interactions {inter:,}: whir {round(whir):,} (auth {r['auth']:,} initial {r['initial']:,} "
          f"codeword {r['codeword']:,} final_poly {r['final_poly']:,} small {round(small):,}) gkr {g:,} (L={L}) rel {pb['rel']:,} "
          f"stk {e.stacking(18, W):,} q={r['q']}")
