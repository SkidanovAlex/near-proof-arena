"""Model for the measured O-2 chain (lane/pq-recursion-sha384 @ 819beab10 model, size_cut3 deltas):
penultimate b7 h20 k1=2 k4 lf6, final b7 h20 k1=1 k4 lf7. Prints the model fixed point and, given the
measured final stacked width W (argv[1], optional), the final's components at that W.
Usage: NV_MCA=O2 python3 model_chain.py [W_final]
"""
import math
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'pq-recursion-nv'))
os.chdir(os.path.join(HERE, '..', 'pq-recursion-nv'))
import extrapolate_nv2 as e  # noqa: E402

# size_cut3.py milestone deltas (program cut milestones 1-2, v4 child DAG)
e.PER_LEVEL = 5; e.QR_BASE -= 26; e.FOLD_ROW = 5; e.FINAL_EQ = 22
e.final_per_q = lambda lf: e.FINAL_EQ + e.FINAL_OTHER + (1 << lf) + 2; e.LEAF_FELTS_PER_ROW = 2
e.Q0_BASE -= 44; e.QR_BASE -= 44; e.P_FIXED -= 6764

c, pb, q = e.fixed_point(236, 236, 42, 7, 18, k1=2, k=4, lf=6)
print(f"MODEL fixed point: prog {c['prog']:,} NvAir {c['nv_rows']:,} (2^{math.log2(c['nv_rows']):.3f}) "
      f"SHA {c['sha_rows']:,} comps {c['comps']:,} cells 2^{math.log2(c['cells']):.3f} inter {c['inter']:,} (2^{math.log2(c['inter']):.3f}) pen q {q}")
print(f"MODEL final: total {pb['total']:,} whir {pb['whir']:,} gkr {pb['gkr']:,} (L={pb['L']}) rel {pb['rel']:,} "
      f"stk {pb['stk']:,} W={pb['W']} shape {pb['shape']} q={pb['q']} certified={pb['certified']} (+73 misc, +{e.o2_reserve(len(pb['q']))} O-2 reserve)")
if len(sys.argv) > 1:
    W = int(sys.argv[1])
    P = e.ext.P(target=236, m=3, extra=e.L15, shrink=0, digest=42)
    r = e.ext.layer(W * 2 ** 20, e.COLS, 7, 1, 4, 20, 7, dict(P, colb=0))
    whir = r['bytes'] - (3112 + 8456 + 1840 + 861)
    small = whir - (r['auth'] + r['initial'] + r['codeword'] + r['final_poly'])
    print(f"MODEL final at measured W={W}: whir {whir:,} = auth {r['auth']:,} + initial {r['initial']:,} + codeword {r['codeword']:,} "
          f"+ final_poly {r['final_poly']:,} + small {small:,}; stacking {e.stacking(18, W):,}; q={r['q']}")
