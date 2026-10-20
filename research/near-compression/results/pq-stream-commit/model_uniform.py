"""Model for the bound chain with FINAL at the fixed point (lane/pq-recursion-sha384 @ 717eb518e
model: G1 fix, binding at every level, size_cut3 deltas). The final shares the penultimate's shape
(b7, log_h 20, k 4, k1, lf). Prints the fixed-point circuit and the final's components, also at a
measured stacked width W and measured interactions if given.
Usage: NV_MCA=O2 python3 model_uniform.py <k1> <lf> [W_meas] [interactions_meas]
"""
import math
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'pq-recursion-nv'))
os.chdir(os.path.join(HERE, '..', 'pq-recursion-nv'))
import extrapolate_nv2 as e  # noqa: E402

e.PER_LEVEL = 5; e.QR_BASE -= 26; e.FOLD_ROW = 5; e.FINAL_EQ = 22
e.final_per_q = lambda lf: e.FINAL_EQ + e.FINAL_OTHER + (1 << lf) + 2; e.LEAF_FELTS_PER_ROW = 2
e.Q0_BASE -= 44; e.QR_BASE -= 44; e.P_FIXED -= 6764

k1, lf = int(sys.argv[1]), int(sys.argv[2])
c, _, q = e.fixed_point(236, 236, 42, 7, 18, k1=k1, k=4, lf=lf)
P = e.ext.P(target=236, m=3, extra=e.L15, shrink=0, digest=42)


def final(cells, inter):
    r = e.ext.layer(cells, e.COLS, 7, k1, 4, 20, lf, dict(P, colb=0))
    whir = r['bytes'] - (3112 + 8456 + 1840 + 861)
    g, L = e.gkr(inter)
    n = math.ceil(math.log2(max(c['nv_rows'], c['sha_rows']))) - e.L_SKIP
    rel, stk = e.relations(n), e.stacking(18, r['width'])
    small = whir - (r['auth'] + r['initial'] + r['codeword'] + r['final_poly'])
    tot = whir + g + rel + stk + 73 + e.o2_reserve(len(r['q']))
    return (f"total {round(tot):,} | whir {round(whir):,} (auth {r['auth']:,} initial {r['initial']:,} codeword {r['codeword']:,} "
            f"final_poly {r['final_poly']:,} small {round(small):,}) gkr {g:,} (L={L}) rel {rel:,} stk {stk:,} W={r['width']} q={r['q']}")


print(f"MODEL fixed point (k1={k1}, lf={lf}): prog {c['prog']:,} NvAir {c['nv_rows']:,} (2^{math.log2(c['nv_rows']):.3f}) "
      f"SHA {c['sha_rows']:,} inter {c['inter']:,} (2^{math.log2(c['inter']):.3f}) q {q}")
print("MODEL final:", final(c['cells'], c['inter']))
if len(sys.argv) > 3:
    W = int(sys.argv[3])
    inter = int(sys.argv[4]) if len(sys.argv) > 4 else c['inter']
    print(f"MODEL final at measured W={W}, interactions={inter:,}:", final(W * 2 ** 20, inter))
