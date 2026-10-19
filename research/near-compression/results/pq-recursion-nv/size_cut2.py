# Program-cut milestones toward NvAir < 2^18 (MODEL), backed O-1 by default.
#   sibling op: Merkle level 10 -> 7 rows; fold butterfly 7 -> 5 rows; eq_mle 6 -> 2 rows/var
#   (shared per-alpha factors); Horner 2 -> 1 row/coefficient; v4 child DAG (5,848 SHA nodes
#   instead of 12,718); penultimate shape searched over b, n_stack, k, k1, log_final.
# Usage: NV_MCA=m64|O2 python3 size_cut2.py
import math, sys
sys.path.insert(0, '.')
import extrapolate_nv2 as e
def best():
    out = None
    for b in (6, 7, 8):
        for ns in (15, 16, 17, 18):
            for k in (3, 4):
                for k1 in (1, 2):
                    if ns + 2 + b > e.MAX_DOM:
                        continue
                    c, pb, q = e.fixed_point(236, 236, 42, b, ns, k1=k1, k=k)
                    if out is None or pb['total'] < out[1]['total']:
                        out = (c, pb, (b, ns, k, k1, c['pen_lf']), q)
    return out
def show(tag):
    c, pb, sh, q = best()
    print(f"{e.SHA} {e.MCA:3s} {tag:22s} final {pb['total']:,} B (L={pb['L']}) | prog {c['prog']:,} NvAir {c['nv_rows']:,} "
          f"(2^{math.log2(c['nv_rows']):.3f}) | inter 2^{math.log2(c['inter']):.3f} | pen (b,ns,k,k1,lf)={sh} q={q}", flush=True)
show('baseline')
e.PER_LEVEL = 7; show('+ sibling op')
e.QR_BASE -= 26; e.FOLD_ROW = 5; show('+ fold butterfly')
e.FINAL_EQ = 22; show('+ eq 2 rows/var')
e.P_FIXED -= 6764; show('+ v4 child DAG')
e.final_per_q = lambda lf: e.FINAL_EQ + e.FINAL_OTHER + (1 << lf); show('+ Horner 1 row/coef')
