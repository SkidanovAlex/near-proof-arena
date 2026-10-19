# Backed figures (MODEL): O-2 certificate-gated by shape (CERT_SHAPES) or O-1, v4 SHA AIR,
# 49 NvAir interactions/row, program-cut milestones; penultimate searched over b, n_stack, k, k1, lf.
# Usage: NV_MCA=O2|m64 python3 size_cut3.py
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
                    for lf in range(1, 12):
                        if (ns + 2 - k1 - lf) % k:
                            continue
                        c, pb, q = e.fixed_point(236, 236, 42, b, ns, k1=k1, k=k, lf=lf)
                        if out is None or pb['total'] < out[1]['total']:
                            out = (c, pb, (b, ns, k, k1, lf), q)
    return out
def show(tag):
    c, pb, sh, q = best()
    pen_cert = (sh[0], sh[1] + 2, sh[3], sh[2], sh[4]) in e.CERT_SHAPES
    print(f"{e.MCA:3s} {tag:28s} final {pb['total']:,} B (L={pb['L']}, final certified={pb['certified']}, shape {pb['shape']}) | "
          f"prog {c['prog']:,} NvAir {c['nv_rows']:,} (2^{math.log2(c['nv_rows']):.3f}) | inter 2^{math.log2(c['inter']):.3f} | "
          f"pen (b,ns,k,k1,lf)={sh} certified={pen_cert} q={q}", flush=True)
show('baseline (bfad906ec^)')
e.PER_LEVEL = 5; e.QR_BASE -= 26; e.FOLD_ROW = 5; e.FINAL_EQ = 22
show('milestone 1 (bfad906ec)')
e.final_per_q = lambda lf: e.FINAL_EQ + e.FINAL_OTHER + (1 << lf) + 2; e.LEAF_FELTS_PER_ROW = 2
show('+ Horner chain + Horn2')
e.Q0_BASE -= 44; e.QR_BASE -= 44
show('+ x15 index decomposition')
e.P_FIXED -= 6764
show('+ v4 child DAG (model fix)')
