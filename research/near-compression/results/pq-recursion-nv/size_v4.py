# Combined extrapolation: SHA AIR v4 + NvAir 49 interactions/row, regimes O-1 (m = 64, all rounds on
# the certificate fallback = the backed case) and O-2 (all rounds certified), with / without the
# program cut (-28 %).  MODEL.  Usage: NV_SHA=v4|v21 NV_MCA=m64|O2 python3 size_v4.py
import math, sys
sys.path.insert(0, '.')
import extrapolate_nv2 as e
def best():
    out = None
    for b in (3, 4, 5, 6):
        for ns in (17, 18, 19):
            c, pb, q = e.fixed_point(236, 236, 42, b, ns)
            if out is None or pb['total'] < out[1]['total']:
                out = (c, pb, b, ns)
    return out
def show(tag):
    c, pb, b, ns = best()
    print(f"{e.SHA} {e.MCA:3s} {tag:8s} final {pb['total']:,} B (whir {pb['whir']:,} gkr {pb['gkr']:,} L={pb['L']} rel {pb['rel']:,} "
          f"stk {pb['stk']:,}) | prog {c['prog']:,} NvAir {c['nv_rows']:,} (2^{math.ceil(math.log2(c['nv_rows']))}) "
          f"SHA {c['sha_rows']:,} (2^{math.ceil(math.log2(c['sha_rows']))}) | interactions {c['inter']:,} = 2^{math.log2(c['inter']):.3f} | pen b{b} ns{ns}")
show('base')
e.P_FIXED = int(e.P_FIXED * .72); e.Q0_COST = int(451 * .72); e.QR_COST = int(530 * .72); e.FINAL_PER_Q = int(110 * .72)
show('cut-28%')
