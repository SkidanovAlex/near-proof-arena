# Program-cut variants of the extrapolated final layer under the MCA regimes. MODEL.
# Usage: NV_MCA=m3|m64|O2 python3 size_cut_mca.py
import sys; sys.path.insert(0,'.')
import extrapolate_nv2 as e
def best():
    out=None
    for b in (3,4,5,6):
        for ns in (17,18,19):
            c,pb,q=e.fixed_point(236,236,42,b,ns)
            if out is None or pb['total']<out[1]['total']: out=(c,pb)
    return out
c,pb=best(); print(e.MCA,'base',pb['total'],c['prog'])
e.P_FIXED=int(e.P_FIXED*.72); e.Q0_COST=int(451*.72); e.QR_COST=int(530*.72); e.FINAL_PER_Q=int(110*.72)
c,pb=best(); print(e.MCA,'prog-28%',pb['total'],c['prog'])
e.NV_IPR=30
c,pb=best(); print(e.MCA,'prog-28% + 30 int/row',pb['total'],c['prog'])
