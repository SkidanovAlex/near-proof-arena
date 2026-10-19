# Sensitivity of the extrapolated final layer (extrapolate_nv2.py) to circuit-size levers. MODEL.
# Run from this directory: python3 size_sensitivity.py
import sys, importlib
sys.path.insert(0, '.')
import extrapolate_nv2 as e
def best(name):
    out=None
    for b in (3,4,5,6):
        for ns in (17,18,19):
            c,pb,q=e.fixed_point(236,236,42,b,ns)
            if out is None or pb['total']<out[1]['total']: out=(c,pb,q,b,ns)
    c,pb,q,b,ns=out
    print(f"{name:40s} final {pb['total']:,} whir {pb['whir']:,} gkr {pb['gkr']:,} L={pb['L']} rel {pb['rel']:,} stk {pb['stk']:,} | prog {c['prog']:,} nv {c['nv_rows']:,} sha {c['sha_rows']:,} comps {c['comps']:,} | pen b{b} ns{ns}")
best("baseline")
saved={k:getattr(e,k) for k in ['P_FIXED','APP_ROWS','Q0_COST','QR_COST','FINAL_PER_Q','TRANSCRIPT_BLOCKS','NV_IPR','TR_ROWS']}
def tweak(name, **kw):
    for k,v in kw.items(): setattr(e,k,v)
    best(name)
    for k,v in saved.items(): setattr(e,k,v)
tweak("app table out of program (-11k)", P_FIXED=saved['P_FIXED']-10988, APP_ROWS=0)
tweak("program -28% (all costs)", P_FIXED=int(saved['P_FIXED']*.72), Q0_COST=int(451*.72), QR_COST=int(530*.72), FINAL_PER_Q=int(110*.72))
tweak("NvAir rows 0 (bound: SHA only)", P_FIXED=0, Q0_COST=0, QR_COST=0, FINAL_PER_Q=0, APP_ROWS=0, TR_ROWS=0)
tweak("transcript blocks -50%", TRANSCRIPT_BLOCKS=800)
tweak("NV int/row 55->30", NV_IPR=30)
print("relations law parts at n=17, d=21:", 48*(e.COLS+e.ROT), 48*((e.D+1)*(2**e.L_SKIP-1)+1), 48*((e.D+1)*17-4), 96*e.AIRS+32)
for d in (21, 12, 8):
    e.D=d; best(f"SHA AIR degree {d}")
e.D=21
r0=e.ROT
e.ROT=r0-144+40; best("SHA rot cols 144->40"); e.ROT=r0
e.DEDUP=True; best("in-circuit multiproof dedup"); e.DEDUP=False
