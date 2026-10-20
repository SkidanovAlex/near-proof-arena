import math, sys
import ext2
from ext import P
L15 = math.log2(15)
combo = dict(pen_leaf='seq', pen_dedup='multiproof', extra=L15, fin_pack=31/32, shrink=0)
def mk(kind, m, **kw):
    pen = dict(target=268, m=m) if kind == 'T' else dict(target=236, m=m)
    fin = dict(target=268, m=m) if kind == 'T' else dict(target=226, m=m, digest=42)
    for k, v in kw.items():
        if k.startswith('pen_'): pen[k[4:]] = v
        elif k.startswith('fin_'): fin[k[4:]] = v
        else: pen[k] = v; fin[k] = v
    return P(**pen), P(**fin)
print('corrected model (gate-5 laws, no E6); final columns 460 unless noted')
for c_sha in (19448, 28288):
    for kind in ('T', 'L'):
        for m in (3, 8):
            for name, kw in (('combo', {}), ('+gruen', dict(gruen=True)), ('+gruen+next 0.3', dict(gruen=True, nextcols=0.3)),
                             ('+gruen+next0.3, 230 cols', dict(gruen=True, nextcols=0.3, cols=230))):
                cols = kw.pop('cols', 460)
                pen, fin = mk(kind, m, **combo)
                cells, blocks, shape, f = ext2.fixed_point(c_sha, pen, fin, cols=cols, **kw)
                print(f"c_sha={c_sha} {kind} m={m} {name:26} penSHA={blocks:>5} cells=2^{math.log2(cells):.2f} final={f['bytes']:>8,} "
                      f"[whir {f['whir']:,} (auth {f['auth']:,} init {f['initial']:,} cw {f['codeword']:,} fp {f['final_poly']:,}) "
                      f"gkr {f['gkr']:,} L={f['L']} stk {f['stacking']:,} rel {f['relations']:,}] W={f['W']} {f['shape']}", flush=True)
