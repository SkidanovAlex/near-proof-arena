import math, ext, sys
from ext import P
L15, L3, L5 = math.log2(15), math.log2(3), math.log2(5)
def base(kind, **kw):
    if kind == 'T':
        pen = dict(target=268, m=8); fin = dict(target=268, m=8)
    else:
        pen = dict(target=236, m=8); fin = dict(target=226, m=8, digest=42)
    pk = {k[4:]: v for k, v in kw.items() if k.startswith('pen_')}
    fk = {k[4:]: v for k, v in kw.items() if k.startswith('fin_')}
    bk = {k: v for k, v in kw.items() if not k.startswith(('pen_', 'fin_'))}
    pen.update(bk); pen.update(pk); fin.update(bk); fin.update(fk)
    return P(**pen), P(**fin)
EXPS = [
 ('baseline', {}),
 ('E1 seq leaf hash (pen)', dict(pen_leaf='seq')),
 ('E2 in-circuit multiproof dedup', dict(pen_dedup='multiproof')),
 ('E1+E2', dict(pen_leaf='seq', pen_dedup='multiproof')),
 ('E3 blowup x3', dict(extra=L3)),
 ('E3 blowup x5', dict(extra=L5)),
 ('E3 blowup x15', dict(extra=L15)),
 ('E5 no domain shrink', dict(shrink=0)),
 ('E5 no shrink, fin only', dict(fin_shrink=0)),
 ('E6 48 B/col', dict(fin_colb=48)),
 ('E7 bit-pack elems', dict(fin_pack=31/32)),
 ('COMBO neutral (E1,E2,E3x15,E6,E7)', dict(pen_leaf='seq', pen_dedup='multiproof', extra=L15, fin_colb=48, fin_pack=31/32)),
 ('COMBO +E5', dict(pen_leaf='seq', pen_dedup='multiproof', extra=L15, fin_colb=48, fin_pack=31/32, shrink=0)),
]
sel = sys.argv[1:] or None
for c_sha in (12000, 24000):
  for kind in ('T', 'L'):
    for name, kw in EXPS:
        pen, fin = base(kind, **kw)
        cells, blocks, shape, f = ext.fixed_point(c_sha, pen, fin)
        print(f"c_sha={c_sha:>5} {kind} {name:38} penSHA={blocks:>6} cells=2^{math.log2(cells):.2f} final={f['bytes']:>8,} "
              f"[auth {f['auth']:,} init {f['initial']:,} cw {f['codeword']:,} fp {f['final_poly']:,} rel {f['relations']:,}] "
              f"b={f['b']} k1={f['k1']} k={f['k']} h={f['log_h']} lf={f['log_final']} W={f['width']} q={f['q']} | pen b={shape['b']} k1={shape['k1']} k={shape['k']} h={shape['log_h']} lf={shape['lf']}", flush=True)
