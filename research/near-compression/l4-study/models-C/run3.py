import math, ext
from run import base, L15
NEUT = dict(pen_leaf='seq', pen_dedup='multiproof', extra=L15, fin_colb=48, fin_pack=31/32)
for c_sha in (12000, 24000):
  for name, kind, kw in [
      ('T m=3 baseline', 'T', dict(m=3)), ('T m=3 COMBO neutral', 'T', dict(m=3, **NEUT)),
      ('T beacon fin target 140', 'T', dict(fin_target=140)),
      ('T COMBO + beacon 140', 'T', dict(fin_target=140, **NEUT)),
      ('T COMBO, 300->150 cols', 'T', dict(**NEUT)),
  ]:
      pen, fin = base(kind, **kw)
      cols = 150 if '150' in name else 300
      cells, blocks, shape, f = ext.fixed_point(c_sha, pen, fin, cols=cols)
      print(f"{c_sha} {name:28} penSHA={blocks} cells=2^{math.log2(cells):.2f} final={f['bytes']:,} [auth {f['auth']:,} init {f['initial']:,} cw {f['codeword']:,} fp {f['final_poly']:,} rel {f['relations']:,}] b={f['b']} h={f['log_h']} W={f['width']} q={f['q']}", flush=True)
