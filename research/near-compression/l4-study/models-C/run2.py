import math, ext
from ext import P
from run import base, L15, L3
# (a) E3 split: x15 only in final vs only in penultimate
for c_sha in (12000,):
  for kind in ('T','L'):
    for name, kw in [('x15 final only', dict(fin_extra=L15)), ('x15 pen only', dict(pen_extra=L15)),
                     ('x15 + seq leaf', dict(extra=L15, pen_leaf='seq')),
                     ('hypothetical maxdom 28', dict(maxdom=28)), ('hypothetical maxdom 30', dict(maxdom=30)), ('hypothetical maxdom 32', dict(maxdom=32))]:
        pen, fin = base(kind, **kw)
        cells, blocks, shape, f = ext.fixed_point(c_sha, pen, fin)
        print(f"{c_sha} {kind} {name:26} penSHA={blocks} cells=2^{math.log2(cells):.2f} final={f['bytes']:,} b={f['b']} h={f['log_h']} W={f['width']} q={f['q']}", flush=True)
# (b) Goldilocks final layer over BabyBear penultimate
for c_sha in (12000, 24000):
  for kind in ('T','L'):
    for leafmode in ('tree','seq'):
      pen, fin = base(kind, pen_leaf=leafmode)
      cells, blocks, shape, f0 = ext.fixed_point(c_sha, pen, fin)
      r = ext.layer(cells, 300, shape['b'], shape['k1'], shape['k'], shape['log_h'], shape['lf'], pen)
      q = sum(r['q'])
      for g in (0.7, 1.0):
        fcells = int(blocks*c_sha*g + q*2000*3 + 4*((1<<20) + shape['extra']))
        finG = dict(fin); finG.update(cell=8, maxdom=32)
        f = ext.best(fcells, 300, finG)
        print(f"GOLD {c_sha} {kind} leaf={leafmode} g={g} BBfinal={f0['bytes']:,} Gcells=2^{math.log2(fcells):.2f} Gfinal={f['bytes']:,} b={f['b']} h={f['log_h']} W={f['width']} q={f['q']} init={f['initial']:,} auth={f['auth']:,}", flush=True)
