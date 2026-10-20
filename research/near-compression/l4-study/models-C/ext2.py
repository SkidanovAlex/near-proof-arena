"""ext.py corrected with the gate-5 measurements (lane/pq-whir-levers cdccbc7e6).

Measured laws replacing ext.py's child-calibrated constants:
  GKR        72 L^2 + 264 L + 248 B, L = ceil(log2(total interactions))   (exact, L = 13..23)
  stacking   1,984 + 48 W B                                               (exact, W = 4..15)
  relations  2*48*cols + 5,784 + 432*(log2 rows - 12) B                   (measured h = 12..18)
  transcript +510 in-circuit compressions over ext.py's 733 + final-poly term (measured 1,435)
E6 (one opening per column) is unavailable (gate 5), so colb = 96.
Levers added here (model only):
  gruen      GKR round polynomials sent with the eq factor stripped (degree d-1): 72 -> 48 L^2
  nextcols   fraction of columns that need a next-row opening (default 1.0)
"""
import math
import ext

IPC_SHA = 43 / 460          # interactions per committed cell, L3 SHA AIR (43 per 460-col row)


def final_bytes(cells, cols, Pf, ipc=IPC_SHA, gruen=False, nextcols=1.0):
    r = ext.best(cells, cols, dict(Pf, colb=0))       # WHIR part; relations handled below
    whir = r['bytes'] - (3112 + 8456 + 1840 + 861)     # strip ext.py's child constants
    rows = cells / cols
    L = math.ceil(math.log2(cells * ipc))
    gkr = (48 if gruen else 72) * L * L + 264 * L + 248
    stacking = 1984 + 48 * r['width']
    rel = round(48 * cols * (1 + nextcols) + 5784 + 432 * max(0, math.log2(rows) - 12))
    other = 73
    tot = whir + gkr + stacking + rel + other
    return dict(bytes=round(tot), whir=round(whir), auth=r['auth'], initial=r['initial'], codeword=r['codeword'],
                final_poly=r['final_poly'], gkr=gkr, L=L, stacking=stacking, relations=rel, W=r['width'],
                shape=dict(b=r['b'], k1=r['k1'], k=r['k'], h=r['log_h'], lf=r['log_final'], q=r['q']))


def fixed_point(c_sha, Ppen, Pfin, cols=460, c_query=2000, c_fixed=1 << 20, transcript_extra=510, **kw):
    cells = 1 << 24
    for _ in range(25):
        blocks, q, shape = ext.cheapest(cells, Ppen, c_sha)
        blocks += transcript_extra
        new = int(blocks * c_sha + q * c_query + c_fixed + shape['extra'])
        if abs(new - cells) < cells // 1000:
            cells = new
            break
        cells = new
    return cells, blocks, shape, final_bytes(cells, cols, Pfin, **kw)
