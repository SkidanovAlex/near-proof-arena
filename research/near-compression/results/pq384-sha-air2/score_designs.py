"""Score SHA-512-compression AIR designs in the corrected final-layer model.

Model: lane/pq-native-hermetic @ b1dba6353, research/near-compression/l4-study/models-C/
ext2.py (gate-5 laws), with the L4-C combo levers (x15 domains, coset leaves, multiproof,
non-halving, packing), Gruen GKR, m = 3.  ext.py and levers_model.py are copied verbatim
into model/.  Differences from ext2.final_bytes, all needed to score an AIR design:
  * GKR and relations use the measured laws of lane/pq-whir-levers @ ab3cfd969
    (native/levers_laws.py): GKR = 48 L^2 + 192 L + 152; relations = 48 (cols + next-row
    cols) + 48 ((d+1)(2^l_skip - 1) + 1) + 48 (d+1) n + 96 airs + 28 (no gruen zerocheck);
  * interactions are counted explicitly: SHA blocks x interactions per compression, plus
    the rest of the circuit at ext2's density (43/460 per cell);
  * next-row openings are counted per column (48 B each), not as a fraction;
  * the final circuit's other columns: OTHER_COLS = 100, all referenced at the next row;
  * constraint degree d enters through the relations law: each unit above 4 costs
    48 (3 + n) B with n = log2(SHA AIR height) - 2 (reported as 'deg').
Settings: 'L' = grinding z=32 + 42-byte digests (236/226 bits), 'T' = today (268, 48 B).

Usage: python3 score_designs.py
"""
import math
import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'model'))
import ext  # noqa: E402
from ext import P  # noqa: E402

L15 = math.log2(15)
COMBO = dict(pen_leaf='seq', pen_dedup='multiproof', extra=L15, fin_pack=31 / 32, shrink=0)
OTHER_COLS, OTHER_NEXT, OTHER_IPC = 100, 100, 43 / 460


def settings(kind, m=3):
    pen = dict(target=268, m=m) if kind == 'T' else dict(target=236, m=m)
    fin = dict(target=268, m=m) if kind == 'T' else dict(target=226, m=m, digest=42)
    for k, v in COMBO.items():
        if k.startswith('pen_'):
            pen[k[4:]] = v
        elif k.startswith('fin_'):
            fin[k[4:]] = v
        else:
            pen[k] = v
            fin[k] = v
    return P(**pen), P(**fin)


def score(rows, cols, tcols, nxt, ipr, d, kind='L', table_cells=64 * 13):
    """rows/cols/nxt/ipr: SHA AIR rows per compression, columns, next-row columns,
    interactions per row; tcols: table columns (all next-row); d: constraint degree."""
    C = rows * cols
    pen, fin = settings(kind)
    cells = 1 << 24
    for _ in range(25):
        blocks, q, shape = ext.cheapest(cells, pen, C)
        blocks += 510  # transcript compressions (gate 5)
        new = int(blocks * C + q * 2000 + (1 << 20) + shape['extra'] + table_cells)
        if abs(new - cells) < cells // 1000:
            cells = new
            break
        cells = new
    inter = blocks * rows * ipr + (cells - blocks * C) * OTHER_IPC
    tc = cols + tcols + OTHER_COLS
    r = ext.best(cells, tc, dict(fin, colb=0))
    whir = r['bytes'] - (3112 + 8456 + 1840 + 861)
    L = math.ceil(math.log2(inter))
    gkr = 48 * L * L + 192 * L + 152          # levers lane law (gruen + derived claims)
    stacking = 1984 + 48 * r['width']
    n = math.ceil(math.log2(blocks * rows)) - 2  # rounds: SHA AIR is the tallest trace
    # levers lane relations law; 10 AIRs assumed for the whole final circuit (constant)
    rel = (48 * (tc + nxt + tcols + OTHER_NEXT) + 48 * ((d + 1) * 3 + 1) + 48 * (d + 1) * n
           + 96 * 10 + 28)
    deg = 48 * (d - 4) * (3 + n)               # part of rel attributable to d > 4 (reported)
    tot = whir + gkr + stacking + rel + 73
    return dict(bytes=round(tot), C=C, whir=round(whir), gkr=gkr, L=L, rel=rel, deg=deg,
                stk=stacking, blocks=blocks, cells=math.log2(cells))


# name, rows/compression, SHA AIR cols, table cols, next-row cols (SHA AIR), interactions/row,
# degree, status
DESIGNS = [
    ('v1 bits, 2 rounds/row (lane/pq-sha384-air)', 44, 442, 18, 442, 43, 4, 'measured'),
    ('v1 + 1 round/row, duplicated history', 84, 350, 15, 332, 15, 5, 'modelled'),
    ('v2 k=1 (bits + v2 overhead cuts)', 44, 384 + 39, 13, 384 + 12, 14, 8, 'built'),
    ('spread/limb lookups, 2 rounds/row (estimate)', 44, 330, 20, 200, 220, 4, 'modelled'),
    ('v2 k=2 (base-4 digits)', 44, 192 + 39, 13, 192 + 12, 14, 9, 'built'),
    ('v2 k=3 (base-8 digits)', 44, 132 + 39, 13, 132 + 12, 14, 21, 'built'),
    ('v2 k=4 (base-16 digits)', 44, 96 + 39, 13, 96 + 12, 14, 45, 'modelled'),
    ('v2 k=3 with 43 rows', 43, 132 + 39, 13, 132 + 12, 14, 21, 'modelled'),
]

if __name__ == '__main__':
    base = {k: score(*DESIGNS[0][1:7], kind=k)['bytes'] for k in 'LT'}
    for name, *a, status in DESIGNS:
        out = []
        for kind in 'LT':
            r = score(*a, kind=kind)
            out.append(f"{kind} {r['bytes']:>8,} ({r['bytes'] - base[kind]:+,})")
        r = score(*a, kind='L')
        print(f"{name:46} [{status:8}] C={r['C']:>6} cols={a[1] + a[2]:>3} nxt={a[3] + a[2]:>3} "
              f"ipr={a[4]:>2} d={a[5]:>2} | {' | '.join(out)} | L: gkr L={r['L']} deg +{r['deg']:,} "
              f"rel {r['rel']:,} pen={r['blocks']} cells=2^{r['cells']:.2f}")
