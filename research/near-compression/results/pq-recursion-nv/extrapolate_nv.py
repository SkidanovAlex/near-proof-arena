"""Milestone (d): extrapolate the NV fixed point to the final-layer settings.

MODEL, not a measurement.  Structure and per-unit costs are measured on the NV U2
circuit (lane/pq-recursion-sha384); the WHIR / query / transcript sizes come from the
corrected final-layer model used by the S lane (../pq384-sha-air2/score_designs.py,
which wraps ext.py from lane/pq-native-hermetic l4-study/models-C), with the same
lever combination (x15 domains, coset leaves, multiproof, packing; 'L' = z = 32 grinding
+ 42-byte digests at 236 / 226 bits; 'T' = 268 bits, 48-byte digests).

NV U2 (measured, debug + T = 20 chain):
  * one non-SHA AIR, NvAir: 64 columns, 59 interactions / row, degree 8;
  * byte table 2 columns; air2 SHA AIR (k = 3): 171 columns, 44 rows / compression,
    14 interactions / row, degree 21; table 13 columns;
  * NvAir rows = 2 * program (ALU + BIND) + 8 * job compressions (GLUE) + transcript
    jobs + sample words;
  * program = fixed part + per-query cost (measured NV_QCOST):
      round 0: 875 rows at depth 16, k = 3, child width W ~ 38;
      rounds >= 1: 490 + 19 (depth - 11) rows;
    split as 230 (index bits, fold, misc) + leaves + Merkle, Merkle = 2 * 2^k (digests)
    + 7 (2^k - 1) (coset nodes) + 17 per path level + 4.
The levers are not implemented in-circuit: their in-circuit cost is modelled with the
same per-node / per-row costs (coset leaf = one leaf job of 2^k rows, multiproof = the
expected number of distinct path nodes).

Usage: python3 extrapolate_nv.py
"""
import math
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'pq384-sha-air2', 'model'))
sys.path.insert(0, os.path.join(HERE, '..', 'pq384-sha-air2'))
import ext  # noqa: E402
from score_designs import settings  # noqa: E402

# measured structure (NV U2)
SHA_ROWS, SHA_COLS, SHA_NEXT, SHA_IPR, SHA_DEG = 44, 171, 144, 14, 21
TABLE_COLS, TABLE_CELLS = 13, 64 * 13
NV_COLS, NV_IPR, NV_DEG = 64, 59, 8
BYTE_COLS = 2
PROG_FIXED = 40_000      # preamble, GKR, batch-constraint DAG, stacking (measured ~40k)
Q_MISC = 230             # per query: 31 index bits + recomposition, fold, misc
TRANSCRIPT_ROWS = 1_100  # hash-chain + sample rows (measured ~1k + ~4k at T = 20; scaled below)


def merkle_rows(kk, depth, multiproof_nodes=None):
    leaves = 2 * (1 << kk) + 7 * ((1 << kk) - 1)
    path = 17 * depth if multiproof_nodes is None else 17 * multiproof_nodes
    return leaves + path + 4


def program_rows(shape, cells, P, coset_leaf):
    r = ext.layer(cells, 300, shape['b'], shape['k1'], shape['k'], shape['log_h'], shape['lf'], P)
    rows = PROG_FIXED
    for i, rd in enumerate(r['rounds']):
        kk, q = rd['kk'], rd['q']
        depth = math.ceil(math.log2(rd['leaves']) - 1e-9)
        width = r['width'] if i == 0 else 12
        leaf_vals = (1 << kk) * width if i == 0 else 2 * (1 << kk)
        if P.get('dedup') == 'multiproof':
            nodes = ext.mp_internal(q, rd['leaves']) / q
            m = merkle_rows(kk, depth, nodes)
        else:
            m = merkle_rows(kk, depth)
        if coset_leaf:
            m -= 7 * ((1 << kk) - 1) + 2 * ((1 << kk) - 1)  # one leaf job, no coset tree
        rows += q * (Q_MISC + leaf_vals + m)
    return int(rows), sum(rd['q'] for rd in r['rounds'])


def nv_fixed_point(kind, pad=True, per_column_next=False, coset_leaf=True, bind_per_row=1, nv_ipr=NV_IPR):
    pen, fin = settings(kind)
    C = SHA_ROWS * SHA_COLS
    cells = 1 << 26
    for _ in range(40):
        blocks, q, shape = ext.cheapest(cells, pen, C)
        blocks += 510  # transcript compressions (gate 5)
        prog, qt = program_rows(shape, cells, pen, coset_leaf)
        prog_len = 1 << math.ceil(math.log2(prog)) if pad else -(-prog // 512) * 512
        nv_rows = prog_len + prog_len // bind_per_row + 8 * blocks + TRANSCRIPT_ROWS + qt
        sha_rows = blocks * SHA_ROWS
        if pad:
            nv_h, sha_h = 1 << math.ceil(math.log2(nv_rows)), 1 << math.ceil(math.log2(sha_rows))
        else:
            nv_h, sha_h = nv_rows, sha_rows
        new = nv_h * NV_COLS + sha_h * SHA_COLS + TABLE_CELLS + 256 * BYTE_COLS
        if abs(new - cells) < cells // 1000:
            cells = new
            break
        cells = new
    inter = nv_h * nv_ipr + sha_h * SHA_IPR + 64 * 2 + 256
    cols = NV_COLS + SHA_COLS + TABLE_COLS + BYTE_COLS
    nxt = (NV_COLS + SHA_NEXT + TABLE_COLS + BYTE_COLS) if per_column_next else cols
    r = ext.best(cells, cols, dict(fin, colb=0))
    whir = r['bytes'] - (3112 + 8456 + 1840 + 861)
    L = math.ceil(math.log2(inter))
    gkr = 48 * L * L + 192 * L + 152
    stacking = 1984 + 48 * r['width']
    d = max(SHA_DEG, NV_DEG)
    n = math.ceil(math.log2(max(nv_h, sha_h))) - 2
    rel = 48 * (cols + nxt) + 48 * ((d + 1) * 3 + 1) + 48 * (d + 1) * n + 96 * 4 + 28
    tot = whir + gkr + stacking + rel + 73
    return dict(bytes=round(tot), whir=round(whir), gkr=gkr, L=L, rel=rel, stk=stacking,
                blocks=blocks, prog=prog, prog_len=prog_len, nv_rows=nv_h, sha_rows=sha_h,
                cells=math.log2(cells), inter=math.log2(inter), q=qt, shape=shape)


VARIANTS = [
    ('as built (U2)', dict()),
    ('+ BIND rows cover 2 ALU rows', dict(bind_per_row=2)),
    ('+ 16-bit byte-pair lookups (47 int/row)', dict(bind_per_row=2, nv_ipr=47)),
]

if __name__ == '__main__':
    print("NV U2 fixed point at the final-layer settings [MODEL; structure measured]")
    for vname, kw in VARIANTS:
      print(f"== {vname}")
      for kind in 'LT':
        for pad in (True, False):
            for pcn in (False,):
                r = nv_fixed_point(kind, pad=pad, per_column_next=pcn, **kw)
                s = r['shape']
                print(f"{kind} pad={'pow2' if pad else 'none':4} next={'per-col' if pcn else 'per-AIR':7} | "
                      f"final {r['bytes']:>8,} B (whir {r['whir']:,} gkr {r['gkr']:,} L={r['L']} rel {r['rel']:,} "
                      f"stk {r['stk']:,}) | pen compressions {r['blocks']:,}, queries {r['q']}, "
                      f"program {r['prog']:,} -> {r['prog_len']:,}, NvAir 2^{math.log2(r['nv_rows']):.2f} rows, "
                      f"SHA 2^{math.log2(r['sha_rows']):.2f} rows, cells 2^{r['cells']:.2f}, "
                      f"interactions 2^{r['inter']:.2f} | pen shape b={s['b']} k1={s['k1']} k={s['k']} "
                      f"log_h={s['log_h']} lf={s['lf']}")
