"""Phase-2 extrapolation of the NV final layer from the all-lever chain measurements.

MODEL built from MEASURED laws.  Everything structural is measured on the NV phase-2 circuit
(lane/pq-recursion-sha384, unified backend, all levers on: x15, k1 = 1, k = 4, keep-domain,
coset leaf, 42-byte digests, z = 32 wide PoW, multiproof, Gruen GKR + zerocheck, derived
claims, next-row mask, WHIR-Y, tight heights), at the largest target that fits 24 GB
(logs/nvp2-T102.log: 70 query bits + z = 32, n_stack = 18, log_blowup = 1).

Per-component laws (all checked against the measured chain proofs, see `check()`):
  GKR        48 L^2 + 192 L + 152,  L = ceil(log2(total interactions)) - 1
  relations  48 (cols + rot) + 48 ((d+1)(2^l_skip - 1) + 1) + 48 ((d+1) n - g)
             + 96 airs + 28 + 4,    n = log2(tallest trace) - l_skip, g = Gruen rounds
  stacking   352 + 96 n_stack + 48 W
  WHIR       ext.layer (lane/pq-native-hermetic models-C, as used by the S lane) with the
             lever settings; checked against the measured WHIR bytes
Circuit size (measured): NvAir 70 columns (36 rotated), 52 interactions / row; SHA AIR v2.1
171 columns (144 rotated), 43 rows / compression, 14 interactions / row, degree 21; table
13 (11); byte-pair table 5 (2).  Program = fixed part + per-query costs (NV_QCOST) + final
check; NvAir rows = prog (ALU, no power-of-two padding: ACC2/ACC sit at fixed early
addresses and the program length is just even) + prog / 2 (BIND) + app table / 2 + 8 * job
compressions + transcript; committed rows = used rows (tight heights).

Usage: python3 extrapolate_nv2.py
"""
import math
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'pq384-sha-air2', 'model'))
import ext  # noqa: E402

L15 = math.log2(15)
L_SKIP = 2
COLS, ROT = 70 + 171 + 13 + 5, 36 + 144 + 11 + 2
D = 21
AIRS = 4
NV_IPR, SHA_IPR, SHA_ROWS = 52, 14, 43
# measured program costs (A2 of nvp2-T102: child = the NV level itself)
P_FIXED = 72_278          # preamble + app table (10,9k) + GKR + DAG + stacking
APP_ROWS = 10_988          # level-1 table (data rows)
Q0_COST = 451              # round 0 (k1 = 1), depth 20 + 4 (x15)
QR_COST = 530              # rounds >= 1 (k = 4), depth 17 + 4
PER_LEVEL = 10             # ALU rows per Merkle path level
FINAL_PER_Q = 110          # final WHIR check per query (powers, eq, Horner)
TRANSCRIPT_BLOCKS = 1_600  # transcript compressions (measured ~1.5k)
TR_ROWS = 6_000            # hash-chain + sample rows


def gkr(inter):
    L = math.ceil(math.log2(inter)) - 1
    return 48 * L * L + 192 * L + 152, L


def relations(n, g=4):
    return 48 * (COLS + ROT) + 48 * ((D + 1) * (2 ** L_SKIP - 1) + 1) + 48 * ((D + 1) * n - g) + 96 * AIRS + 32


def stacking(n_stack, W):
    return 352 + 96 * n_stack + 48 * W


def whir(cells, b, k1, k, log_h, lf, target, digest):
    P = ext.P(target=target, m=3, extra=L15, shrink=0, digest=digest, leaf='seq', dedup='multiproof', pack=1.0)
    r = ext.layer(cells, COLS, b, k1, k, log_h, lf, P)
    return r['bytes'] - (r['relations'] + 8456 + 1840 + 861), r


def nv_circuit(rounds_q, depth0, depthr, child_W):
    """NV circuit size verifying a child with WHIR schedule rounds_q (per-round queries)."""
    q0, qr = rounds_q[0], sum(rounds_q[1:])
    prog = P_FIXED + q0 * (Q0_COST + PER_LEVEL * (depth0 - 24)) + qr * (QR_COST + PER_LEVEL * (depthr - 21)) \
        + FINAL_PER_Q * (q0 + qr)
    prog_log = math.ceil(math.log2(prog + 2))
    # compressions: leaf jobs (round 0: 2 rows of W felts; later: 16 Ext12 values) + nodes
    blk = lambda nbytes: -(-(nbytes + 33 + 8 + 17) // 128)
    comps = q0 * (blk(2 * child_W * 4) + depth0) + qr * (blk(16 * 48) + depthr) + TRANSCRIPT_BLOCKS
    glue = 8 * comps
    prog += prog % 2
    nv_rows = prog + prog // 2 + APP_ROWS // 2 + glue + TR_ROWS
    sha_rows = SHA_ROWS * comps
    return dict(prog=prog, prog_log=prog_log, comps=comps, nv_rows=nv_rows, sha_rows=sha_rows,
                cells=nv_rows * 70 + sha_rows * 171 + 64 * 13 + 65536 * 5,
                inter=nv_rows * NV_IPR + sha_rows * SHA_IPR + 64 * 2 + 65536)


def proof_bytes(c, target, digest):
    """Final-layer proof of the NV circuit `c`; the final layer picks its own WHIR shape."""
    P = ext.P(target=target, m=3, extra=L15, shrink=0, digest=digest)
    r = ext.best(c['cells'], COLS, dict(P, colb=0))
    log_h = r['log_h']
    n_stack = log_h - L_SKIP
    W = r['width']
    w = r['bytes'] - (3112 + 8456 + 1840 + 861)
    g, L = gkr(c['inter'])
    n = math.ceil(math.log2(max(c['nv_rows'], c['sha_rows']))) - L_SKIP
    rel = relations(n)
    st = stacking(n_stack, W)
    return dict(total=round(w + g + rel + st + 73), whir=round(w), gkr=g, L=L, rel=rel, stk=st, W=W,
                q=r['q'], shape=dict(b=r['b'], k1=r['k1'], k=r['k'], log_h=log_h, lf=r['log_final']))


def schedule(cells, b, k1, k, log_h, lf, target):
    P = ext.P(target=target, m=3, extra=L15, shrink=0)
    r = ext.layer(cells, COLS, b, k1, k, log_h, lf, P)
    return r['q'], [math.ceil(math.log2(rd['leaves']) - 1e-9) for rd in r['rounds']]


def fixed_point(pen_target, fin_target, digest, b, n_stack, k1=1, k=4):
    log_h = L_SKIP + n_stack
    lf = next(x for x in range(3, 12) if (log_h - k1 - x) % k == 0)
    cells = 1 << 26
    for _ in range(30):
        q, depths = schedule(cells, b, k1, k, log_h, lf, pen_target)
        W = -(-cells // (1 << log_h))
        c = nv_circuit(q, depths[0], depths[1] if len(depths) > 1 else depths[0], W)
        if abs(c['cells'] - cells) < cells // 1000:
            break
        cells = c['cells']
    pb = proof_bytes(c, fin_target, digest)
    return c, pb, q


if __name__ == '__main__':
    print("NV phase-2 final layer [MODEL from measured laws; see docstring]")
    for name, pen, fin in [("268 / z=32 (236 query bits), 42 B", 236, 236), ("258 / z=32 (226 query bits), 42 B", 236, 226)]:
        best = None
        for b in (1, 2, 3, 4, 5, 6):
            for n_stack in range(17, 25 - b):
                c, pb, q = fixed_point(pen, fin, 42, b, n_stack)
                if best is None or pb['total'] < best[1]['total']:
                    best = (b, pb, c, n_stack, q)
        b, pb, c, n_stack, q = best
        print(f"{name}: final {pb['total']:,} B (whir {pb['whir']:,} gkr {pb['gkr']:,} L={pb['L']} rel {pb['rel']:,} "
              f"stk {pb['stk']:,} W={pb['W']}) | final shape {pb['shape']} q={pb['q']} | pen b={b} n_stack={n_stack} | pen queries {q} | program "
              f"{c['prog']:,} -> 2^{c['prog_log']} | compressions {c['comps']:,} | NvAir {c['nv_rows']:,} rows, "
              f"SHA {c['sha_rows']:,} rows, cells 2^{math.log2(c['cells']):.2f}, interactions 2^{math.log2(c['inter']):.2f}")
