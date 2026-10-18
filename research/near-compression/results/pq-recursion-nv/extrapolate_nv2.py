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

ext.bits = lambda rate, m: bits_mca(rate, m)  # MCA regime hook (see bits_mca)

L15 = math.log2(15)

# ---- WHIR per-query bits regime (MCA): 'm3' (today: BCGM, ListDecoding{m: 3}), 'm64' (O-1:
# DKT26 Thm 5.12, ListDecoding{m: 64}), 'O2' (O-1 + O-2: per-round first-order agreement
# a_i = (a1(rho_i)/sqrt(rho_i) + 0.05) sqrt(rho_i), the rule certified in
# lane/pq-mca-upgrade calc/dkt_certs.json / bound_mca.py; the table a_i is bound into the vk;
# +48 B per later round reserved for a second OOD answer).  Env NV_MCA; default m3.
# O-1 / O-2 are pending verification (lane/pq-mca-upgrade @6841b5f56, MCA-UPGRADE.md).
MCA = os.environ.get('NV_MCA', 'm3')
O2_MARGIN = 0.05


def a1(r):
    """First-order agreement a1(rho) of DKT26 (size_mca.py / bound_mca.py)."""
    rc = 11 - 3 * math.sqrt(13)
    if r < rc:
        s, lo, hi = math.sqrt(r / 2), 0.0, 1.0
        for _ in range(200):
            mid = (lo + hi) / 2
            lo, hi = (mid, hi) if mid * mid * (mid + 3) < s else (lo, mid)
        return s * (1 + lo)
    return (3 * r + 2 * math.sqrt(r * (5 - r) * (2 - r))) / (8 - r)


def agreement_table(rates):
    """O-2: per-round agreement a_i / sqrt(rho_i) for the rounds' rates (-log2 rho_i)."""
    return [min(a1(2 ** -r) / math.sqrt(2 ** -r) + O2_MARGIN, 1 + 1 / 128) for r in rates]


def bits_mca(rate, m):
    if MCA == 'm3':
        return rate / 2 - math.log2(1 + 1 / 6)
    if MCA == 'm64':
        return rate / 2 - math.log2(1 + 1 / 128)
    if MCA == 'O2':
        return rate / 2 - math.log2(agreement_table([rate])[0])
    raise ValueError(MCA)


def o2_reserve(rounds):
    return 48 * (rounds - 1) if MCA == 'O2' else 0
L_SKIP = 2
COLS, ROT = 73 + 171 + 13 + 5, 36 + 144 + 11 + 2   # NvAir 73 columns after T*
D = 21
AIRS = 4
NV_IPR, SHA_IPR, SHA_ROWS = 55, 14, 43
# measured program costs (A2 of nvp2-T102: child = the NV level itself)
P_FIXED = 72_278          # preamble + app table (10,9k) + GKR + DAG + stacking
APP_ROWS = 10_988          # level-1 table (data rows)
Q0_COST = 451              # round 0 (k1 = 1), depth 20 + 4 (x15)
QR_COST = 530              # rounds >= 1 (k = 4), depth 17 + 4
PER_LEVEL = 10             # ALU rows per Merkle path level
FINAL_PER_Q = 110          # final WHIR check per query (powers, eq, Horner)
TRANSCRIPT_BLOCKS = 1_600  # transcript compressions (measured ~1.5k)
TR_ROWS = 6_000            # hash-chain + sample rows
DEDUP = False              # in-circuit multiproof dedup: NOT possible with a static (bound) program -
                           # which nodes coincide depends on the sampled indices; model-only what-if


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
    if DEDUP:
        # in-circuit multiproof: each distinct node of the union of the paths hashed once
        # (rounds >= 1 split evenly; expected distinct nodes for uniform queries)
        def nodes(q, depth):
            return sum(min(q, (1 << (depth - l)) * (1 - (1 - 2.0 ** -(depth - l)) ** q)) for l in range(depth))
        per_r = [rounds_q[0]] + list(rounds_q[1:])
        nn = nodes(q0, depth0) + sum(nodes(x, depthr) for x in rounds_q[1:])
        comps = int(q0 * blk(2 * child_W * 4) + qr * blk(16 * 48) + nn) + TRANSCRIPT_BLOCKS
    else:
        comps = q0 * (blk(2 * child_W * 4) + depth0) + qr * (blk(16 * 48) + depthr) + TRANSCRIPT_BLOCKS
    glue = 8 * comps
    prog += prog % 2
    nv_rows = prog + prog // 2 + APP_ROWS // 2 + glue + TR_ROWS
    sha_rows = SHA_ROWS * comps
    return dict(prog=prog, prog_log=prog_log, comps=comps, nv_rows=nv_rows, sha_rows=sha_rows,
                cells=nv_rows * 73 + sha_rows * 171 + 64 * 13 + 65536 * 5,
                inter=nv_rows * NV_IPR + sha_rows * SHA_IPR + 64 * 2 + 65536)


def best_capped(cells, P, bmax):
    """ext.best restricted to log_blowup <= bmax (memory: the x15 codeword is cells * 2^b * 15)."""
    out = None
    for b in range(1, bmax + 1):
        for log_h in range(8, int(P['maxdom'] - b) + 1):
            if cells / (1 << log_h) > 1 << 14:
                continue
            for k in range(1, 6):
                for k1 in range(1, 6):
                    for lf in range(0, min(log_h - k1, 14) + 1):
                        if (log_h - k1 - lf) % k:
                            continue
                        r = ext.layer(cells, COLS, b, k1, k, log_h, lf, P)
                        if out is None or r['bytes'] < out['bytes']:
                            out = r
    return out


def proof_bytes(c, target, digest, bmax=None):
    """Final-layer proof of the NV circuit `c`; the final layer picks its own WHIR shape."""
    P = ext.P(target=target, m=3, extra=L15, shrink=0, digest=digest)
    r = ext.best(c['cells'], COLS, dict(P, colb=0)) if bmax is None else best_capped(c['cells'], dict(P, colb=0), bmax)
    log_h = r['log_h']
    n_stack = log_h - L_SKIP
    W = r['width']
    w = r['bytes'] - (3112 + 8456 + 1840 + 861)
    g, L = gkr(c['inter'])
    n = math.ceil(math.log2(max(c['nv_rows'], c['sha_rows']))) - L_SKIP
    rel = relations(n)
    st = stacking(n_stack, W)
    return dict(total=round(w + g + rel + st + 73 + o2_reserve(len(r['q']))), whir=round(w), gkr=g, L=L, rel=rel, stk=st, W=W,
                q=r['q'], shape=dict(b=r['b'], k1=r['k1'], k=r['k'], log_h=log_h, lf=r['log_final']))


def schedule(cells, b, k1, k, log_h, lf, target):
    P = ext.P(target=target, m=3, extra=L15, shrink=0)
    r = ext.layer(cells, COLS, b, k1, k, log_h, lf, P)
    return r['q'], [math.ceil(math.log2(rd['leaves']) - 1e-9) for rd in r['rounds']]


def fixed_point(pen_target, fin_target, digest, b, n_stack, k1=1, k=4, fin_bmax=None):
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
    pb = proof_bytes(c, fin_target, digest, fin_bmax)
    return c, pb, q


def report(name, b, n_stack, fin_bmax=None, pen=236, fin=236):
    c, pb, q = fixed_point(pen, fin, 42, b, n_stack, fin_bmax=fin_bmax)
    print(f"{name}: final {pb['total']:,} B (whir {pb['whir']:,} gkr {pb['gkr']:,} rel {pb['rel']:,} stk {pb['stk']:,} W={pb['W']}) "
          f"| final shape {pb['shape']} q={pb['q']} | pen b={b} n_stack={n_stack} queries {q} | program {c['prog']:,} | "
          f"NvAir {c['nv_rows']:,} SHA {c['sha_rows']:,} rows, cells 2^{math.log2(c['cells']):.2f}")


if __name__ == '__main__':
    if len(sys.argv) > 1 and sys.argv[1] == 'run':
        # the measured run's shape: pen b=2 n_stack=18; final b <= 3 (fits 100 GB)
        report("268/z32 pen b2 ns18, final b<=3", 2, 18, fin_bmax=3)
        report("268/z32 pen b2 ns18, final b<=2", 2, 18, fin_bmax=2)
        report("268/z32 pen b2 ns18, final any b", 2, 18)
        sys.exit(0)
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
