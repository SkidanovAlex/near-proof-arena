"""PQ prover latency model: base -> aggregation -> NV chain -> final, on H200 GPUs.

lane/pq-prover-latency.  MODEL.  Labels used in the output and LATENCY.md:
  M  measured on this host (logs/), C  cited vendor / public benchmark, D  derived, A  assumption.

Structure (all sizes from the lane's measured laws; see ../results/pq-recursion-nv/extrapolate_nv2.py):
  * the NV fixed point at the real settings (268-bit with z = 32 -> 236 query bits, 42-B digests,
    x15, k1 = 1, WHIR-Y, T*, tight heights): penultimate shape b = 6, n_stack = 17, NV circuit
    2^26.13 cells (NvAir 327k rows, SHA 295k rows);
  * the final layer = the same NV circuit committed at its own WHIR shape (ext.py `layer`).
Per-layer GPU work (D from the shape):
  commit   NTT points 15 * 2^(log_h + b) * W (base) + WHIR rounds' Ext12 codewords (12x per point),
           SHA-512 compressions for coset leaves + nodes (+ the rounds' Ext12 leaves),
  prove    zerocheck + LogUp-GKR, calibrated per trace row from the CPU NV-layer run (M) and
           converted to Ext12-multiplication equivalents (M: the CPU Ext12 mul rate),
  grind    2^z SHA-512 compressions per WHIR query phase (one per round), perfectly parallel.
"""
import math
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'results', 'pq-recursion-nv'))
sys.path.insert(0, os.path.join(HERE, '..', 'results', 'pq384-sha-air2', 'model'))
import ext  # noqa: E402
import extrapolate_nv2 as X  # noqa: E402

L15 = math.log2(15)

# ---------------------------------------------------------------- measured on this host (M)
CPU = dict(
    sha_compress_1t=3.44e6,      # sha2 0.10 compress512, 1 thread (logs/micro-sha-grind-ext.log)
    sha_compress_32t=45.1e6,     # 32 threads (16 Zen 5 cores + SMT)
    openssl_sha512_1t=6.0e6,     # openssl speed sha512, 8 KiB blocks: 769 MB/s / 128 B
    grind_32t=34.3e6,            # honest T* pow_step attempts/s, 32 threads -> 2^32 in 125 s
    grind_8t=13.3e6,             # 8 threads -> 2^32 in 322 s (mean; the 65.5 s note was one lucky grind)
    ext12_mul_1t=2.58e6,         # p3 BinomialExtensionField<BabyBear,12> mul, 388 ns
    ext12_mul_32t=36.9e6,
    bb_mul_1t=6.4e8,
    merkle_ns_per_cell_32t=4.1,  # SHA-384 Merkle, coset leaves k1=1, 42 B, W=32 (1.0 ns/byte)
    rs_ns_per_cell_32t=20.0,     # x15 RS encode as built (per-column Radix2DitParallel), W=32, 2^21x15
)

# ---------------------------------------------------------------- H200 (C / A), (low, mid, high)
GPU = dict(
    # hashcat v6.2.6 mode 1700 (SHA2-512), NVIDIA H100 80GB HBM3 (SXM), 5,408.6 MH/s per GPU (C).
    # H200 = same GH100 die, SM count and clocks; only HBM differs -> same compression rate (D).
    # A grind attempt is one compression (T* block 105/109 B), the hashcat case; hashcat's early
    # exit / precomputation tricks are worth ~10 %, so the honest grind rate is (A):
    grind=(3.5e9, 4.5e9, 5.4e9),
    # Merkle leaves/nodes read operands from HBM and write digests: (A) 50-85 % of hashcat.
    sha_merkle=(2.7e9, 3.5e9, 4.6e9),
    # BabyBear LDE points/s per GPU (coset NTT from coefficients, fused leaf hashing in the epilogue).
    # Roofline: HBM3e 4.8 TB/s, ~3 passes x 8 B -> 2e11/s; 16.7 TIMAD/s / ~130 ops -> 1.3e11/s (D);
    # sustained (A):
    ntt=(3e10, 6e10, 1.2e11),
    # Ext12 mul: 144 32x32->64 MACs (2 issue slots each) + 12 Montgomery reductions + W-fold
    # ~ 400 int32 ops -> 4.2e10/s at 100 % of 16.7 TIMAD/s (D); sustained 20-60 % (A):
    ext12_mul=(0.8e10, 1.5e10, 2.5e10),
    # efficiency of spreading one proof's work over N GPUs (A): intra-node NVLink / 4-node IB
    eta_node=(0.75, 0.85, 0.92),
    eta_multi=(0.55, 0.7, 0.85),
    # serial per-layer overhead: ~300-600 sumcheck/GKR rounds x (transcript + all-reduce),
    # kernel launches, host tracegen of the verifier program (A, seconds)
    layer_serial=(0.12, 0.06, 0.03),
)
LMH = {'low': 0, 'mid': 1, 'high': 2}   # 'low' = pessimistic GPU, 'high' = optimistic


def g(key, case):
    return GPU[key][LMH[case]]


# ---------------------------------------------------------------- zerocheck + LogUp-GKR work
# Bottom-up count (D): after the univariate-skip round 0 (base field, l_skip = 2) the zerocheck
# evaluates each AIR's constraint DAG in Ext12 at (d + 1) points on N/2 + N/4 + ... = N/4 rows;
# a DAG node costs ~0.42 Ext12-mul equivalents (A: ~40 % of nodes are products, adds ~3 %).
# LogUp-GKR: ~40 Ext12 muls per fraction over all layers (A).  DAG node counts are measured by the
# NV verifier program (NV_DAG lines, logs/nvp2-T268.log): NvAir 3,637, Sha512Air 12,718.
AIRS = dict(nv=dict(deg=8, nodes=3637, ipr=55), sha=dict(deg=21, nodes=12718, ipr=14))
NODE_MUL_EQ = 0.42
GKR_MUL_PER_FRACTION = 40
# CPU calibration (M, logs/nv-layer-s16.log, 32 threads): prove_zerocheck_and_logup = 1,124 s for
# NvAir 2^18 + Sha512Air 2^16 rows (+ byte table 2^16) = 4.15e10 CPU-Ext12-mul equivalents, i.e.
# 12.0x the bottom-up count (3.45e9).  The pessimistic GPU case keeps that 12x overhead, the mid
# case assumes a GPU implementation 3x from the bottom-up count, the optimistic 1.5x.
ZC_OVERHEAD = (12.0, 4.0, 1.5)


def pow2(x):
    return 1 << math.ceil(math.log2(max(1, x)))


def zc_ext12_muls(nv_rows, sha_rows, case='mid', bottom_up=False):
    """Ext12-mul equivalents of zerocheck + LogUp-GKR for an NV-circuit layer (padded heights)."""
    hn, hs = pow2(nv_rows), pow2(sha_rows)
    a, s = AIRS['nv'], AIRS['sha']
    zc = (a['deg'] + 1) * hn / 4 * a['nodes'] * NODE_MUL_EQ + (s['deg'] + 1) * hs / 4 * s['nodes'] * NODE_MUL_EQ
    gkr = (hn * a['ipr'] + hs * s['ipr'] + 65536) * GKR_MUL_PER_FRACTION
    base = zc + gkr
    return base if bottom_up else base * ZC_OVERHEAD[LMH[case]]


# ---------------------------------------------------------------- shapes
def nv_fixed_point(pen_b=6, pen_n_stack=17, target=236):
    c, pb, q = X.fixed_point(target, target, 42, pen_b, pen_n_stack)
    return c, pb, q


def layer_at(cells, b, target=236, digest=42, k1=None, k=None, log_h=None, kmax=5):
    """Best (min bytes) WHIR shape for `cells` at a fixed blowup b (others free)."""
    P = ext.P(target=target, m=3, extra=L15, shrink=0, digest=digest, colb=0)
    out = None
    for lh in ([log_h] if log_h else range(8, int(P['maxdom'] - b) + 1)):
        if cells / (1 << lh) > 1 << 14:
            continue
        for kk in ([k] if k else range(1, kmax + 1)):
            for k1_ in ([k1] if k1 else range(1, 6)):
                for lf in range(0, min(lh - k1_, 14) + 1):
                    if (lh - k1_ - lf) % kk:
                        continue
                    r = ext.layer(cells, X.COLS, b, k1_, kk, lh, lf, P)
                    if out is None or r['bytes'] < out['bytes']:
                        out = r
    return out


def final_bytes(c, r):
    """Final-proof bytes for NV circuit c at WHIR shape r (extrapolate_nv2.proof_bytes, fixed shape)."""
    w = r['bytes'] - (3112 + 8456 + 1840 + 861)
    gk, L = X.gkr(c['inter'])
    n = math.ceil(math.log2(max(c['nv_rows'], c['sha_rows']))) - X.L_SKIP
    return round(w + gk + X.relations(n) + X.stacking(r['log_h'] - X.L_SKIP, r['width']) + 73)


def commit_work(r, cols_width=None):
    """NTT points (base-equivalent) and SHA compressions of committing + WHIR rounds for shape r."""
    W = cols_width or r['width']
    dom = 15 * 2 ** (r['log_h'] + r['b'])
    ntt = dom * W
    leaf_blocks = -(-((2 ** r['k1']) * W * 4 + 58) // 128)
    leaves0 = dom / 2 ** r['k1']
    sha = leaves0 * (leaf_blocks + 1)
    for rd in r['rounds'][1:]:
        ntt += rd['leaves'] * 2 ** rd['kk'] * 12      # Ext12 codeword (keep-domain)
        sha += rd['leaves'] * (-(-((2 ** rd['kk']) * 48 + 58) // 128) + 1)
    return dict(ntt=ntt, sha=sha, rounds=len(r['rounds']), lde_bytes=dom * W * 4)


def layer_time(c, r, z, N, case, intra=None):
    """Seconds for one NV-circuit layer (trace c, WHIR shape r) proven on N GPUs."""
    w = commit_work(r)
    t_ntt = w['ntt'] / g('ntt', case)
    t_sha = w['sha'] / g('sha_merkle', case)
    t_zc = zc_ext12_muls(c['nv_rows'], c['sha_rows'], case) / g('ext12_mul', case)
    t_grind = w['rounds'] * 2 ** z / g('grind', case)
    eta = 1.0 if N == 1 else (g('eta_node', case) if N <= 8 else g('eta_multi', case))
    par = (t_ntt + t_sha + t_zc) / (N * eta)
    grind = t_grind / N              # embarrassingly parallel
    return dict(total=par + grind + g('layer_serial', case), ntt=t_ntt, sha=t_sha, zc=t_zc,
                grind_gpu_s=t_grind, grind=grind, gpu_s=t_ntt + t_sha + t_zc + t_grind,
                lde_tb=w['lde_bytes'] / 1e12, rounds=w['rounds'])


def expected_grind_tail(rounds, p=0.99):
    """Sum of `rounds` exponential(1) grind times: ratio of its p-quantile to its mean."""
    # Gamma(rounds, 1) quantile by bisection on the regularised lower incomplete gamma
    def cdf(x):
        s, term = 0.0, 1.0
        for i in range(rounds):
            if i:
                term *= x / i
            s += term
        return 1 - math.exp(-x) * s
    lo, hi = 0.0, 50.0 * rounds
    for _ in range(100):
        mid = (lo + hi) / 2
        lo, hi = (mid, hi) if cdf(mid) < p else (lo, mid)
    return lo / rounds


# ---------------------------------------------------------------- chain
def schedule(cells, b, log_h, x15, target, k1=1, k=4):
    P = ext.P(target=target, m=3, extra=L15 if x15 else 0.0, shrink=0, digest=42)
    lf = next(x for x in range(3, 12) if (log_h - k1 - x) % k == 0)
    r = ext.layer(cells, X.COLS, b, k1, k, log_h, lf, P)
    r['x15'] = x15
    r['depths'] = [math.ceil(math.log2(rd['leaves']) - 1e-9) for rd in r['rounds']]
    return r


def verifier_circuit(child, extra_prog=0, extra_comps=0):
    """NV circuit verifying one child proof with WHIR schedule `child` (extrapolate_nv2 laws)."""
    d = child['depths']
    c = X.nv_circuit(child['q'], d[0], d[1] if len(d) > 1 else d[0], child['width'])
    if extra_prog or extra_comps:
        prog = c['prog'] + extra_prog
        comps = c['comps'] + extra_comps
        nv_rows = c['nv_rows'] + extra_prog * 3 // 2 + 8 * extra_comps
        sha_rows = c['sha_rows'] + X.SHA_ROWS * extra_comps
        c = dict(prog=prog, prog_log=math.ceil(math.log2(prog + 2)), comps=comps, nv_rows=nv_rows,
                 sha_rows=sha_rows, cells=nv_rows * 70 + sha_rows * 171 + 64 * 13 + 65536 * 5,
                 inter=nv_rows * X.NV_IPR + sha_rows * X.SHA_IPR + 64 * 2 + 65536)
    return c


def commit_shape(cells, b, x15, target, log_h=None):
    """WHIR shape a layer of `cells` is committed with: log_h as large as the 2-adic domain allows."""
    if log_h is None:
        log_h = min(27 - b, max(17, math.ceil(math.log2(cells)) - 7))
    return schedule(cells, b, log_h, x15, target)


# ---------------------------------------------------------------- base (V3-PERF-DESIGN §7, ML backend)
# PLACEHOLDER until lane/pq-base-aggregation DESIGN-BASE.md lands: V3-PERF's ML (zerocheck + LogUp-GKR
# + multilinear PCS) per-op costs at E = 10, scaled to Ext12 (A: x1.3 on the work), at V3-PERF's
# GPU efficiency assumption (35 % of peak INT32 = 8.3 G cell-eq/s/GPU; 20 % / 60 % for low / high).
BASE = dict(
    typical=dict(ops=4.1e7, cells_op=10, celleq_op=98),
    mainnet=dict(ops=3.6e8, cells_op=21, celleq_op=207),
    adversarial=dict(ops=1.22e9, cells_op=32, celleq_op=387),
)
BASE_EXT12 = 1.3          # A
BASE_POSTEXEC = 0.65      # A: share of base work after execution ends (main commit streams)
BASE_EFF = (0.20, 0.35, 0.60)


def base_time(cls, N, case, z=32):
    b = BASE[cls]
    r = 8.3e9 * BASE_EFF[LMH[case]] / 0.35
    gpu_s = b['ops'] * b['celleq_op'] * BASE_EXT12 / r
    eta = g('eta_node', case) if N <= 8 else g('eta_multi', case)
    shape = commit_shape(b['ops'] * b['cells_op'], 2, False, 268 - z, log_h=None)
    t_grind = len(shape['rounds']) * 2 ** z / g('grind', case) / N
    return dict(gpu_s=gpu_s, post=BASE_POSTEXEC * gpu_s / (N * eta) + t_grind + g('layer_serial', case),
                cells=b['ops'] * b['cells_op'], shape=shape, grind=t_grind)


# base-DAG / column absorption extra in L1's program (A): the WASM machine AIR set is wider than NV's
L1_EXTRA_PROG = 150_000
L1_EXTRA_COMPS = 1_500


def chain(cls, N, case, z=32, z_inner=32, b_final=6, b_l1=3, deep=True, final_target=None):
    """Critical path after execution: base -> L1 -> [L2 (pen)] -> final.  Returns dict of stages."""
    tgt_in = 268 - z_inner
    tgt_fin = final_target or (268 - z)
    base = base_time(cls, N, case, z_inner)
    st = dict(base=base['post'])
    c1 = verifier_circuit(base['shape'], L1_EXTRA_PROG, L1_EXTRA_COMPS)
    if deep:
        s1 = commit_shape(c1['cells'], b_l1, False, tgt_in)
        t1 = layer_time(c1, s1, z_inner, N, case)
        c2 = verifier_circuit(s1)
        s2 = schedule(c2['cells'], 6, 19, True, tgt_in)        # pen shape (b = 6, n_stack = 17)
        t2 = layer_time(c2, s2, z_inner, N, case)
        cf = verifier_circuit(s2)
        st.update(L1=t1['total'], L2=t2['total'])
        layers = [('L1', c1, s1, t1), ('L2', c2, s2, t2)]
    else:
        s1 = schedule(c1['cells'], 6, min(21, max(19, math.ceil(math.log2(c1['cells'])) - 7)), True, tgt_in)
        t1 = layer_time(c1, s1, z_inner, N, case)
        cf = verifier_circuit(s1)
        st.update(L1=t1['total'])
        layers = [('L1', c1, s1, t1)]
    rf = layer_at(cf['cells'], b_final, target=tgt_fin)
    tf = layer_time(cf, rf, z, N, case)
    st['final'] = tf['total']
    st['total'] = sum(st.values())
    return dict(stages=st, bytes=final_bytes(cf, rf), final=(cf, rf, tf), layers=layers, base=base)


def fmt(x):
    return f"{x:.2f}"


def report():
    out = []
    p = out.append
    c, pb, q = nv_fixed_point()
    p("== NV fixed point at the real settings (extrapolate_nv2, 268 / z = 32, 42 B) ==")
    p(f"pen b=6 n_stack=17 queries {q}; NV circuit {c['cells']:,} cells (2^{math.log2(c['cells']):.2f}), "
      f"NvAir {c['nv_rows']:,} rows, SHA {c['sha_rows']:,} rows, {c['comps']:,} compressions; final {pb['total']:,} B")
    p("")
    p("== zerocheck + LogUp-GKR work (Ext12-mul equivalents) ==")
    bu = zc_ext12_muls(2 ** 18, 2 ** 16, bottom_up=True)
    p(f"CPU run s16 (NvAir 2^18, SHA 2^16): bottom-up {bu:.3e}; measured 1,124 s x 36.9 M/s = {1124 * 36.9e6:.3e} (x{1124 * 36.9e6 / bu:.1f})")
    p(f"NV fixed point (padded 2^19 / 2^19): bottom-up {zc_ext12_muls(c['nv_rows'], c['sha_rows'], bottom_up=True):.3e}")
    p("")
    p("== per-layer GPU work, adversarial chain, mid case (GPU-seconds on one H200) ==")
    r = chain('adversarial', 32, 'mid')
    p(f"{'layer':6} {'cells':>10} {'b':>2} {'log_h':>5} {'W':>5} {'queries':24} {'LDE TB':>7} {'NTT':>6} {'SHA':>6} {'ZC+GKR':>7} {'grind':>6} {'GPU-s':>6}")
    for n, cc, s, t in r['layers'] + [('final', r['final'][0], r['final'][1], r['final'][2])]:
        p(f"{n:6} {cc['cells']:10.3e} {s['b']:2} {s['log_h']:5} {int(s['width']):5} {str(s['q']):24} {t['lde_tb']:7.3f} "
          f"{t['ntt']:6.2f} {t['sha']:6.2f} {t['zc']:7.2f} {t['grind_gpu_s']:6.2f} {t['gpu_s']:6.2f}")
    b = r['base']
    p(f"base   {b['cells']:10.3e} GPU-s {b['gpu_s']:.1f} (V3-PERF ML x1.3), proof shape b=2 log_h={b['shape']['log_h']} "
      f"W={int(b['shape']['width'])} q={b['shape']['q']}")
    p("")
    p("== end to end after execution ends (s): base phase B + L1 + L2 + final; [optimistic / mid / pessimistic] ==")
    for cls in BASE:
        for N in (8, 16, 32):
            rows = {case: chain(cls, N, case) for case in ('high', 'mid', 'low')}
            m = rows['mid']['stages']
            p(f"{cls:12} N={N:2}: total {fmt(rows['high']['stages']['total'])} / {fmt(m['total'])} / {fmt(rows['low']['stages']['total'])}"
              f"   mid: base {fmt(m['base'])} L1 {fmt(m['L1'])} L2 {fmt(m['L2'])} final {fmt(m['final'])}   final proof {rows['mid']['bytes']:,} B")
    p("")
    p("== lever: final-layer blowup b (final layer only; 268 / z = 32; N = 8 / 32; mid) ==")
    cf = r['final'][0]
    for bf in range(3, 10):
        rf = layer_at(cf['cells'], bf, target=236)
        t8 = layer_time(cf, rf, 32, 8, 'mid')
        t32 = layer_time(cf, rf, 32, 32, 'mid')
        p(f"b={bf}: {final_bytes(cf, rf):,} B  shape log_h={rf['log_h']} W={int(rf['width'])} q={rf['q']}  LDE {t8['lde_tb']:.3f} TB  "
          f"GPU-s {t8['gpu_s']:.1f}  N=8 {fmt(t8['total'])} s  N=32 {fmt(t32['total'])} s")
    p("")
    p("== lever: final-layer grinding z (b = 6; 268 - z query bits) ==")
    for z in (0, 16, 20, 24, 28, 32, 36):
        rf = layer_at(cf['cells'], 6, target=268 - z)
        t8 = layer_time(cf, rf, z, 8, 'mid')
        t32 = layer_time(cf, rf, z, 32, 'mid')
        p(f"z={z:2}: {final_bytes(cf, rf):,} B  q={rf['q']}  grind {t8['grind_gpu_s']:.2f} GPU-s (mean; p99 x{expected_grind_tail(t8['rounds']):.2f})"
          f"  final layer N=8 {fmt(t8['total'])} s  N=32 {fmt(t32['total'])} s")
    p("")
    p("== lever: inner-layer grinding z_inner (adversarial, N = 8 / 32, mid; final z = 32, b = 6) ==")
    for zi in (0, 16, 24, 32):
        a8 = chain('adversarial', 8, 'mid', z_inner=zi)
        a32 = chain('adversarial', 32, 'mid', z_inner=zi)
        p(f"z_inner={zi:2}: tail (L1+L2+final) N=8 {fmt(a8['stages']['L1'] + a8['stages']['L2'] + a8['stages']['final'])} s,"
          f" N=32 {fmt(a32['stages']['L1'] + a32['stages']['L2'] + a32['stages']['final'])} s; final {a32['bytes']:,} B;"
          f" L2 circuit {a32['layers'][1][1]['cells']:.3e} cells")
    p("")
    p("== lever: recursion depth (adversarial, mid) ==")
    for deep in (True, False):
        for N in (8, 32):
            a = chain('adversarial', N, 'mid', deep=deep)
            s = a['stages']
            p(f"{'deep: base->L1(b3)->L2(b6,x15)->final' if deep else 'shallow: base->L1(b6,x15)->final':42} N={N:2}: tail "
              f"{fmt(s['total'] - s['base'])} s, final {a['bytes']:,} B, final circuit {a['final'][0]['cells']:.3e} cells")
    p("")
    p("== lever: final query target 258 bits (z = 32 -> 226) ==")
    for bf in (5, 6, 7):
        a = chain('adversarial', 32, 'mid', b_final=bf, final_target=226)
        a8 = chain('adversarial', 8, 'mid', b_final=bf, final_target=226)
        p(f"b={bf}: final {a['bytes']:,} B; final layer N=8 {fmt(a8['stages']['final'])} s, N=32 {fmt(a['stages']['final'])} s")
    p("")
    p("== GPUs needed (mid / optimistic), total after execution ==")
    for cls in BASE:
        for tgt in (1.0, 2.0, 3.0):
            res = []
            for case in ('mid', 'high'):
                n = next((N for N in (8, 16, 24, 32, 48, 64, 96, 128, 192, 256) if chain(cls, N, case, z_inner=24)['stages']['total'] <= tgt), None)
                res.append(str(n) if n else '>256')
            p(f"{cls:12} <= {tgt:.0f} s: N = {res[0]} (mid) / {res[1]} (optimistic)   [z_inner = 24]")
    p("")
    p("== grinding tail (z = 32 everywhere, 4-6 query phases per layer) ==")
    a = chain('adversarial', 32, 'mid')
    nr = len(a['base']['shape']['rounds']) + sum(t['rounds'] for _, _, _, t in a['layers']) + a['final'][2]['rounds']
    for N in (8, 16, 32):
        mean = nr * 2 ** 32 / g('grind', 'mid') / N
        p(f"N={N:2}: {nr} grinds on the critical path, mean {mean:.2f} s, p99 {mean * expected_grind_tail(nr):.2f} s, p99.9 {mean * expected_grind_tail(nr, 0.999):.2f} s")
    return "\n".join(out)


if __name__ == '__main__':
    print(report())
