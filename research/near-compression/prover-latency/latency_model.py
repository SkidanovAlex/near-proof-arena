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
# case assumes a GPU implementation 4x from the bottom-up count, the optimistic 1.5x.
# Cross-check (M, logs/nv-layer-s17.log, SHA 2^17): 1,754 s = 6.47e10 vs bottom-up 5.40e9 (12.0x again);
# per-row split s17 - s16: SHA 9.6 ms/row, NvAir 1.9 ms/row, ratio 5.1 (bottom-up 5.3).
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
    dom = r['rounds'][0]['leaves'] * 2 ** r['k1']      # c * 2^(log_h + b), c = 15 or 1
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
def schedule(cells, b, log_h, x15, target, k1=1, k=4, m=3):
    P = ext.P(target=target, m=m, extra=L15 if x15 else 0.0, shrink=0, digest=42)
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


# ---------------------------------------------------------------- base + aggregation (DESIGN-BASE)
# lane/pq-base-aggregation @ 6c97b4b28, DESIGN-BASE.md §2.4, §3, §5, §7 (labels there: [A]/[L]/[B]):
#   segments of 2^23 WASM ops; work per op on SWIRL at Ext12 = 118 / 248 / 546 cell-eq (typical /
#   mainnet / adversarial) at 7.1 G cell-eq/s per H200 (PERF: 35 % of peak INT32); execution 1.2 s,
#   base GPU-bound and streaming during execution; pinned base WHIR b = 1, m = 16, z = 32,
#   queries [518, 247, 80, 48, 34] (5 query phases); tree nodes commit at c = 1, b = 3, m = 8.
#   NV-cell sizes [L]: one segment 2^28.04, L1 (design G, one global child, W = 690) 2^28.73,
#   N1x8 2^30.93, N2x4 (preprocessed program) 2^29.16, tail T1 / T2 / FINAL at the fixed point.
BASE = dict(
    typical=dict(ops=4.1e7, celleq_op=118, cells_op=10),
    mainnet=dict(ops=3.6e8, celleq_op=248, cells_op=21),
    adversarial=dict(ops=1.22e9, celleq_op=546, cells_op=38),
)
SEG_OPS = 2 ** 23
# one recursive proof is sharded over at most 32 GPUs (4 x 8, P-PERF-7); beyond that the efficiency of
# a single SWIRL proof's distributed sumchecks is unknown, so extra GPUs only shorten the base (A)
MAX_GPUS_PER_PROOF = 32
EXEC_S = 1.2
BASE_RATE = 7.1e9
BASE_EFF = (0.20 / 0.35, 1.0, 0.60 / 0.35)    # GPU efficiency 20 / 35 / 60 % of peak (PERF sensitivity)
BASE_ROUNDS = 5                                # base WHIR query phases (pinned schedule)
NODE = dict(L1=2 ** 28.73, N1x8=2 ** 30.93, N2x4=2 ** 29.16)
NV_COLS_ROW = 73 + 171                         # NvAir + SHA AIR columns


def l1_cells(cls):
    """Design-G L1: verifying the one global base proof (pinned b = 1, m = 16, q0 = 518, log_h = 26).
    DESIGN-BASE's 2^28.73 is for the adversarial width W = 690; the round-0 leaf blocks scale with W
    (518 queries x ceil((8W + 58) / 128) blocks x (43 SHA rows x 171 + 8 NvAir rows x 73) cells) [D]."""
    blocks = lambda W: -(-(8 * W + 58) // 128)
    W = max(1, math.ceil(BASE[cls]['ops'] * BASE[cls]['cells_op'] / 2 ** 26))
    return NODE['L1'] - 518 * (blocks(690) - blocks(W)) * (43 * 171 + 8 * 73)


def node_circuit(cells):
    """NV-AIR node of `cells`: rows split evenly between NvAir and the SHA AIR (as in a 1-segment verifier:
    program 625k rows -> ~1.15M NvAir rows, 26.5k compressions -> 1.14M SHA rows) [A]."""
    r = int(cells / NV_COLS_ROW)
    return dict(cells=cells, nv_rows=r, sha_rows=r, inter=r * (55 + 14))


def base_time(cls, N, case, z=32, design='G'):
    b = BASE[cls]
    rate = BASE_RATE * BASE_EFF[LMH[case]]
    gpu_s = b['ops'] * b['celleq_op'] / rate
    S = max(1, math.ceil(b['ops'] / SEG_OPS))
    # grinding: design G has one transcript (5 grinds spread over all GPUs); independent segment
    # proofs (T designs) grind 5 x 2^z each, on their own GPU
    grind_one = 2 ** z / g('grind', case)
    if design == 'G':
        grind_gpu_s = BASE_ROUNDS * grind_one
        post = max(gpu_s / (N * g('eta_multi' if N > 8 else 'eta_node', case)) - EXEC_S, 0) \
            + grind_gpu_s / N + g('layer_serial', case)
    else:
        grind_gpu_s = S * BASE_ROUNDS * grind_one
        # independent proofs: ~1.0 efficiency; the last segment proof (one GPU) cannot finish earlier
        # than its own work + its grinds after execution ends
        per_seg = gpu_s / S + BASE_ROUNDS * grind_one
        post = max((gpu_s + grind_gpu_s) / N - EXEC_S, per_seg) + g('layer_serial', case)
    return dict(gpu_s=gpu_s, grind_gpu_s=grind_gpu_s, post=post, S=S)


def level_time(c, shape, z, gpus_per_node, nodes, N, case):
    """A level of `nodes` independent proofs, each spread over <= gpus_per_node GPUs, on N GPUs."""
    t1 = layer_time(c, shape, z, min(gpus_per_node, N), case)
    waves = math.ceil(nodes * min(gpus_per_node, N) / N)
    return dict(t1, total=t1['total'] * waves, waves=waves)


def tail(child_shape, N, case, z_inner, z, b_final, final_target, tail_levels=2):
    """T1 [, T2] at the inner shape (c = 15, b = 6, n_stack = 17), then FINAL at b_final."""
    out, shape = [], child_shape
    for name in ('T1', 'T2')[:tail_levels]:
        c = verifier_circuit(shape)
        s = schedule(c['cells'], 6, 19, True, 268 - z_inner)
        out.append((name, c, s, layer_time(c, s, z_inner, min(N, MAX_GPUS_PER_PROOF), case)))
        shape = s
    cf = verifier_circuit(shape)
    rf = layer_at(cf['cells'], b_final, target=final_target or (268 - z))
    out.append(('FINAL', cf, rf, layer_time(cf, rf, z, min(N, MAX_GPUS_PER_PROOF), case)))
    return out, final_bytes(cf, rf)


def chain(cls, N, case, z=32, z_inner=32, z_base=32, b_final=6, final_target=None, design='G', tail_levels=2):
    """Critical path after execution ends.  design G: base (one shared-transcript proof) -> L1 -> T1 -> T2
    -> FINAL.  design T8: segment proofs -> N1x8 -> N2x4 levels -> T1 -> T2 -> FINAL (DESIGN-BASE §5.3)."""
    base = base_time(cls, N, case, z_base, design)
    st, layers = dict(base=base['post']), []
    node_shape = lambda cells: schedule(cells, 3, min(24, max(17, math.ceil(math.log2(cells / 141)))), False,
                                        268 - z_inner, m=8)
    if design == 'G':
        c1 = node_circuit(l1_cells(cls))
        s1 = node_shape(c1['cells'])
        lt = level_time(c1, s1, z_inner, MAX_GPUS_PER_PROOF, 1, N, case)
        layers.append(('L1', c1, s1, lt))
        last = s1
    else:
        S = base['S']
        n1 = math.ceil(S / 8)
        c1 = node_circuit(NODE['N1x8'] * min(8, S) / 8)
        s1 = node_shape(c1['cells'])
        layers.append(('N1x8', c1, s1, level_time(c1, s1, z_inner, 8, n1, N, case)))
        last, nodes = s1, n1
        while nodes > 1:
            nodes = math.ceil(nodes / 4)
            c2 = node_circuit(NODE['N2x4'])
            s2 = node_shape(c2['cells'])
            layers.append(('N2x4', c2, s2, level_time(c2, s2, z_inner, 8, nodes, N, case)))
            last = s2
    t, nbytes = tail(last, N, case, z_inner, z, b_final, final_target, tail_levels)
    layers += t
    for name, c, s, tt in layers:
        st[name] = st.get(name, 0) + tt['total']
    st['total'] = sum(v for k, v in st.items())
    return dict(stages=st, bytes=nbytes, layers=layers, base=base, final=layers[-1][1:])


def fmt(x):
    return f"{x:.2f}"


def tail_s(r):
    return r['stages']['total'] - r['stages']['base']


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
    for case in ('mid', 'high'):
        p(f"== per-layer GPU work, design G, adversarial, {case} case (GPU-seconds on one H200; cell-eq per NV cell at 7.1 G/s) ==")
        r = chain('adversarial', 32, case)
        p(f"{'layer':6} {'NV cells':>10} {'b':>2} {'log_h':>5} {'W':>5} {'queries':26} {'LDE TB':>7} {'NTT':>6} {'SHA':>6} {'ZC+GKR':>7} {'grind':>6} {'GPU-s':>6} {'ceq/cell':>8}")
        for n, cc, s, t in r['layers']:
            p(f"{n:6} {cc['cells']:10.3e} {s['b']:2} {s['log_h']:5} {int(s['width']):5} {str(s['q']):26} {t['lde_tb']:7.3f} "
              f"{t['ntt']:6.2f} {t['sha']:6.2f} {t['zc']:7.2f} {t['grind_gpu_s']:6.2f} {t['gpu_s']:6.2f} {t['gpu_s'] * 7.1e9 / cc['cells']:8.0f}")
        b = r['base']
        p(f"base   {BASE['adversarial']['ops'] * 546 / 7.1e9:.0f} GPU-s at 35 % (DESIGN-BASE), {b['S']} segments; grinding (one transcript) {b['grind_gpu_s']:.1f} GPU-s")
        p("")
    p("== end to end after execution ends (s), design G; [optimistic / mid / pessimistic]; z = 32 everywhere ==")
    for cls in BASE:
        for N in (8, 16, 32):
            rows = {case: chain(cls, N, case) for case in ('high', 'mid', 'low')}
            m = rows['mid']['stages']
            p(f"{cls:12} N={N:2}: total {fmt(rows['high']['stages']['total'])} / {fmt(m['total'])} / {fmt(rows['low']['stages']['total'])}"
              f"   mid: base {fmt(m['base'])} L1 {fmt(m['L1'])} T1 {fmt(m['T1'])} T2 {fmt(m['T2'])} FINAL {fmt(m['FINAL'])}  ({rows['mid']['bytes']:,} B)")
    p("")
    p("== same, recommended latency settings: z_inner = z_base = 24, final z = 32, b_final = 6 ==")
    for cls in BASE:
        for N in (8, 16, 32):
            rows = {case: chain(cls, N, case, z_inner=24, z_base=24) for case in ('high', 'mid', 'low')}
            m = rows['mid']['stages']
            p(f"{cls:12} N={N:2}: total {fmt(rows['high']['stages']['total'])} / {fmt(m['total'])} / {fmt(rows['low']['stages']['total'])}"
              f"   mid: base {fmt(m['base'])} L1 {fmt(m['L1'])} T1 {fmt(m['T1'])} T2 {fmt(m['T2'])} FINAL {fmt(m['FINAL'])}  ({rows['mid']['bytes']:,} B)")
    p("")
    p("== design T8 (independent segment proofs, wide tree), adversarial, N = 32, mid ==")
    for zb in (32, 24, 0):
        r = chain('adversarial', 32, 'mid', design='T8', z_base=zb, z_inner=24)
        p(f"z_base={zb:2} z_inner=24: total {fmt(r['stages']['total'])} s = " + ", ".join(f"{k} {fmt(v)}" for k, v in r['stages'].items() if k != 'total')
          + f"; base grinding {r['base']['grind_gpu_s']:.0f} GPU-s over {r['base']['S']} segment proofs")
    p("")
    cf = chain('adversarial', 32, 'mid')['final'][0]
    p("== lever: final-layer blowup b (FINAL only; 268 / z = 32; mid) ==")
    for bf in range(3, 10):
        rf = layer_at(cf['cells'], bf, target=236)
        t8 = layer_time(cf, rf, 32, 8, 'mid')
        t32 = layer_time(cf, rf, 32, 32, 'mid')
        th = layer_time(cf, rf, 32, 32, 'high')
        p(f"b={bf}: {final_bytes(cf, rf):,} B  shape log_h={rf['log_h']} W={int(rf['width'])} q={rf['q']}  LDE {t8['lde_tb']:.3f} TB  "
          f"GPU-s {t8['gpu_s']:.1f} (NTT+SHA {t8['ntt'] + t8['sha']:.1f})  N=8 {fmt(t8['total'])} s  N=32 {fmt(t32['total'])} s (opt. {fmt(th['total'])})")
    p("")
    p("== lever: final-layer grinding z (b = 6; 268 - z query bits; mean grind, p99/mean for the layer's grinds) ==")
    for z in (0, 16, 20, 24, 28, 32, 36):
        rf = layer_at(cf['cells'], 6, target=268 - z)
        t8 = layer_time(cf, rf, z, 8, 'mid')
        t32 = layer_time(cf, rf, z, 32, 'mid')
        p(f"z={z:2}: {final_bytes(cf, rf):,} B  q={rf['q']}  grind {t8['grind_gpu_s']:.2f} GPU-s (p99 x{expected_grind_tail(t8['rounds']):.2f})"
          f"  FINAL N=8 {fmt(t8['total'])} s  N=32 {fmt(t32['total'])} s")
    p("")
    p("== lever: inner/base grinding (design G, adversarial, mid; final z = 32, b = 6) ==")
    for zi in (0, 16, 20, 24, 32):
        a8 = chain('adversarial', 8, 'mid', z_inner=zi, z_base=zi)
        a32 = chain('adversarial', 32, 'mid', z_inner=zi, z_base=zi)
        p(f"z_inner=z_base={zi:2}: tail N=8 {fmt(tail_s(a8))} s, N=32 {fmt(tail_s(a32))} s; total N=32 {fmt(a32['stages']['total'])} s;"
          f" final {a32['bytes']:,} B; T2 circuit {a32['layers'][2][1]['cells']:.3e} cells")
    p("")
    p("== lever: recursion depth (design G, adversarial, mid, z_inner = z_base = 24) ==")
    for tl, lab in ((2, 'L1 -> T1 -> T2 -> FINAL (DESIGN-BASE)'), (1, 'L1 -> T1 -> FINAL (one fewer level)')):
        for N in (8, 32):
            a = chain('adversarial', N, 'mid', z_inner=24, z_base=24, tail_levels=tl)
            p(f"{lab:40} N={N:2}: tail {fmt(tail_s(a))} s, final {a['bytes']:,} B, final circuit {a['final'][0]['cells']:.3e} cells")
    p("")
    p("== lever: final query target 258 bits (z = 32 -> 226) ==")
    for bf in (5, 6, 7):
        a = chain('adversarial', 32, 'mid', b_final=bf, final_target=226, z_inner=24, z_base=24)
        a8 = chain('adversarial', 8, 'mid', b_final=bf, final_target=226, z_inner=24, z_base=24)
        p(f"b={bf}: final {a['bytes']:,} B; FINAL N=8 {fmt(a8['stages']['FINAL'])} s, N=32 {fmt(a['stages']['FINAL'])} s")
    p("")
    p("== lever: SHA AIR zerocheck cost ((d+1) x DAG nodes); design G, adversarial, N = 32, z_inner = z_base = 24 ==")
    save = dict(AIRS['sha'])
    for deg, nodes, lab in ((21, 12718, 'today: degree 21'), (9, 12718, 'degree 9, same DAG (k = 2 digits, if rows unchanged)'), (21, 6359, 'half the DAG nodes')):
        AIRS['sha'].update(deg=deg, nodes=nodes)
        a = chain('adversarial', 32, 'mid', z_inner=24, z_base=24)
        h = chain('adversarial', 32, 'high', z_inner=24, z_base=24)
        p(f"{lab:52}: tail {fmt(tail_s(a))} s (optimistic {fmt(tail_s(h))} s)")
    AIRS['sha'].update(save)
    p("")
    p("== frontier: final proof vs tail (design G, adversarial, z_inner = z_base = 24, mid / optimistic; N = 32 and 8) ==")
    for tgt, z, bf in ((268, 32, 7), (268, 32, 6), (268, 28, 6), (268, 32, 5), (268, 24, 5), (268, 24, 6), (268, 32, 4), (268, 32, 3), (268, 0, 6), (258, 32, 7), (258, 32, 6), (258, 28, 6)):
        a = chain('adversarial', 32, 'mid', z=z, z_inner=24, z_base=24, b_final=bf, final_target=tgt - z)
        h = chain('adversarial', 32, 'high', z=z, z_inner=24, z_base=24, b_final=bf, final_target=tgt - z)
        a8 = chain('adversarial', 8, 'mid', z=z, z_inner=24, z_base=24, b_final=bf, final_target=tgt - z)
        p(f"{tgt} / z {z:2} / b {bf}: {a['bytes']:,} B   tail N=32 {fmt(tail_s(a))} s (opt. {fmt(tail_s(h))}), N=8 {fmt(tail_s(a8))} s")
    p("")
    p("== GPUs needed, design G, total after execution (mid / optimistic); z_inner = z_base = 24 ==")
    for cls in BASE:
        for tgt in (1.0, 2.0, 3.0):
            res = []
            for case in ('mid', 'high'):
                n = next((N for N in (8, 16, 24, 32, 48, 64, 96, 128, 192, 256) if chain(cls, N, case, z_inner=24, z_base=24)["stages"]['total'] <= tgt), None)
                res.append(str(n) if n else '>256')
            p(f"{cls:12} <= {tgt:.0f} s: N = {res[0]} (mid) / {res[1]} (optimistic)")
    p("")
    p("== grinding on the critical path, design G (z = 32 everywhere): mean, p99, p99.9 ==")
    a = chain('adversarial', 32, 'mid')
    nr = BASE_ROUNDS + sum(t['rounds'] for _, _, _, t in a['layers'])
    for N in (8, 16, 32):
        mean = nr * 2 ** 32 / g('grind', 'mid') / N
        p(f"N={N:2}: {nr} grinds, mean {mean:.2f} s, p99 {mean * expected_grind_tail(nr):.2f} s, p99.9 {mean * expected_grind_tail(nr, 0.999):.2f} s")
    return "\n".join(out)


if __name__ == '__main__':
    print(report())
