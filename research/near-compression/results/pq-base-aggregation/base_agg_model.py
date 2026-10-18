#!/usr/bin/env python3
"""End-to-end cost model: 1 Pgas chunk -> segment proofs -> aggregation -> NV tail -> final.

MODEL.  Every number is labelled in the output:
  [M]  measured here or in a cited log;   [L] law fitted to NV measurements (extrapolate_nv2.py);
  [B]  bound.py / backend WHIR schedule (exact);   [A] assumption (see DESIGN-BASE.md §8).

Sources: V3-PERF-DESIGN.md (workload, per-op cells, GPU rate), V3-D3A-STUDY.md (1 Pgas = 1.22e9
adversarial ops), results/pq-recursion-nv/extrapolate_nv2.py (NV circuit laws), base_bound.py
(WHIR schedules at the U-10 settings), nv/agg.rs measurements (agg_tests: per-child program rows).

Usage: python3 -I base_agg_model.py
"""
import math
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'pq-recursion-nv'))
sys.path.insert(0, HERE)
import extrapolate_nv2 as X  # noqa: E402  (NV laws [L])
import base_bound as BB      # noqa: E402  (bound.py schedule [B])

whir_schedule = BB.ns['whir_schedule']
lg = math.log2

# ---------------------------------------------------------------- workload [A] (PERF-DESIGN)
OPS_1PGAS_ADV = 1.22e9            # adversarial pure-WASM operators in 1 Pgas (study §10.1)
MAIN_CELLS_PER_OP = dict(typical=10, mainnet=21, adversarial=38)   # PERF §4.6 (ML / SWIRL backend)
WORK_PER_OP_E10 = dict(typical=98, mainnet=207, adversarial=455)    # PERF §4.6, cell-eq per op, E = 10
E_SCALE = 1.2                     # [A] Ext12 instead of Ext10: GKR/zerocheck ext work x 12/10
GPU_RATE = 7.1e9                  # [A] work cell-eq / s / H200 at 35 % of peak INT32 (PERF §0)
GPUS = 32                         # 4 x 8 H200
EXEC_S = 1.2                      # [A] native execution of 1 Pgas with checkpoints (PERF §5.5)
NV_WORK_PER_CELL = (4, 10, 30)    # [A] work cell-eq per NV cell (degree-21 SHA AIR zerocheck); unmeasured
LEVEL_OVERHEAD_S = 0.02           # [A] per-level fixed cost (transfers, keygen-free prove setup)

# ---------------------------------------------------------------- pinned base shape [B]
BASE = dict(BB.SHAPES['base seg-v1 (c=1, b=1, m=16)'])


def schedule(s):
    sch = whir_schedule(s['log_h'], s['b'], s['k1'], s['k'], s['lf'], s.get('keep', True),
                        c=s.get('c', 15), m=s.get('m', 3))
    q = [r['q'] for r in sch]
    # leaf depth per round: codeword length c * 2^(log_h + b) (keep-domain), leaves = len / 2^k_r
    d = [math.ceil(lg(s.get('c', 15)) + s['log_h'] + s['b'] - r['k'] - 1e-9) for r in sch]
    return q, d


def child_cost(s, W):
    """NV program rows / compressions / cells to verify ONE child of WHIR shape s and stacked width W
    (marginal over the fixed part, which is paid once per child as well: preamble+GKR+DAG+stacking)."""
    q, d = schedule(s)
    c = X.nv_circuit(q, d[0], d[1] if len(d) > 1 else d[0], W)
    return dict(q=q, prog=c['prog'], comps=c['comps'], nv_rows=c['nv_rows'], sha_rows=c['sha_rows'],
                cells=c['cells'])


def node(children, s_child, W_child, bind_regions):
    """A k-ary node: k child verifiers back to back (program, jobs and transcript scale with k
    [M: agg_tests per-child rows 9.2k = 1-ary]), plus one BIND region (prog/2 rows) per bound child."""
    c1 = child_cost(s_child, W_child)
    prog = children * c1['prog']
    glue_tr = children * (c1['nv_rows'] - c1['prog'] - c1['prog'] // 2 - X.APP_ROWS // 2)
    nv_rows = prog + bind_regions * prog // 2 + glue_tr
    sha_rows = children * c1['sha_rows']
    cells = nv_rows * 73 + sha_rows * 171 + 64 * 13 + 65536 * 5
    inter = nv_rows * 55 + sha_rows * 14
    return dict(k=children, q_child=c1['q'], prog=prog, comps=children * c1['comps'], nv_rows=nv_rows,
                sha_rows=sha_rows, cells=cells, inter=inter)


NODE_WHIR = dict(b=3, c=1, m=8)   # [A] tree nodes: low blowup (LDE 8x) -- see the c=15/b=6 comparison


def nv_shape(cells, b=None, k1=1, k=4, c=None, m=None):
    """WHIR shape an NV-AIR node proves at: log_h from cells / W (W ~ 141 stacked columns [L])."""
    b = NODE_WHIR['b'] if b is None else b
    c = NODE_WHIR['c'] if c is None else c
    m = NODE_WHIR['m'] if m is None else m
    W = 141
    log_h = max(17, math.ceil(lg(cells / W)))
    lf = next(x for x in range(5, 12) if (log_h - k1 - x) % k == 0)
    return dict(log_h=log_h, b=b, k1=k1, k=k, lf=lf, c=c, m=m), W


def t_level(cells, gpus, w):
    return cells * w / (GPU_RATE * gpus) + LEVEL_OVERHEAD_S


def report():
    print("[B] pinned base segment shape:", {k: BASE[k] for k in ('log_h', 'b', 'c', 'm', 'k1', 'k', 'lf', 'W')})
    q, d = schedule(BASE)
    print(f"[B] base WHIR queries {q} (sum {sum(q)}), leaf depths {d}")
    cls = 'adversarial'
    seg_ops = 2 ** 23
    seg_cells = seg_ops * MAIN_CELLS_PER_OP[cls]
    S = math.ceil(OPS_1PGAS_ADV / seg_ops)
    work_op = WORK_PER_OP_E10[cls] * E_SCALE
    base_gpu_s = OPS_1PGAS_ADV * work_op / GPU_RATE
    print(f"\n== 1 Pgas adversarial: {OPS_1PGAS_ADV:.3g} ops [A]; segment = 2^23 ops = 2^{lg(seg_cells):.2f} main cells "
          f"(W = {math.ceil(seg_cells / 2**BASE['log_h'])} at 2^{BASE['log_h']}); S = {S} segments")
    print(f"   base work {work_op:.0f} cell-eq/op [A] -> {base_gpu_s:.0f} GPU-s -> {base_gpu_s / GPUS:.2f} s on {GPUS} H200 "
          f"(GPU-bound; overlaps execution {EXEC_S} s) => base done {max(base_gpu_s / GPUS, EXEC_S) - EXEC_S:.2f} s after execution")
    W_seg = math.ceil(seg_cells / 2 ** BASE['log_h'])
    one = child_cost(BASE, W_seg)
    print(f"[L] verifying one segment proof in NV: program {one['prog']:,} rows, {one['comps']:,} compressions, "
          f"2^{lg(one['cells']):.2f} cells (inner NV child: 2^26.1)")

    # ---------------- designs (all share the base work; they differ in how proofs are combined)
    W_g = math.ceil(OPS_1PGAS_ADV * MAIN_CELLS_PER_OP[cls] / 2 ** 26)
    s_g = dict(BASE, log_h=26, lf=9)         # BabyBear 2-adicity: log_h + b <= 27 at c = 1
    tail = [('T1', 2 ** 26.13), ('T2', 2 ** 26.13), ('FINAL', 2 ** 26.13)]   # [L] NV fixed point (recursion lane)
    designs = {}
    # G: one shared-transcript base proof over all 32 GPUs (PERF P-PERF-4), then a linear NV chain
    g1 = node(1, s_g, W_g, bind_regions=0)
    designs['G  global base proof -> L1 -> tail'] = dict(base_after=max(base_gpu_s / GPUS, EXEC_S) - EXEC_S,
                                                       levels=[('L1', g1['cells'], 8)] + [(n, c, 1) for n, c in tail])
    # T2: independent segment proofs, binary tree (N1 over 2 segments; N2 2-to-1 with 2 BIND regions)
    n1 = node(2, BASE, W_seg, bind_regions=0)
    s_n1, w_n1 = nv_shape(n1['cells'])
    n2 = node(2, s_n1, w_n1, bind_regions=2)
    for _ in range(6):
        s_n2, w_n2 = nv_shape(n2['cells'])
        n2 = node(2, s_n2, w_n2, bind_regions=2)
    d2 = math.ceil(lg(math.ceil(S / 2)))
    designs[f'T2 binary tree ({S} segments, depth 1 + {d2})'] = dict(
        base_after=max(base_gpu_s / GPUS, EXEC_S) - EXEC_S,
        levels=[('N1', n1['cells'], 1)] + [('N2', n2['cells'], 1)] * d2 + [(n, c, 1) for n, c in tail])
    # T8: wide tree: N1 over 8 segments (linear, no binding); N2 4-to-1 with a preprocessed program
    # commitment instead of BIND (linear in k; +~1.3k compressions per child [A, DESIGN §2.1 of NV])
    n1w = node(8, BASE, W_seg, bind_regions=0)
    s_n1w, w_n1w = nv_shape(n1w['cells'])
    n4 = node(4, s_n1w, w_n1w, bind_regions=0)
    for _ in range(6):
        s_n4, w_n4 = nv_shape(n4['cells'])
        n4 = node(4, s_n4, w_n4, bind_regions=0)
    n4_cells = n4['cells'] + 4 * 1300 * (43 * 171 + 8 * 73)
    d4 = math.ceil(math.log(math.ceil(S / 8), 4) - 1e-9)
    designs[f'T8 wide tree (N1 8-to-1, N2 4-to-1 preprocessed, depth 1 + {d4})'] = dict(
        base_after=max(base_gpu_s / GPUS, EXEC_S) - EXEC_S,
        levels=[('N1x8', n1w['cells'], 8)] + [('N2x4', n4_cells, 8)] * d4 + [(n, c, 1) for n, c in tail])
    # H: one contiguous range per 8-GPU machine (P-PERF-4 inside the machine), H1 4-to-1 over machines.
    # Contiguous ranges are executed in order, so ranges are sized to finish together:
    # start_g + work_g / 8 = T_f, start_g = EXEC_S * sum_{h<g} f_h
    mach = 4
    per = base_gpu_s / 8
    f = [1.0]
    for g in range(1, mach):
        f.append(f[0] * (1 - EXEC_S / per * sum(f[:g])))
    tot = sum(f)
    f = [x / tot for x in f]
    t_f = per * f[0]
    mseg_cells = OPS_1PGAS_ADV * f[0] * MAIN_CELLS_PER_OP[cls]
    s_m = dict(BASE, log_h=26, lf=9)
    W_m = math.ceil(mseg_cells / 2 ** 26)
    h1 = node(mach, s_m, W_m, bind_regions=0)
    designs[f'H  {mach} machine ranges (fractions {", ".join(f"{x:.2f}" for x in f)}) -> H1 -> tail'] = dict(
        base_after=t_f - EXEC_S, levels=[('H1', h1['cells'], 8)] + [(n, c, 1) for n, c in tail])

    print("\n   node sizes [L]: "
          f"L1 2^{lg(g1['cells']):.2f} | N1 2^{lg(n1['cells']):.2f} | N2 2^{lg(n2['cells']):.2f} (child q {n2['q_child']}) | "
          f"N1x8 2^{lg(n1w['cells']):.2f} | N2x4 2^{lg(n4_cells):.2f} | H1 2^{lg(h1['cells']):.2f}; node WHIR {NODE_WHIR}")
    print("   latency after execution = base (GPU-bound remainder) + levels on the critical path "
          "[A: 7.1 G cell-eq/s/GPU; NV work per cell 4 / 10 / 30; node GPUs as listed]:")
    for name, dsg in designs.items():
        cells_line = []
        for w in NV_WORK_PER_CELL:
            tl = [t_level(c, g, w) for (_, c, g) in dsg['levels']]
            cells_line.append(f"{dsg['base_after'] + sum(tl):.2f}")
        lv = ' + '.join(f"{n}" for n, _, _ in dsg['levels'])
        print(f"     {name:<66} base {dsg['base_after']:.2f} + [{lv}] = {' / '.join(cells_line)} s")
    s_h1, _ = nv_shape(h1['cells'])
    # memory per node (H200 141 GB): trace + LDE (blowup c 2^b) in base field + GKR ext buffers
    for nm, cells, s in (('N1', n1['cells'], s_n1), ('N2', n2['cells'], s_n2), ('N1x8', n1w['cells'], s_n1w), ('H1', h1['cells'], s_h1)):
        lde = cells * s['c'] * 2 ** s['b'] * 4
        print(f"   memory {nm}: trace {cells * 4 / 2**30:.1f} GiB, LDE {lde / 2**30:.0f} GiB (c 2^b = {s['c'] * 2 ** s['b']}) "
              f"[A: streamed/sharded if > 100 GiB]")


if __name__ == '__main__':
    report()
    print("\n######## comparison: tree nodes at the inner-NV WHIR settings (c = 15, b = 6, m = 3)")
    NODE_WHIR.update(b=6, c=15, m=3)
    report()
