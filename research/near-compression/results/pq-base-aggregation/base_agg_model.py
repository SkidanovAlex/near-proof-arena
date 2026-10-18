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

    rows = []
    # ---- design T: binary tree over independent segment proofs
    n1 = node(2, BASE, W_seg, bind_regions=0)
    s_n1, w_n1 = nv_shape(n1['cells'])
    n2 = node(2, s_n1, w_n1, bind_regions=2)
    for _ in range(6):                      # N2 fixed point (children are N2 of the same shape)
        s_n2, w_n2 = nv_shape(n2['cells'])
        n2 = node(2, s_n2, w_n2, bind_regions=2)
    depth = math.ceil(lg(math.ceil(S / 2)))
    tail = [('T1 (1-ary over N2, app-table binding)', 2 ** 26.13), ('T2 (inner NV fixed point)', 2 ** 26.13),
            ('FINAL (b = 8)', 2 ** 26.13)]
    print(f"\n== Design T: S = {S} segment proofs -> N1 (2-to-1 over segments, no binding) -> "
          f"{depth} levels of N2 (2-to-1, 2 BIND regions) -> tail (3 levels)")
    print(f"   N1: 2^{lg(n1['cells']):.2f} cells, program {n1['prog']:,}, compressions {n1['comps']:,}, "
          f"interactions 2^{lg(n1['inter']):.2f}; proves at {s_n1}")
    print(f"   N2: 2^{lg(n2['cells']):.2f} cells, program {n2['prog']:,}, compressions {n2['comps']:,}, "
          f"child queries {n2['q_child']}, interactions 2^{lg(n2['inter']):.2f}; proves at {s_n2}")
    levels_T = [('N1', n1['cells'])] + [('N2', n2['cells'])] * depth + tail
    # ---- design H: one distributed (shared-transcript) segment per machine, k = 4 at level 1
    mach = 4
    mseg_cells = OPS_1PGAS_ADV / mach * MAIN_CELLS_PER_OP[cls]
    s_m = dict(BASE, log_h=26, lf=9)         # BabyBear 2-adicity: log_h + b <= 27 at c = 1
    W_m = math.ceil(mseg_cells / 2 ** 26)
    h1 = node(mach, s_m, W_m, bind_regions=0)
    s_h1, _ = nv_shape(h1['cells'])
    qm, _ = schedule(s_m)
    print(f"\n== Design H: {mach} machine-segments (P-PERF-4 inside each 8-GPU machine; 2^{lg(mseg_cells):.2f} cells, "
          f"W = {W_m} at 2^26, queries {qm}) -> H1 ({mach}-to-1, no binding) -> tail (3 levels)")
    print(f"   H1: 2^{lg(h1['cells']):.2f} cells, program {h1['prog']:,}, compressions {h1['comps']:,}, "
          f"interactions 2^{lg(h1['inter']):.2f}; proves at {s_h1}")
    levels_H = [('H1', h1['cells'])] + tail

    print("\n   critical path after execution (base GPU-bound part + levels), seconds [A: GPU rate, NV work/cell]:")
    for name, levels, gpus_first in (('T', levels_T, 1), ('H', levels_H, 8)):
        for w in NV_WORK_PER_CELL:
            tl = [t_level(c, gpus_first if i == 0 else 1, w) for i, (_, c) in enumerate(levels)]
            base_after = max(base_gpu_s / GPUS, EXEC_S) - EXEC_S
            print(f"     design {name}, {w:>2} cell-eq/NV cell: base {base_after:.2f} + {len(levels)} levels "
                  f"{sum(tl):.2f} = {base_after + sum(tl):.2f} s   (levels: "
                  + ', '.join(f"{n} {t:.3f}" for (n, _), t in zip(levels, tl)) + ")")
    # memory per node (H200 141 GB): trace + LDE (blowup c 2^b) in base field + GKR ext buffers
    for nm, cells, s in (('N1', n1['cells'], s_n1), ('N2', n2['cells'], s_n2), ('H1', h1['cells'], s_h1)):
        lde = cells * s['c'] * 2 ** s['b'] * 4
        print(f"   memory {nm}: trace {cells * 4 / 2**30:.1f} GiB, LDE {lde / 2**30:.0f} GiB (c 2^b = {s['c'] * 2 ** s['b']}) "
              f"[A: streamed/sharded if > 100 GiB]")


if __name__ == '__main__':
    report()
    print("\n######## comparison: tree nodes at the inner-NV WHIR settings (c = 15, b = 6, m = 3)")
    NODE_WHIR.update(b=6, c=15, m=3)
    report()
