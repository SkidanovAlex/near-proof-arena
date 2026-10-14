#!/usr/bin/env python3
"""End-to-end performance model for docs/zk-formal/V3-PERF-DESIGN.md (§7).

Every input is a named parameter with a provenance label:
  M  = measured (this lane's spike, or the D3a workload study)      [contended CPUs: indicative]
  MR = measured earlier in this repo (cited file)
  D  = derived (arithmetic from other parameters / public specs)
  A  = ASSUMPTION (must be measured; see the spike plan, §9)

Usage:  python3 tools/perf-design/model.py            # full report
        python3 tools/perf-design/model.py --json     # machine-readable results
"""
import json
import math
import sys
from copy import deepcopy

# ------------------------------------------------------------------------------------------
# 1. Per-class chip costs: (main base cells per row, bus fractions per row)
#    v1 = the §2 design (single-lookup timestamp range, stack temps as channels, folded gas);
#    v0 = the spike-#1 layout as built (every slot RW memory, 2-limb timestamp range).
# ------------------------------------------------------------------------------------------
CHIPS_V1 = {  # (m, f, label)
    "alu_ri":   (32, 13, "D"),  # i64 add/sub reg+imm, locals in/out
    "alu_rr":   (36, 16, "D"),
    "mul":      (49, 32, "D"),  # i64 mul, byte limbs (BabyBear)
    "divrem":   (75, 45, "D"),
    "bitwise":  (36, 16, "D"),  # and/or/xor via byte-op tables
    "shift":    (40, 18, "D"),
    "clz":      (30, 12, "D"),  # clz/ctz/popcnt
    "cmp":      (28, 12, "D"),
    "brz":      (19, 6, "D"),   # eqz+br_if / br_if on a slot
    "brcmp":    (30, 12, "D"),  # fused compare + br_if
    "conv":     (18, 8, "D"),
    "global":   (16, 7, "D"),
    "select":   (26, 10, "D"),
    "mov":      (20, 7, "D"),
    "ld_al":    (20, 12, "D"),  # aligned i32 load, temp address/result
    "ld_gen":   (37, 19, "D"),  # general load (unaligned / sub-word / i64)
    "st_gen":   (40, 22, "D"),
    "callret":  (35, 20, "D"),  # call row + return row (zero-copy frames), per call
    "memcpy16": (60, 24, "D"),  # bulk copy/fill/register copy, 16 B per row
    "prep_b":   (30, 2, "D"),   # contract preparation, per code byte (excl. SHA)
}
# Spike #4 (wasmchip run1, v1 layouts: typed operand forms, stack-temporary channels, single-lookup
# timestamps) measured per-row (main cells, bus fractions). Forms: d/a/b operand kinds L(ocal)/T(emp)/I(mm).
CHIPS_M = {
    "alu_ri":   (33, 13, "M alu_ri[LLI]"),   # LTI 33/12, TLI 28/11, L_I 32/10
    "mov":      (28, 11, "M alu_ri[TLI]"),
    "mul":      (44, 30, "M mul[TLL]"),
    "mul_TTL":  (44, 29, "D from M mul[TLL]: T read instead of L read"),
    "brz":      (21, 6, "M brz[_L]"),
    "ld_gen":   (32, 19, "M ld_gen[TT] (unaligned)"),
    "callret":  (30, 12, "M call 16/6 + ret 14/6"),
    "alu_rr":   (34, 16, "M alu_rr[LLL]"),
    "divrem":   (60, 37, "D from M divu[LLL] 65/40: T forms for a and d (-5 cells, -3 fractions)"),
}
CHIPS_V1.update(CHIPS_M)
# SHA chips measured (wasmchip sha): per compression rows of (main excl. preprocessed, fraction slots, rows)
SHA384_ROWS = [(449, 3, 41), (90, 8, 80), (98, 1, 1)]   # M: 128-B block
SHA256_ROWS = [(225, 3, 33), (46, 8, 64), (50, 1, 1)]   # M: 64-B block
# contract preparation per code byte (D): decoder 1 row/B; validator+translator 0.5 instr/B; code rows 0.2/B
PREP_ROWS_PER_BYTE = [(16, 3, 1.0), (50, 14, 0.5), (20, 2, 0.2)]
CHIPS_V0 = deepcopy(CHIPS_V1)
CHIPS_V0.update({  # spike-#1 layouts (columns and interactions as built; wasmchip report)
    "alu_ri": (36, 15, "M"), "alu_rr": (40, 19, "D"), "mul": (55, 35, "M"),
    "brz": (21, 7, "M"), "ld_al": (31, 18, "M"), "st_al": (29, 18, "M"),
})

# Spike #1 measurements (wasmchip, CPUs 9,25 under nice 19, contended): per WASM op over
# chips + memory boundary (fixed lookup/code/io tables excluded).
SPIKE1 = {
    "measured-mix loop (14 ops/iter, 3.50 ops/row)": {"main": 10.6, "frac": 5.1, "prover_weq": 65.8,
        "mix_v0": {"alu_ri": 2 / 14, "mul": 1 / 14, "brz": 1 / 14}},
    "i32.load chain (16/iter, 1.44 ops/row)": {"main": 21.3, "frac": 11.9, "prover_weq": 137.5,
        "mix_v0": {"ld_al": 16 / 26, "alu_ri": 1 / 26, "brz": 1 / 26}},
    "store/load loop (3.60 ops/row)": {"main": 9.3, "frac": 4.3, "prover_weq": 61.1,
        "mix_v0": {"alu_ri": 2 / 18, "brz": 1 / 18, "ld_al": 1 / 18, "st_al": 1 / 18}},
}
# CPU micro-benchmarks (spike #1/#2, 1 thread of a Zen 5 core, contended): rate-1/2 LDE + SHA-384
# Merkle of 2^20 x 64: 27.5 ns per trace cell (hashing 62 %); SHA-512 compression 9.0 M/s;
# SHA-256 (SHA-NI) 38 M/s; ext mul (generic schoolbook) E=8 61 ns, E=10 87 ns, E=12 200 ns;
# Plonky3 Fp8 mul 8.6 ns; logUp fraction compute (generic) E=8 532 ns, E=10 633 ns, E=12 1391 ns.
CPU = {"commit_ns_per_cell": 27.5, "frac_ns_generic_E10": 633, "p3_speedup_ext": 61.1 / 8.6}

# ------------------------------------------------------------------------------------------
# 2. Workload mixes: register-form rows per WASM op, per class
# ------------------------------------------------------------------------------------------
# measured synthetic mix (V3-D3A-STUDY §1, per-opcode aggregation of the 19,179 cases):
# local.get 22.0 %, i64.const 19.7 %, local.set 13.3 %, br 6.85 %, br_if 6.84 %, i64.add 6.82 %,
# i64.sub 6.37 %, i64.mul 6.37 %, i64.eqz 6.37 %, i32.const 1.05 %, convert 0.94 %, i32.store8 0.47 %,
# cmp ~0.9 %, global 0.39 %, call 0.27 %, load 0.06 %. Folded: local.get/const/set(95 %)/br/eqz.
MIX_MEASURED = {"alu_ri": 0.118, "alu_rr": 0.021, "mul": 0.064, "brz": 0.070, "conv": 0.0094,
                "st_gen": 0.0047, "ld_gen": 0.0006, "cmp": 0.004, "global": 0.0039,
                "callret": 0.0027, "mov": 0.007}
# mainnet-like (ASSUMPTION A: Rust/near-sdk contracts; loads+stores ~22 %, locals ~30 %, consts ~12 %)
MIX_MAINNET = {"alu_ri": 0.08, "alu_rr": 0.06, "bitwise": 0.03, "shift": 0.015, "mul": 0.012,
               "divrem": 0.004, "cmp": 0.03, "brz": 0.04, "brcmp": 0.03, "ld_gen": 0.13,
               "st_gen": 0.09, "callret": 0.03, "global": 0.01, "select": 0.01, "conv": 0.02,
               "mov": 0.04}
# adversarial candidates: rows per *gas unit* (regular_op_cost = 822,756 gas). All non-bulk WASM
# operators cost one unit; a function's closing `end` is free; read_register costs 98,562 gas/B;
# contract loading 1,089,295 gas/B (spec/lean/v3/NearSpecV3/Wasm/Machine.lean).
RD_GAS_PER_BYTE = 98562 + 2723772      # spec: read_register_byte + write_memory_byte (read_register -> memory)
LOAD_GAS_PER_BYTE = 1089295             # spec: contract_loading_bytes
ADVERSARIAL = {
    "unaligned i32.load chain (1 op/row) [M]":        {"ld_gen": 1.0},
    "call of an empty function [M]":                  {"callret": 1.0},
    "local.get b; i64.div_u chain (2 ops/row) [M]":   {"divrem": 0.5},
    "local.get b; i64.mul chain (2 ops/row) [M]":     {"mul_TTL": 0.5},
    "i64.popcnt chain (1 op/row) [D]":                {"clz": 1.0},
    "memory.copy (1 gas unit/B) [M]":                 {"memcpy16": 1 / 16},
    "read_register -> memory (2.82 Mgas/B) [M]":      {"memcpy16": 822756 / RD_GAS_PER_BYTE / 16},
    "distinct-contract loading [M SHA-256 + D PREP]": {"_load_bytes": 822756 / LOAD_GAS_PER_BYTE},
}

# ------------------------------------------------------------------------------------------
# 3. Parameters
# ------------------------------------------------------------------------------------------
P = {
    # workload
    "gas": (1e15, "spec: chunk gas limit"),
    "regular_op": (822756, "spec: regular_op_cost"),
    "wasm_share_measured": (0.034, "M: WASM-operator share of FC gas, corpora"),
    "wasm_share_mainnet": (0.30, "A: mainnet-like WASM-operator gas share"),
    "host_celleq_per_gas": (6e-5, "D: §3 host table, ~3e-5 committed cells/gas x 2 work-eq"),
    "witness_bytes": (8e6, "A: state witness of a 1 Pgas chunk"),
    "witness_celleq_per_byte": (1.35e3, "MR/D: 0.9k cells/B (D3A §10.2) x 1.5 work-eq"),
    "sha256_cells_per_byte": (190.0, "MR: L5 SHA-256 12k cells / 64 B"),
    # proof system
    "E": (10, "D: PQ extension degree (|K| >= 2^290, D3A §11.2)"),
    "d_quot": (2, "D: quotient chunks at constraint degree 3 (rate-1/2 domain)"),
    "rbr_bits": (260, "D: per-round PQ target (t^2 eps_rbr, t = 2^64; D3A §11.2)"),
    "z_inner": (16, "A: grinding bits on inner layers (Grover: z/2 PQ bits)"),
    "log_blowup0": (1, "design: base layer rate 1/2"),
    "log_blowup1": (2, "design: compression layer rate 1/4"),
    "log_blowup2": (4, "design: L3 (the layer the final layer verifies) rate; higher blowup = fewer queries for the final verifier"),
    "log_blowup_f": (5, "design: final layer rate 1/32 (size vs latency; 1/64 = 740 KB but +0.14 s)"),
    "sha384_cells": (0, "M: 0 = from the measured SHA-512-family layout (SHA384_ROWS; ~38k cell-eq at E=10); >0 overrides"),
    "prep_early": (1, "design lever P-PERF-8: contract preparation + code hash proved in a separate sub-proof from chunk start (code known before execution)"),
    "tail_all_gpus": (1, "design: 1 = L2/L3 distributed over all GPUs (P-PERF-4; never transmitted); the final layer stays one FRI on one node"),
    "rec_field_cells_per_value": (30, "A: in-AIR DEEP/FRI field work per opened value"),
    "table_log_h": (24, "design: per-GPU table height (segments concatenated per chip)"),
    # GPU (H200 = GH100: 132 SMs x 64 INT32 lanes x 1.98 GHz)
    "gpu_int32": (16.7e12, "D: public GH100 specs"),
    "eff": (0.35, "A: sustained fraction of peak INT32 across all kernels"),
    "sha512_int_ops": (2750, "A/D: hashcat SHA-512 on RTX 4090 (~7.5 GH/s at 20.6 T INT32/s), recollection"),
    "ntt_int_ops_per_cell": (306, "D: 34 butterflies x 9 ops (iDFT n + DFT 2n)"),
    "constraints_per_cell": (0.7, "M(spike)/A"),
    "hbm_gb": (141, "spec: H200"),
    "gpus_per_node": (8, "hardware"),
    # execution
    "exec_s_per_pgas": (1.0, "A: NEAR gas ~ time calibration (1 Tgas ~ 1 ms) on validator HW"),
    "exec_slowdown": (1.2, "A: native run with checkpoint recording"),
    "seg_tail_s": (0.05, "A: last segment's trace gen + main commit after execution ends"),
    "sync_s": (0.03, "A: per-layer transcript sync / roots / launch overhead"),
}
def v(name, p=None):
    return (p or P)[name][0]

# ------------------------------------------------------------------------------------------
# 4. Cost primitives
# ------------------------------------------------------------------------------------------
def ext_mul_ops(p):
    E = v("E", p)
    return E * E * 6 * 0.75            # D: schoolbook-ish, Montgomery mult + add, 25 % Karatsuba saving

def int_ops_per_cell(p, lb=None):
    """(int32 ops per committed cell, of which phase A) at rate 2^-lb (default: base layer)."""
    E = v("E", p)
    lb = v("log_blowup0", p) if lb is None else lb
    B = 2 ** lb
    sha = (4 * B / 128) * 1.05 * v("sha512_int_ops", p)    # B LDE values x 4 B per cell; +5 % nodes
    ntt = v("ntt_int_ops_per_cell", p) * (1 + B) / 3        # iDFT n + DFT B*n (calibrated at B = 2)
    deep = B * E * 6
    ev = 2 * v("constraints_per_cell", p) * (E * 6 + 10)    # quotient domain 2n (degree 3)
    return ntt + sha + deep + ev, ntt + sha

def frac_ops(p, backend):
    """int32 ops per bus fraction (compute only; committed aux cells counted as cells)."""
    E = v("E", p)
    fp = 7 * E * 6
    if backend == "U-logUp":
        return fp + 3 * ext_mul_ops(p) + 2 * (fp + 2 * ext_mul_ops(p))
    return fp + 28 * ext_mul_ops(p)    # GKR (univariate or multilinear)

def row_cost(p, backend, m, f):
    """(committed base cells, int32 ops) for one chip row."""
    E = v("E", p)
    cell, _ = int_ops_per_cell(p)
    if backend == "U-logUp":
        cells = m + E * (math.ceil(f / 2) + 1) + E * v("d_quot", p)
    elif backend == "U-GKR":
        cells = m + E * v("d_quot", p)
    else:  # multilinear: no quotient, no aux; zerocheck work ~ per-row eq products
        cells = m
    ops = cells * cell + f * frac_ops(p, backend)
    if backend == "ML":
        ops += 2 * ext_mul_ops(p) * 3
    return cells, ops

def per_op(p, backend, mix, chips):
    cells = ops = rows = fr = main = 0.0
    for cls, r in mix.items():
        if cls == "_load_bytes":   # r code bytes: SHA-256 code hash (measured layout) + PREP (D)
            for (m, f, n) in [(m, f, n / 64) for (m, f, n) in SHA256_ROWS] + PREP_ROWS_PER_BYTE:
                c, o = row_cost(p, backend, m, f)
                cells += r * n * c
                ops += r * n * o
                main += r * n * m
                fr += r * n * f
                rows += r * n
            continue
        m, f, _ = chips[cls]
        c, o = row_cost(p, backend, m, f)
        cells += r * c
        ops += r * o
        rows += r
        fr += r * f
        main += r * m
    return {"rows": rows, "main": main, "frac": fr, "cells": cells, "ops": ops,
            "celleq": ops / int_ops_per_cell(p)[0]}

# ------------------------------------------------------------------------------------------
# 5. Recursion / compression chain (shared-transcript distributed base proof, §5)
# ------------------------------------------------------------------------------------------
def queries(p, log_blowup, regime="best"):
    rho = 2.0 ** -log_blowup
    udr = -math.log2((1 + rho) / 2)
    joh = 0.5 * log_blowup - 0.1
    b = {"udr": udr, "johnson": joh, "best": max(udr, joh)}[regime]
    return math.ceil((v("rbr_bits", p) - v("z_inner", p) / 2) / b)

def sha384_celleq(p):
    """work cell-eq of one in-circuit SHA-384 compression (measured layout, E and rate of p)."""
    if v("sha384_cells", p) > 0:
        return v("sha384_cells", p)
    cell = int_ops_per_cell(p)[0]
    return sum(n * row_cost(p, "U-logUp", m, f)[1] for (m, f, n) in SHA384_ROWS) / cell

def verifier_cells(p, q, n_trees, log_lde, c_tot, E, n_parts=1):
    """in-AIR cells to verify one proof whose `n_trees` commitments are global trees over
    `n_parts` GPUs: leaf_i = H(d_1,i || ... || d_N,i) with d_g,i = H(row of GPU g at i)
    (row-digest all-to-all, §5.2), so each query opens one path per tree."""
    cap = math.log2(q)
    path = max(0.0, log_lde - cap)
    leaf = c_tot * 4 / 128 + n_trees * n_parts * (1 + 48 / 128)
    fri_layers = max(1, math.ceil((log_lde - 6) / 4))     # arity 16 down to 2^6
    fri = sum(16 * E * 4 / 128 + max(0, log_lde - 4 * (i + 1) - cap) for i in range(fri_layers))
    compr = q * (n_trees * path + leaf + fri)
    return compr * sha384_celleq(p) + q * c_tot * v("rec_field_cells_per_value", p), compr

def size_final(p, logn, logb, weq=400, trees=3, D=48, E=40, ar=4, flog=6):
    """final-layer bytes (tools/d3a-study/pqsize.py formula, SHA-384, arity 16)."""
    bq = 0.5 * logb - 0.1
    q = math.ceil((v("rbr_bits", p) - 32 / 2) / bq)
    sh = math.log2(q)
    L = logn + logb
    per = 4 * weq + trees * D * max(0, L - sh)
    d = L
    fri = 0
    layers = 0
    while d - ar >= flog + logb:
        d -= ar
        layers += 1
        fri += (2 ** ar) * E + D * max(0, d - sh)
    per += fri
    fixed = D * (trees + layers) + E * 2 ** flog + E * 2 * weq
    return q, q * per + fixed

# ------------------------------------------------------------------------------------------
# 6. Scenario evaluation
# ------------------------------------------------------------------------------------------
def scenario(p, name, backend, n_gpu, chips=CHIPS_V1, cand=None):
    if name == "adversarial" and cand is None:
        rs = [scenario(p, name, backend, n_gpu, chips, c) for c in ADVERSARIAL]
        return max(rs, key=lambda r: r["after_exec"])
    gas = v("gas", p)
    units = gas / v("regular_op", p)
    if name == "typical-measured":
        ops_wasm = units * v("wasm_share_measured", p)
        mix = MIX_MEASURED
        host_gas = gas * (1 - v("wasm_share_measured", p))
    elif name == "mainnet-like":
        ops_wasm = units * v("wasm_share_mainnet", p)
        mix = MIX_MAINNET
        host_gas = gas * (1 - v("wasm_share_mainnet", p))
    else:
        worst = (cand, None, ADVERSARIAL[cand])
        ops_wasm = units
        mix = worst[2]
        host_gas = 0.0
    po = per_op(p, backend, mix, chips)
    cell_ops, a_ops = int_ops_per_cell(p)
    ops_base = ops_wasm * po["ops"]
    ops_host = host_gas * v("host_celleq_per_gas", p) * cell_ops
    ops_wit = v("witness_bytes", p) * v("witness_celleq_per_byte", p) * cell_ops
    total_ops = ops_base + ops_host + ops_wit
    cells_total = ops_wasm * po["cells"] + (ops_host + ops_wit) / cell_ops
    R = v("gpu_int32", p) * v("eff", p)                    # int32 ops/s/GPU, sustained
    t_base = total_ops / (n_gpu * R)
    # phase A (main LDE + Merkle) streams during execution; the rest needs global challenges
    frac_a = (ops_wasm * po["main"] * a_ops + (ops_host + ops_wit) * a_ops / cell_ops) / total_ops
    t_exec = v("exec_s_per_pgas", p) * gas / 1e15 * v("exec_slowdown", p)
    t_a = frac_a * t_base
    t_b = (1 - frac_a) * t_base
    # compression chain
    E = v("E", p)
    h = v("table_log_h", p)
    trees0 = {"U-logUp": 3, "U-GKR": 2, "ML": 2}[backend]
    q0 = queries(p, v("log_blowup0", p))
    c_tot0 = cells_total / 2 ** h
    # each layer proves the verifier of the previous layer's proof
    rc1, cmp1 = verifier_cells(p, q0, trees0, h + v("log_blowup0", p), c_tot0, E, n_gpu)   # L1 circuit
    c1 = int_ops_per_cell(p, v("log_blowup1", p))[0]
    c2 = int_ops_per_cell(p, v("log_blowup2", p))[0]
    cf = int_ops_per_cell(p, v("log_blowup_f", p))[0]
    node = min(n_gpu, v("gpus_per_node", p))       # the final layer: one FRI instance, one node
    mid = n_gpu if v("tail_all_gpus", p) else node  # L2/L3 (not transmitted) may be distributed
    t_l1 = rc1 * 1.2 * c1 / (n_gpu * R) + v("sync_s", p)
    q1 = queries(p, v("log_blowup1", p))
    rc2, cmp2 = verifier_cells(p, q1, 3, math.log2(rc1 / (400 * n_gpu)) + v("log_blowup1", p), 400 * n_gpu, E, n_gpu)  # L2 circuit
    t_l2 = rc2 * 1.2 * c1 / (mid * R) + v("sync_s", p)
    q2 = queries(p, v("log_blowup1", p))
    rc3, _ = verifier_cells(p, q2, 3, math.log2(rc2 / 400) + v("log_blowup1", p), 400, E)   # L3 circuit
    t_l3 = rc3 * 1.2 * c2 / (mid * R) + v("sync_s", p)
    q3 = queries(p, v("log_blowup2", p))
    rcf, _ = verifier_cells(p, q3, 3, math.log2(rc3 / 400) + v("log_blowup2", p), 400, E)   # final circuit
    hf = max(18, math.ceil(math.log2(rcf / 400)))
    t_fin = rcf * 1.2 * cf / (node * R) + v("sync_s", p)
    qf, size = size_final(p, hf, v("log_blowup_f", p))
    rec_ops = rc1 * 1.2 * c1 + rc2 * 1.2 * c1 + rc3 * 1.2 * c2 + rcf * 1.2 * cf
    tail = t_l1 + t_l2 + t_l3 + t_fin
    t_commit_done = max(t_exec + v("seg_tail_s", p), t_a + v("sync_s", p))
    latency = t_commit_done + t_b + v("sync_s", p) + tail
    if name == "adversarial" and worst[0].startswith("distinct-contract") and v("prep_early", p):
        # PREP + code hash: own transcript, starts at t = 0 (all executed code is known at chunk
        # start); the main proof then holds only the witness/plumbing work
        main_ops = ops_host + ops_wit
        t_main_b = main_ops / (n_gpu * R) * (1 - a_ops / cell_ops)
        t_all = (ops_base + main_ops) / (n_gpu * R) + v("sync_s", p)
        latency = max(t_exec + v("seg_tail_s", p) + t_main_b + v("sync_s", p), t_all) + tail
        t_a, t_b = (ops_base + main_ops) / (n_gpu * R), t_main_b
    # memory per GPU: trace (4 B) + LDE (8 B) per committed cell, GKR layers (E*4 B per fraction)
    frac_total = ops_wasm * po["frac"]
    mem = cells_total / n_gpu * 12 + (frac_total / n_gpu * E * 4 * 2 if backend != "U-logUp" else 0)
    return {
        "scenario": name, "backend": backend, "gpus": n_gpu,
        "wasm_ops": ops_wasm, "rows_per_op": po["rows"], "main_per_op": po["main"],
        "frac_per_op": po["frac"], "cells_per_op": po["cells"], "celleq_per_op": po["celleq"],
        "worst_kind": (worst[0] if name == "adversarial" else None),
        "cells_total": cells_total, "ops_total": total_ops,
        "gpu_s": total_ops / R, "rec_gpu_s": rec_ops / R, "rec_share": rec_ops / total_ops,
        "t_exec": t_exec, "t_A": t_a, "t_B": t_b, "t_L1": t_l1, "t_L2": t_l2, "t_L3": t_l3,
        "t_final": t_fin, "latency": latency, "after_exec": latency - t_exec,
        "q0": q0, "q1": q1, "qf": qf, "proof_bytes": size, "mem_gb_per_gpu": mem / 1e9,
        "celleq_per_s_gpu": R / cell_ops,
    }

def required(p, backend, n_gpu, budget_after_exec=1.0):
    """GPU sustained efficiency needed so the adversarial chunk lands <= budget after execution."""
    lo, hi = 0.01, 5.0
    for _ in range(60):
        mid = (lo + hi) / 2
        q = deepcopy(p)
        q["eff"] = (mid, "solve")
        if scenario(q, "adversarial", backend, n_gpu)["after_exec"] <= budget_after_exec:
            hi = mid
        else:
            lo = mid
    q = deepcopy(p)
    q["eff"] = (hi, "solve")
    r = scenario(q, "adversarial", backend, n_gpu)
    return hi, r["celleq_per_s_gpu"], r

# ------------------------------------------------------------------------------------------
# 7. Report
# ------------------------------------------------------------------------------------------
def fmt(x, n=2):
    if x == 0:
        return "0"
    e = math.floor(math.log10(abs(x)))
    if -2 <= e <= 4:
        return f"{x:.{max(0, n - 1 - e) if e < n else 0}f}"
    return f"{x:.{n - 1}e}"

SENS = [  # (param, low, high)
    ("eff", 0.2, 0.6), ("E", 8, 12), ("sha512_int_ops", 2000, 5500), ("sha384_cells", 20000, 50000), ("table_log_h", 23, 25), ("tail_all_gpus", 0, 1), ("prep_early", 0, 1),
    ("exec_slowdown", 1.0, 2.0), ("rbr_bits", 200, 290), ("z_inner", 0, 32),
    ("ntt_int_ops_per_cell", 200, 450), ("log_blowup0", 1, 2), ("witness_bytes", 4e6, 16e6),
]

def main():
    out = []
    as_json = "--json" in sys.argv
    if not as_json:
        print("Per-class chip costs (v1 design; m = main cells/row, f = bus fractions/row)")
        cell, a = int_ops_per_cell(P)
        print(f"  int32 ops per committed cell {cell:.0f} (phase-A part {a:.0f}); per fraction: "
              f"U-logUp {frac_ops(P, 'U-logUp'):.0f} (+E/2 committed cells), GKR {frac_ops(P, 'U-GKR'):.0f}")
        print(f"  {'class':10s} {'m':>4s} {'f':>4s} | committed cells/row: U-logUp  U-GKR  ML | work cell-eq/row: U-logUp U-GKR ML")
        for c, (m, f, lab) in CHIPS_V1.items():
            r = [row_cost(P, b, m, f) for b in ("U-logUp", "U-GKR", "ML")]
            print(f"  {c:10s} {m:4d} {f:4d} | {r[0][0]:22.0f} {r[1][0]:6.0f} {r[2][0]:4.0f} | "
                  f"{r[0][1]/cell:16.0f} {r[1][1]/cell:5.0f} {r[2][1]/cell:4.0f}   [{lab}]")
        print("\nAdversarial candidates (per gas unit = 822,756 gas), backend U-logUp, v1 chips:")
        for adv, mx in ADVERSARIAL.items():
            r = per_op(P, "U-logUp", mx, CHIPS_V1)
            print(f"  {adv:40s} committed {r['cells']:6.0f}  work cell-eq {r['celleq']:6.0f}")
    for sc in ("typical-measured", "mainnet-like", "adversarial"):
        for be in ("U-logUp", "U-GKR", "ML"):
            for n in (16, 32):
                out.append(scenario(P, sc, be, n))
    if as_json:
        print(json.dumps(out, indent=1))
        return
    print("\nEnd-to-end at 1 Pgas (latency from execution start; 'post' = after execution ends)")
    hdr = (f"  {'scenario':16s} {'backend':8s} {'GPUs':>4s} {'ops':>8s} {'cells/op':>8s} {'celleq/op':>9s} "
           f"{'GPU-s':>7s} {'rec%':>5s} {'exec':>5s} {'A':>5s} {'B':>5s} {'tail':>5s} {'latency':>7s} "
           f"{'post':>5s} {'q0':>4s} {'proof':>7s} {'GB/GPU':>6s}")
    print(hdr)
    for r in out:
        tail = r["t_L1"] + r["t_L2"] + r["t_L3"] + r["t_final"]
        print(f"  {r['scenario']:16s} {r['backend']:8s} {r['gpus']:4d} {fmt(r['wasm_ops']):>8s} "
              f"{r['cells_per_op']:8.0f} {r['celleq_per_op']:9.0f} {r['gpu_s']:7.1f} {100*r['rec_share']:5.1f} "
              f"{r['t_exec']:5.2f} {r['t_A']:5.2f} {r['t_B']:5.2f} {tail:5.2f} {r['latency']:7.2f} "
              f"{r['after_exec']:5.2f} {r['q0']:4d} {r['proof_bytes']/1e3:6.0f}K {r['mem_gb_per_gpu']:6.0f}")
    worst = [r for r in out if r["scenario"] == "adversarial"][0]
    print(f"\n  adversarial worst kind: {worst['worst_kind']}")
    print("\nAdversarial candidates at 1 Pgas, U-logUp, 32 H200 (latency after execution, s):")
    for c in ADVERSARIAL:
        r = scenario(P, "adversarial", "U-logUp", 32, cand=c)
        print(f"  {c:50s} cell-eq/unit {r['celleq_per_op']:5.0f}  GPU-s {r['gpu_s']:5.1f}  post-exec {r['after_exec']:5.2f}  (B {r['t_B']:.2f}; L1 {r['t_L1']:.2f} L2 {r['t_L2']:.2f} L3 {r['t_L3']:.2f} final {r['t_final']:.2f})")
    print("\nRequired sustained GPU efficiency for the adversarial 1 Pgas chunk (U-logUp backend)")
    for n in (16, 32):
        for budget in (1.0, 2.0):
            e, cps, r = required(P, "U-logUp", n, budget)
            print(f"  {n} H200, proof <= {budget:.0f} s after execution ends: eff >= {e:.2f} of peak INT32 "
                  f"= {cps/1e9:.1f} G cell-eq/s/GPU = {cps/worst['celleq_per_op']/1e6:.0f} M worst-case ops/s/GPU; "
                  f"total latency {r['latency']:.2f} s")
    print("\nSpike #1 cross-check (v0 layouts as built; model per-op vs measured):")
    for name, d in SPIKE1.items():
        r = per_op(P, "U-logUp", d["mix_v0"], CHIPS_V0)
        print(f"  {name:48s} measured main {d['main']:5.1f} frac {d['frac']:5.1f} | model main {r['main']:5.1f} frac {r['frac']:5.1f}")
    fr_opt = CPU["frac_ns_generic_E10"] / CPU["p3_speedup_ext"]
    print(f"  CPU fraction/cell work ratio (E=10, Plonky3-grade ext arithmetic, D): {fr_opt / CPU['commit_ns_per_cell']:.1f} "
          f"+ 5 committed aux cells = {fr_opt / CPU['commit_ns_per_cell'] + 5:.1f} cell-eq per fraction "
          f"(model GPU: {frac_ops(P, 'U-logUp') / int_ops_per_cell(P)[0] + 5:.1f})")
    print("\nSensitivity: adversarial, U-logUp, 32 H200, latency after execution (s)")
    base = scenario(P, "adversarial", "U-logUp", 32)["after_exec"]
    rows = []
    for name, lo, hi in SENS:
        res = []
        for val in (lo, hi):
            q = deepcopy(P)
            q[name] = (val, "sens")
            res.append(scenario(q, "adversarial", "U-logUp", 32)["after_exec"])
        rows.append((abs(res[1] - res[0]), name, lo, hi, res))
    rows.sort(reverse=True)
    print(f"  base {base:.2f} s")
    for sw, name, lo, hi, res in rows:
        print(f"  {name:22s} {lo:>8} -> {res[0]:5.2f} s | {hi:>8} -> {res[1]:5.2f} s | swing {sw:5.2f}")
    print("\nParameters:")
    for k, (val, lab) in P.items():
        print(f"  {k:28s} {val!s:>10}   {lab}")

if __name__ == "__main__":
    main()
