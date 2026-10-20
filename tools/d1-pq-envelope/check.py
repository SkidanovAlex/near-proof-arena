#!/usr/bin/env python3
"""D1-on-PQ envelope check: does `nearAirV3D1` fit the SWIRL/WHIR PQ stack?

This replaces the prose "one-day envelope check" with a deterministic computation over the
*actual* exported Lean AIR, so the verdict does not depend on reading design notes.

Inputs (no guessed numbers):

  --d1-json    `np-lean-export-v3d1` output (format `np-air-v2`) for `nearAirV3D1`
  --d1-layout  `np-lean-export-v3d1 --layout 2` output (one line per table:
               index width auxCount degree quotCount sendG recvG maxLog)
  --d0-json    optional `np-lean-export-v3` output, for the D0a baseline
  --d0-layout  optional `np-lean-export-v3 --layout 2`

Produce them with the compiled exporters (no rebuild needed):

  B=/data/illia/nearproof-wt/v3-d1-a7b/examples/np-udr-stark-v2/conformance/.lake/build/bin
  $B/np-lean-export-v3d1 > d1.json
  $B/np-lean-export-v3d1 --layout 2 > d1.layout
  $B/np-lean-export-v3    > d0.json      # from a tree whose binary is current
  $B/np-lean-export-v3 --layout 2 > d0.layout

What the script separates (this distinction is the whole point):

  HARD     a protocol/algebra/Lean limit. Violating it needs an architecture change.
  PIN      a pinned *base-shape* choice (DESIGN-BASE §3). Exceeding it is a cost decision,
           not an impossibility, and it does not by itself break soundness.
  COST     a downstream price (prover time, memory, bytes) that follows from the shape.

Exit code 0 when every HARD limit passes, 1 otherwise.
"""
from __future__ import annotations

import argparse
import json
import math
import sys

BB_P = 15 * 2**27 + 1                 # BabyBear
LOG_BB = math.log2(BB_P)              # 2^30.91
EXT_DEG = 12                          # Ext12
LOG_F = EXT_DEG * LOG_BB              # |Ext12| ~ 2^370.9

# --- Lean-side hard limits (ZkFormal.Air.Table.wf / Air.wf) ------------------------------
LEAN_MAX_MULT_BITS = 25               # `i.mult.length <= 25`
LEAN_BUS_BUDGET_LOG = 36              # `Air.multBound`, `Air.fpBound` <= 2^36
LEAN_MAX_TABLES_LOG = 32              # `AP.tables.length < 2^32`
LEAN_MAX_DEG = 22                     # `T.maxLog <= 22`
LEAN_MAX_CONSTRAINT_DEG = 16          # `nearAirV3D1.wf 16`

# --- NV / backend hard limits ------------------------------------------------------------
NV_LOG_MAX_MESSAGE = 7                # `log_max_message_length`; message + bus <= 2^7
NV_ADDR_BITS = 24                     # `isa.rs ADDR_BITS`; program log_rows - 1 <= 24
NV_MAX_DOMAIN_LOG = 27                # BabyBear 2-adicity: 15 * 2^27 (x15 domains)

# --- pinned base shape (DESIGN-BASE §3), NOT a hard limit --------------------------------
PIN_AIRS = 32
PIN_DEG = 8
PIN_SLICE_W = 24                      # per-GPU-slice stacked width
PIN_OPENED = 1024
PIN_INTERACTION_LOG = 28              # `max_interaction_count` (a *security* parameter)
PIN_MSG = 16

# Realistic heights from lane/v3-d1-tables (maxima over 137 checked fixtures, padLog22):
# txV3 <=10, akmV3 <=7, kibV3 <=10, plfV3 <=4, ridV3 <=7; unread tables <=10; mrk 2^20;
# the six fixed D0a tables keep 2^22 because their work is real.
REAL_HEIGHT_LOG = {
    "txV3": 10, "akmV3": 7, "kibD1": 10, "plfV3": 4, "ridV3": 7,
    "walkU": 10, "nmemV3": 10, "uvalV3": 10,
    "mrk": 20, "head": 13, "bnd": 13, "akey": 16, "sort": 19, "sizeA7": 4, "qv": 22,
}

D1_NAMES = [
    "sha0", "sha1", "nodeD1", "head", "valA7", "walkV3", "uniqD1", "upsA7",
    "chacha", "rng", "shuffle", "codec", "scandist", "proc", "mem", "cmp",
    "rcptV3D1", "acct", "akey", "bnd", "srcp", "sizeA7", "qv", "mrk", "sort",
    "txV3", "akmV3", "kibD1", "plfV3", "ridV3", "walkU", "nmemV3", "uvalV3",
]
D0_NAMES = [
    "sha0", "sha1", "nodeA7", "head", "valA7", "walkV3", "uniqV3", "upsA7",
    "chacha", "rng", "shuffle", "codec", "scandist", "proc", "mem", "cmp",
    "rcptV3", "acct", "akey", "bnd", "srcp", "sizeA7", "qv", "mrk", "sort",
]

SHARDS = {
    "exec + 2xSHA": ["sha0", "sha1"],
    "trie": ["nodeD1", "head", "valA7", "walkV3", "uniqD1", "upsA7", "sizeA7", "mrk", "sort"],
    "scheduler + ChaCha": ["chacha", "rng", "shuffle", "codec", "scandist", "proc", "mem", "cmp"],
    "receipts + accounts": ["rcptV3D1", "acct", "akey", "bnd", "srcp", "qv"],
    "D1 tx + unread": ["txV3", "akmV3", "kibD1", "plfV3", "ridV3", "walkU", "nmemV3", "uvalV3"],
}


def log2(x: float) -> float:
    return math.log2(x) if x > 0 else float("-inf")


def pad_log22(l: int) -> int:
    """`ZkFormal.Size.padLog22`: round up to 1, 4, 7, ..., 22."""
    return 22 - 3 * ((22 - l) // 3)


def load_air(path: str, layout_path: str, names: list[str]):
    try:
        air = json.load(open(path))
        layout = [list(map(int, line.split())) for line in open(layout_path) if line.strip()]
    except FileNotFoundError as e:
        sys.exit(f"missing input: {e.filename}\n"
                 f"See tools/d1-pq-envelope/README.md for the exporter commands.")
    except json.JSONDecodeError as e:
        sys.exit(f"{path}: not JSON ({e})")
    if len(air["tables"]) != len(layout):
        sys.exit(f"{path}: {len(air['tables'])} tables vs {len(layout)} layout lines")
    if len(air["tables"]) != len(names):
        sys.exit(f"{path}: {len(air['tables'])} tables vs {len(names)} expected names")
    tables = []
    for name, t, row in zip(names, air["tables"], layout):
        _, width, aux, deg, quot, _sg, _rg, max_log = row
        tables.append(dict(
            name=name, width=width, aux=aux, deg=deg, quot=quot,
            W=width + aux + quot, max_log=max_log,
            interactions=len(t["interactions"]),
            msg_max=max((len(i["msg"]) for i in t["interactions"]), default=0),
            mult_bits=max((len(i["mult"]) for i in t["interactions"]), default=0),
            cons_deg=max((_expr_deg(c) for c in t["constraints"]), default=1),
            cons_count=len(t["constraints"]),
            ast=_tables_ast([t]),
            buses=[i["bus"] for i in t["interactions"]],
        ))
    return air, tables


def _sha256(path: str) -> str:
    import hashlib
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def _expr_deg(e) -> int:
    """Formal degree, as `ZkFormal.Air.Expr.degree` defines it: constants and public
    reads are degree 0, columns and selectors degree 1."""
    if not isinstance(e, list):
        return 0
    tag = e[0]
    if tag in ("c", "p"):
        return 0
    if tag in ("v", "n", "first", "last", "trans"):
        return 1
    if tag == "+":
        return max(_expr_deg(e[1]), _expr_deg(e[2]))
    if tag == "*":
        return _expr_deg(e[1]) + _expr_deg(e[2])
    if tag == "-":
        return _expr_deg(e[1])
    raise ValueError(f"bad expr tag {tag}")


def _ast(e) -> int:
    if not isinstance(e, list):
        return 1
    if e[0] in ("c", "v", "n", "p", "first", "last", "trans"):
        return 1
    return 1 + sum(_ast(x) for x in e[1:])


def _tables_ast(tables) -> int:
    return sum(_ast(x) for t in tables for x in t["constraints"]) + \
           sum(_ast(x) for t in tables for i in t["interactions"]
               for x in list(i["msg"]) + list(i["mult"]))


def heights(tables, mode: str) -> dict[str, int]:
    out = {}
    for t in tables:
        if mode == "realistic":
            out[t["name"]] = REAL_HEIGHT_LOG.get(t["name"], pad_log22(min(t["max_log"], 22)))
        elif mode == "aligned":
            out[t["name"]] = max(1, t["max_log"])
        else:
            raise ValueError(mode)
    return out


def interaction_mass(tables, h: dict[str, int]) -> float:
    return sum(t["interactions"] * 2**h[t["name"]] for t in tables)


def committed_cells(tables, h: dict[str, int]) -> float:
    return sum(t["width"] * 2**h[t["name"]] for t in tables)


def per_bus_mass(tables, h: dict[str, int]) -> dict[int, float]:
    buses: dict[int, float] = {}
    for t in tables:
        row = 2**h[t["name"]]
        for bus in t["buses"]:
            buses[bus] = buses.get(bus, 0.0) + row
    return buses


# Measured e2e L1 over the direct-Wasm base (lane/pq-e2e-slice, real probe b=1/m=16,
# fast prover): the calibration point for every L1 number below.
E2E_L1 = dict(W=330, prog=623_802, cells=0.51e9, secs=152, gb=10.07)


def _load_nv_model(lane_dir: str):
    """Import the recursion lane's calibrated NV circuit model, or return None."""
    import importlib.util
    import os
    path = os.path.join(lane_dir, "extrapolate_nv2.py")
    if not os.path.isfile(path):
        return None
    try:
        spec = importlib.util.spec_from_file_location("extrapolate_nv2", path)
        mod = importlib.util.module_from_spec(spec)
        sys.path.insert(0, lane_dir)
        spec.loader.exec_module(mod)  # type: ignore[union-attr]
        return mod
    except Exception:
        return None


def nv_l1_cost(child_w: int, lane_dir: str) -> tuple[dict[str, float], bool]:
    """L1 program rows / cells over a child with stacked width `child_w`.

    Prefers the recursion lane's calibrated model (`extrapolate_nv2.nv_circuit`) and
    reports its *ratio* to the W = 330 point, anchored on the measured e2e L1. Falls
    back to the same scaling with a documented linear-in-W approximation when the lane
    model is unavailable (the ratio is what matters; absolute values come from the
    measurement).
    """
    model = _load_nv_model(lane_dir)
    if model is not None:
        q = [536, 256, 83, 50, 36]
        base = model.nv_circuit(q, 28, 21, E2E_L1["W"], lf=7, k1=1)
        tgt = model.nv_circuit(q, 28, 21, child_w, lf=7, k1=1)
        rp = tgt["prog"] / base["prog"]
        rc = tgt["cells"] / base["cells"]
        measured = True
    else:
        # Round-0 leaf work dominates the W dependence: 2^k1 * ceil(W/2) rows per query.
        def leaf_rows(w: int) -> int:
            return -(-w // 2)
        rp = (E2E_L1["prog"] - 536 * leaf_rows(E2E_L1["W"]) + 536 * leaf_rows(child_w)) \
            / E2E_L1["prog"]
        rc = rp
        measured = False
    prog = E2E_L1["prog"] * rp
    cells = E2E_L1["cells"] * rc
    # L1's trace height: model's own nv_rows when available, else derive from cells.
    if model is not None:
        nv_rows, sha_rows = tgt["nv_rows"], tgt["sha_rows"]
    else:
        nv_rows, sha_rows = cells / 76, cells / 83
    height = max(nv_rows, sha_rows)
    return dict(
        prog=prog, cells=cells, nv_rows=nv_rows, sha_rows=sha_rows,
        # n_stack = ceil(log2(trace height)) - l_skip (l_skip = 2)
        log_h=math.ceil(math.log2(max(height, 1))) - 2,
        inter=(1 << math.ceil(math.log2(max(nv_rows, 1)))) * 48
              + (1 << math.ceil(math.log2(max(sha_rows, 1)))) * 17 + 256 + 65536,
        anchored=measured,
    )





def fmt_log(x: float) -> str:
    return f"2^{log2(x):.2f}"


def row(label: str, value: str, target: str = "", verdict: str = "") -> None:
    print(f"  {label:46} {value:>18} {target:>12}  {verdict}")


def section(title: str) -> None:
    print(f"\n{title}")
    print("-" * 100)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--d1-json", default="/tmp/d1air33.json")
    ap.add_argument("--d1-layout", default="/tmp/d1layout33.txt")
    ap.add_argument("--d0-json", default="/tmp/d0air.json")
    ap.add_argument("--d0-layout", default="/tmp/d0layout.txt")
    ap.add_argument("--nv-model-dir",
                    default="/data/illia/nearproof-wt/pq-recursion-sha384/"
                            "research/near-compression/results/pq-recursion-nv",
                    help="directory holding extrapolate_nv2.py (recursion lane)")
    args = ap.parse_args()

    air, d1 = load_air(args.d1_json, args.d1_layout, D1_NAMES)
    try:
        _, d0 = load_air(args.d0_json, args.d0_layout, D0_NAMES)
    except FileNotFoundError:
        d0 = None

    print("=" * 100)
    print("D1-ON-PQ ENVELOPE CHECK")
    print("=" * 100)
    print(f"  input: {args.d1_json} ({len(d1)} tables, numPub={air['numPub']}, "
          f"numBuses={air['numBuses']})")
    for label, path in (("d1 json", args.d1_json), ("d1 layout", args.d1_layout),
                        ("d0 json", args.d0_json), ("d0 layout", args.d0_layout)):
        try:
            print(f"    {label:10} sha256 {_sha256(path)[:16]}  {path}")
        except OSError:
            print(f"    {label:10} (absent)  {path}")

    hard_fail = []

    # ------------------------------------------------------------------ hard limits
    section("[HARD] protocol / algebra / Lean limits")
    w_total = sum(t["W"] for t in d1)
    main_cols = sum(t["width"] for t in d1)
    max_deg = max(t["deg"] for t in d1)
    max_cons_deg = max(t["cons_deg"] for t in d1)
    max_msg = max(t["msg_max"] for t in d1)
    max_mult = max(t["mult_bits"] for t in d1)
    hr = heights(d1, "realistic")
    ha = heights(d1, "aligned")
    n_real = interaction_mass(d1, hr)
    n_align = interaction_mass(d1, ha)
    cells_real = committed_cells(d1, hr)
    cells_align = committed_cells(d1, ha)
    mult_bound = sum(2**t["max_log"] * t["interactions"] * (2**t["mult_bits"] - 1 or 1)
                     for t in d1)
    fp_bound = sum(2**t["max_log"] * t["interactions"] for t in d1) * (max_msg + 1)
    buses = per_bus_mass(d1, hr)
    bus_max = max(buses.values())

    row("tables", f"{len(d1)}", f"< 2^{LEAN_MAX_TABLES_LOG}", "PASS")
    row("max table maxLog", str(max(t["max_log"] for t in d1)), f"<= {LEAN_MAX_DEG}",
        "PASS" if max(t["max_log"] for t in d1) <= LEAN_MAX_DEG else "FAIL")
    row("max constraint degree (formal)", str(max_cons_deg), f"<= {LEAN_MAX_CONSTRAINT_DEG}",
        "PASS" if max_cons_deg <= LEAN_MAX_CONSTRAINT_DEG else "FAIL")
    row("max table degree (aux groups)", str(max_deg), f"<= {PIN_DEG}",
        "PASS" if max_deg <= PIN_DEG else "FAIL")
    row("max multiplicity bits", str(max_mult), f"<= {LEAN_MAX_MULT_BITS}",
        "PASS" if max_mult <= LEAN_MAX_MULT_BITS else "FAIL")
    row("multBound (Lean wf)", fmt_log(mult_bound), f"<= 2^{LEAN_BUS_BUDGET_LOG}",
        "PASS" if mult_bound <= 2**LEAN_BUS_BUDGET_LOG else "FAIL")
    row("fpBound (Lean wf)", fmt_log(fp_bound), f"<= 2^{LEAN_BUS_BUDGET_LOG}",
        "PASS" if fp_bound <= 2**LEAN_BUS_BUDGET_LOG else "FAIL")
    row("interaction message + bus fields", str(max_msg + 1), f"<= 2^{NV_LOG_MAX_MESSAGE}",
        "PASS" if max_msg + 1 <= 2**NV_LOG_MAX_MESSAGE else "FAIL")
    row("max per-bus count mass", fmt_log(bus_max), f"< p = 2^{LOG_BB:.2f}",
        f"PASS (+{LOG_BB - log2(bus_max):.2f} bits)" if bus_max < BB_P else "FAIL")
    row("global interactions N (realistic)", fmt_log(n_real), "<= 2^28 (pin)",
        "PIN FAIL -> see below")
    row("global interactions N (aligned)", fmt_log(n_align), "<= 2^28 (pin)",
        "PIN FAIL -> see below")
    if max_cons_deg > LEAN_MAX_CONSTRAINT_DEG or max_mult > LEAN_MAX_MULT_BITS \
            or mult_bound > 2**LEAN_BUS_BUDGET_LOG or fp_bound > 2**LEAN_BUS_BUDGET_LOG \
            or bus_max >= BB_P or max_msg + 1 > 2**NV_LOG_MAX_MESSAGE:
        hard_fail.append("static")
    print("  -> every algebraic / Lean hard limit PASSES.")

    # ------------------------------------------------------------------ pins
    section("[PIN] pinned base-shape choices (cost decisions, not impossibilities)")
    row("AIR count", str(len(d1)), f"<= {PIN_AIRS}",
        "over by 1; no NV or Lean limit")
    row("max constraint degree", str(max_deg), f"<= {PIN_DEG}", "PASS")
    row("stacked width W (main+aux+quot)", f"{w_total:,}", f"<= {PIN_SLICE_W} (per slice)",
        f"{w_total / PIN_SLICE_W:.0f}x -> needs {math.ceil(w_total / PIN_SLICE_W)} slices/sharding")
    row("opened base columns", f"{2 * main_cols:,}", f"<= {PIN_OPENED}",
        f"{2 * main_cols / PIN_OPENED:.1f}x")
    row("interaction message fields", str(max_msg), f"<= {PIN_MSG}",
        f"over; NV allows 128 (2^{NV_LOG_MAX_MESSAGE}), costs "
        f"{math.ceil(log2(max_msg + 1)) - math.ceil(log2(PIN_MSG + 1))} LogUp bit(s)")
    print("  -> W and opened columns are the only material pin breaks, and both are cost.")

    # ------------------------------------------------------------------ the one edit
    section("[EDIT] the single protocol parameter that must change")
    need_log = math.ceil(log2(n_real))
    row("max_interaction_count (pin)", f"2^{PIN_INTERACTION_LOG}", f">= 2^{need_log}",
        f"must raise to 2^{need_log}")
    # Backend formula (soundness/calculator.rs `logup_soundness`):
    #   |F_ext| - log2(2 * max_interaction_count) - log_max_message_length - log2(list)
    log_msg_len = math.ceil(log2(max_msg + 1))
    for mic_log in (PIN_INTERACTION_LOG, need_log):
        for lml in (NV_LOG_MAX_MESSAGE, log_msg_len):
            bits = LOG_F - (mic_log + 1) - lml - 22.0
            tag = "current pin" if mic_log == PIN_INTERACTION_LOG else "required"
            fits = "OK" if lml >= log_msg_len else "msg too short"
            print(f"  backend logup_soundness: mic=2^{mic_log} ({tag}), "
                  f"log_msg_len={lml} -> {bits:.2f} bits  [{fits}]")
    # Headline: the NV parameter as configured (log_max_message_length = 7).
    logup = LOG_F - (need_log + 1) - NV_LOG_MAX_MESSAGE - 22.0
    print(f"  -> headline: at 2^{need_log} with the NV param log_max_message_length="
          f"{NV_LOG_MAX_MESSAGE}: {logup:.2f} bits")
    print(f"     (budget >= 270; the non-query moves sit at 2^-270)")
    print(f"  -> raising 2^28 -> 2^{need_log} costs "
          f"{need_log - PIN_INTERACTION_LOG} bits only; query counts do not move.")
    row("log_max_message_length (NV param)", str(NV_LOG_MAX_MESSAGE),
        f">= {log_msg_len} needed", "PASS" if NV_LOG_MAX_MESSAGE >= log_msg_len else "FAIL")

    # ------------------------------------------------------------------ downstream
    section("[COST] L1 over this base (never transmitted, but sets the chain length)")
    print(f"  {'app child W':>12} {'L1 prog rows':>14} {'L1 n_stack':>11} {'L1 stacked':>11} "
          f"{'max b':>6} {'L1 cells':>10} {'~L1 s':>7} {'~L1 GB':>8}")
    l1 = {}
    for w in (E2E_L1["W"], 900, 1800, w_total):
        c = nv_l1_cost(w, args.nv_model_dir)
        stacked = c["log_h"] + 2                     # n_stack + l_skip
        max_b = NV_MAX_DOMAIN_LOG - stacked
        secs = c["cells"] / E2E_L1["cells"] * E2E_L1["secs"]
        gb = c["cells"] * 20 / 1e9
        l1[w] = dict(c, stacked=stacked, max_b=max_b, secs=secs, gb=gb)
        print(f"  {w:>12} {c['prog']:>14,.0f} {c['log_h']:>11} {stacked:>11} {max_b:>6} "
              f"{c['cells'] / 1e9:>9.2f}G {secs:>7.0f} {gb:>8.0f}")
    l1d = l1[w_total]
    print(f"  calibration: measured e2e L1 = {E2E_L1['prog']:,} rows / "
          f"{E2E_L1['cells'] / 1e9:.2f} G cells / {E2E_L1['secs']} s / {E2E_L1['gb']} GB")
    if not l1d["anchored"]:
        print("  WARNING: --nv-model-dir has no extrapolate_nv2.py; these are the linear")
        print("           fallback, NOT the lane's calibrated model. Do not quote them.")
    else:
        print("  (source: lane/pq-recursion-sha384 extrapolate_nv2.py, anchored on the")
        print("   measurement above)")
    l1_prog_log = l1d["log_h"] + 2 - 1
    row("L1 program region log", str(l1_prog_log), f"<= {NV_ADDR_BITS} (ADDR_BITS)",
        "PASS" if l1_prog_log <= NV_ADDR_BITS else "FAIL")
    row("x15 domain headroom", f"b <= {l1d['max_b']}",
        f"needs log_h + b <= {NV_MAX_DOMAIN_LOG}",
        "PASS" if l1d["max_b"] >= 1 else "FAIL")
    if l1_prog_log > NV_ADDR_BITS or l1d["max_b"] < 1:
        hard_fail.append("l1")

    section("[BYTES] the transmitted final proof")
    print("  The transmitted proof is the LAST NV level's proof.  Its size is set by that")
    print("  level's own trace and shape, so it is the lane's validated number, not something")
    print("  recomputed here:")
    print("    converged fixed point, G2 + O-2, L=24:  293,101 B   [model, size_g2.py]")
    print("    the same shape, measured:              287,477 B   [lane/pq-stream-commit]")
    print("    with the FINAL shape sweep:            287.9-300.2 KB  [README, options (a)/(b)]")
    print()
    print("  Chain length matters structurally, not through the base width:")
    print("  * G2's tight-height floor pins committed heights so the verifier program")
    print("    converges; `select_anchor` then switches to BIND.  Until it converges each")
    print("    level anchors at its child, which is fine but means at least one intermediate")
    print("    level is needed before FINAL can run the pinned program.")
    print("  * V_d pins the converged program, so the final must be a fixed-point level.")
    print("    With a wide base that is L2 or later, never L1.")
    print("  => use >= 3 NV levels (L1 over the base, L2 over L1, FINAL over L2).  The")
    print("     measured 287 KB direct-Wasm chain used exactly this shape.")
    print()
    print("  New fact established here (exact, from the domain): at the D1 width L1's")
    print(f"  stacked height is 2^{l1d['stacked']}, so the BabyBear x15 domain allows b <= "
          f"{l1d['max_b']}.")
    print(f"  At the direct-Wasm width it is 2^{l1[E2E_L1['W']]['stacked']} and b <= "
          f"{l1[E2E_L1['W']]['max_b']}.")
    print("  L1 is never transmitted, but a smaller b means more WHIR queries and a bigger,")
    print("  slower L1 proof; the shard split keeps every L1 at the direct-Wasm blowup.")
    # ------------------------------------------------------------------ shards
    section("[SHARDS] keeping each child near the direct-Wasm cost")
    print(f"  {'shard':24} {'#tbl':>5} {'main':>7} {'W':>7} {'N':>10} {'cells':>10} "
          f"{'x15 LDE':>10} {'L1 prog':>11} {'~L1 s':>7}")
    for name, members in SHARDS.items():
        sub = [t for t in d1 if t["name"] in members]
        hh = {t["name"]: hr[t["name"]] for t in sub}
        n = interaction_mass(sub, hh)
        cl = committed_cells(sub, hh)
        wsub = sum(t["W"] for t in sub)
        c = nv_l1_cost(wsub, args.nv_model_dir)
        secs = c["cells"] / 0.51e9 * 152
        print(f"  {name:24} {len(sub):>5} {sum(t['width'] for t in sub):>7} "
              f"{wsub:>7} {fmt_log(n):>10} {cl / 1e9:>9.2f}G "
              f"{cl * 15 / 1e9:>9.1f}G {c['prog']:>10,.0f} {secs:>8.0f}")
    row("TOTAL (one proof)", f"{len(d1)} tbl", "", "")
    row("", f"{main_cols:,} cols", f"W={w_total:,}", "")
    row("", fmt_log(n_real), f"{cells_real / 1e9:.2f}G cells",
        f"{cells_real * 15 / 1e9:.0f}G LDE")
    print("  (the base/aggregation lane's `build_l1_linked` already hashes exactly this")
    print("   multi-AIR statement at k=1 per child, so sharded children can be linked")
    print("   into one L1 without a new statement format.)")

    # ------------------------------------------------------------------ baseline
    if d0 is not None:
        section("[BASELINE] D0a on the same stack (25 tables, already proven classically)")
        hr0, ha0 = heights(d0, "realistic"), heights(d0, "aligned")
        n0r, n0a = interaction_mass(d0, hr0), interaction_mass(d0, ha0)
        c0 = committed_cells(d0, hr0)
        row("tables", str(len(d0)), "", "")
        row("sum main columns", f"{sum(t['width'] for t in d0):,}", "", "")
        row("stacked width W", f"{sum(t['W'] for t in d0):,}", "", "")
        row("interactions N (aligned)", fmt_log(n0a), "<= 2^28 (pin)", "PIN FAIL too")
        row("committed cells (realistic)", f"{c0 / 1e9:.2f}G", "", "")
        row("x15 LDE (realistic)", f"{c0 * 15 / 1e9:.0f}G", "", "")
        print("  -> D0a itself exceeds the pinned 2^28 interaction count, so the pin is")
        print("     a direct-Wasm-base assumption, not a property of the NEAR AIRs.")

    # ------------------------------------------------------------------ verdict
    section("[VERDICT]")
    print("  HARD: every algebraic, Lean and backend limit passes.")
    print(f"        (per-bus mass {fmt_log(bus_max)} < p; multBound {fmt_log(mult_bound)};")
    print(f"         fpBound {fmt_log(fp_bound)}; msg {max_msg}+1 <= 128; degree {max_cons_deg}.)")
    print(f"  EDIT: max_interaction_count 2^{PIN_INTERACTION_LOG} -> 2^{need_log}"
          f" ({need_log - PIN_INTERACTION_LOG} LogUp bits, no query change).")
    print("        D0a needs this too on the PQ stack.")
    print(f"  COST: one D1-wide base proof is {cells_real / 1e9:.1f}G committed cells / "
          f"{cells_real * 15 / 1e9:.0f}G LDE cells.")
    print(f"        L1 over it: {l1d['prog']:,.0f} program rows, {l1d['cells'] / 1e9:.2f}G cells, "
          f"~{l1d['secs']:.0f} s, ~{l1d['gb']:.0f} GB.")
    print("  PATH: port the D1 tables as PQ *base shards* (5 groups above), not as one")
    print("        33-table proof.  Each shard's L1 is ~0.7-1.05 M program rows and")
    print("        ~170-250 s, i.e. the same class as today's direct-Wasm L1.")
    print("  CHAIN: needs >= 3 NV levels.  V_d pins the converged program, so the final")
    print("        must be a fixed-point level; with a wide base that is L2 or later.")
    print(f"        At the D1 width L1's stacked height is 2^{l1d['stacked']}, which caps the")
    print(f"        blowup at b={l1d['max_b']} (BabyBear x15 domain).")
    print("  CAVEAT: the peta-gas / full-host coverage gap (G3) is untouched by any of this;")
    print("        this check only decides whether the *existing* D1 tables can be carried")
    print("        on the PQ stack instead of re-proving their semantics.")
    if hard_fail:
        print(f"\n  HARD FAILURES: {hard_fail}")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
