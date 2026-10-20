# D1-on-PQ envelope check — 2026-10-19

Lane: continuation of the review thread "stop proving NEAR twice". Scope: decide whether the
kernel-checked `nearAirV3D1` tables can be carried on the post-quantum SWIRL/WHIR stack, and at
what cost, instead of re-deriving their semantics in `lane/pq-wasm-base`.

Artifact: `tools/d1-pq-envelope/check.py` (+ `README.md`). Nothing in the signed challenges,
`oracle/v3`, pinned files, the D0a certificate, or any PQ lane was modified.

## Method

The check reads the **compiled Lean exporter**, not prose:

* `np-lean-export-v3d1` @ `lane/v3-d1-a7b` → `/tmp/d1air33.json` (1,720,341 B, 33 tables,
  `numPub=350`, `numBuses=77`);
* `np-lean-export-v3d1 --layout 2` → per-table `width aux degree quot sendG recvG maxLog`;
* `np-lean-export-v3` @ `lane/v3-domain-bounds` → the D0a 25-table baseline.

The exporter of the *older* 30-table AIR (`lane/v3-d1-tables` build, 2026-10-14) is rejected by
the name-count assertion, so a stale binary cannot silently change the answer.

For downstream cost the script imports the recursion lane's calibrated
`extrapolate_nv2.nv_circuit` and anchors it on the measured e2e L1
(`lane/pq-e2e-slice`: 623,802 program rows, 0.51 G cells, 152 s, 10.1 GB, 8 threads).

## Result

### Hard limits — all pass

| limit | value | bound | source |
|---|---:|---|---|
| tables | 33 | `< 2^32` | `ZkFormal.V2.Admission` |
| `maxLog` | 22 | `<= 22` | `Table.wf` |
| formal constraint degree | 6 | `<= 16` | `nearAirV3D1.wf 16` |
| multiplicity bits | 1 | `<= 25` | `Table.wf` |
| `multBound` | `2^29.74` | `<= 2^36` | `Air.wf` |
| `fpBound` | `2^34.91` | `<= 2^36` | `Air.wf` |
| message + bus fields | 36 | `<= 128` | `log_max_message_length` |
| max per-bus count mass | `2^27.39` | `< p = 2^30.91` | keygen per-bus constraint |

The AIR is algebraically admissible on the PQ stack. No proof-system change is needed.

### Pins — two material cost breaks

| pin | D1 | pinned | interpretation |
|---|---:|---:|---|
| AIR count | 33 | 32 | not an NV or Lean limit |
| degree | 8 | 8 | pass |
| stacked width `W` | 3,822 | 24 | 159× — per-GPU-slice pin |
| opened columns | 7,026 | 1,024 | 6.9× |
| message fields | 35 | 16 | NV allows 128 |

`DESIGN-BASE §3`'s `W <= 24` / `opened <= 1024` describe a **narrow execution segment**, not a
state/receipt layer. Exceeding them is a cost decision, not an impossibility.

### One protocol parameter must change

`max_interaction_count` `2^28` → `2^30`. D1's N is `2^29.59` (realistic) / `2^29.74` (aligned).

Backend formula (`stark-backend/src/soundness/calculator.rs::logup_soundness`):

```
|F_ext| - log2(2 * max_interaction_count) - log_max_message_length - log2(list)
```

* at `2^28`, `log_msg_len=7`: 312.88 bits;
* at `2^30`, `log_msg_len=7`: **310.88 bits**;
* cost: **2 bits**, no WHIR query count moves.

**D0a needs the same edit** (N = `2^29.55`). The `2^28` pin is a direct-Wasm-base assumption; no
NEAR AIR of this class satisfies it. This is the concrete, actionable finding: any D0a/D1-class
proof on the PQ stack requires raising it, and that is safe against the `2^-270` non-query budget.

### Cost

| quantity | one 33-table proof | per-shard range |
|---|---:|---:|
| committed cells | 11.9 G | 0–4.6 G |
| x15 LDE cells | 179 G (716 GB as u32) | 0–68.5 G |
| L1 program rows | 2,522,917 | 698,853–1,051,266 |
| L1 cells | 2.00 G | 0.51–1.05 G |
| L1 time (8 threads, fast prover) | ~597 s | ~169–252 s |
| L1 peak memory | ~40 GB | ~10–20 GB |

Per shard (columns: tables, main columns, stacked W, interactions, committed cells, x15 LDE,
L1 program rows, L1 seconds):

| shard | # | main | W | N | cells | x15 LDE | L1 prog | ~L1 s |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| exec + 2×SHA | 2 | 1,088 | 1,116 | 2^27.09 | 4.56 G | 68.5 G | 1,051,266 | 252 |
| trie | 9 | 762 | 853 | 2^28.03 | 2.28 G | 34.2 G | 908,234 | 218 |
| scheduler + ChaCha | 8 | 832 | 901 | 2^27.81 | 3.49 G | 52.3 G | 934,339 | 224 |
| receipts + accounts | 6 | 407 | 468 | 2^27.24 | 1.59 G | 23.9 G | 698,853 | 169 |
| D1 tx + unread | 8 | 424 | 484 | 2^14.54 | ~0 G | ~0 G | 707,554 | 171 |

Each sits at the same scale as today's direct-Wasm L1. `build_l1_linked` already hashes this
multi-AIR statement form, so sharded children link without a new statement format.

### L1 domain headroom shrinks with base width

L1 is not transmitted, but its stacked height caps the WHIR blowup (BabyBear x15 needs
`log_h + b <= 27`):

| base W | L1 n_stack | L1 stacked log_h | max b | L1 cells | ~L1 s | ~L1 GB |
|---:|---:|---:|---:|---:|---:|---:|
| 330 (direct-Wasm) | 21 | 23 | 4 | 0.51 G | 152 | 10 |
| 900 | 21 | 23 | 4 | 0.75 G | 224 | 15 |
| 1,800 | 22 | 24 | 3 | 1.13 G | 338 | 23 |
| 3,822 | 23 | 25 | **2** | 2.00 G | 597 | 40 |

### Chain length is structural, not about bytes

The transmitted final is the **last NV level's** proof, so its size is set by that level's trace,
not by the base width. Validated reference numbers:

* converged fixed point, G2 + O-2, `L = 24`: **293,101 B** (model, `size_g2.py`);
* measured with binding on at every level: **293,077 B** (G2 gate, `lane/pq-stream-commit/g2-gate/`);
  an earlier `bind = false` run gave 287,477 B, which is not the sound configuration;
* FINAL shape sweep: 287.9–300.2 KB.

What forces **≥ 3 NV levels** is soundness, not size: V_d pins the converged verifier program, so
the final must run at the fixed point. With a wide base that is L2 or later. The measured 287 KB
direct-Wasm chain has exactly this shape.

## Cross-check with the parallel lanes

`lane/pq-d1-envelope` (`7cd1a7135`) and `lane/pq-state-port` (`c69358866`) did this
independently the same day, including real SWIRL proofs (23/30 D1 tables; all 25 D0a tables).

* All 33 per-table widths, maxLogs, interaction counts and message lengths **match**
  `envelope-d1a7b.csv`; `multBound = 2^29.74` matches.
* Correction absorbed: the formal max constraint degree is **6**. My first version said 7 because
  it counted constants as degree 1; `ZkFormal.Air.Expr.degree` counts them as 0.
* Their 2^27.92 interaction count is at per-fixture render heights; my 2^29.59 floors the D1-only
  tables at log 10 and keeps the six fixed tables at 2^22. Both are recorded; the pin verdict uses
  the conservative one.
* Their "opened columns" includes rotated columns; mine is `2 × main` (the stacking claim count).

Their recommendation matches mine: port the state tables unchanged, keep direct-Wasm for
execution, join on shared buses.

## Verdict

1. **Port the D1 tables**, rather than re-deriving them: every hard limit passes.
2. **As five shards**, not one 33-table proof: the width pin is a cost boundary, and sharded L1s
   match today's direct-Wasm L1.
3. **With ≥ 3 NV levels**: V_d pins the converged program, so the final must be a fixed-point
   level; with a wide base that is L2 or later.
4. **Raise `max_interaction_count` to `2^30`** on the PQ stack (D0a needs it too). Two bits.

## What this does not establish

* Full NEAR / 1 Pgas coverage, host functions, or whole-chunk semantics. The G3 coverage gap is
  untouched; this only replaces re-proving the *existing* D1 table semantics.
* Any measured proof. All L1/final numbers are the recursion lane's calibrated model anchored on
  the measured e2e L1, labelled as such.
* That the `W <= 24` pin should be relaxed: the recommendation is to shard, keeping the pin.

## Input hashes (this run)

```
9f92e7b1b5fbc6ea  /tmp/d1air33.json     np-lean-export-v3d1 @ lane/v3-d1-a7b
17909e8d4777443b  /tmp/d1layout33.txt   np-lean-export-v3d1 --layout 2
b19407e81d389879  /tmp/d0air.json       np-lean-export-v3 @ lane/v3-domain-bounds
a672ed219b62a76f  /tmp/d0layout.txt     np-lean-export-v3 --layout 2
```

## Reproduce

```sh
B=/data/illia/nearproof-wt/v3-d1-a7b/examples/np-udr-stark-v2/conformance/.lake/build/bin
B0=/data/illia/nearproof-wt/v3-domain-bounds/examples/np-udr-stark-v2/conformance/.lake/build/bin
$B/np-lean-export-v3d1 > /tmp/d1air33.json
$B/np-lean-export-v3d1 --layout 2 > /tmp/d1layout33.txt
$B0/np-lean-export-v3 > /tmp/d0air.json
$B0/np-lean-export-v3 --layout 2 > /tmp/d0layout.txt
python3 tools/d1-pq-envelope/check.py; echo "exit=$?"
```
