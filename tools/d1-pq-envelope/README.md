# D1-on-PQ envelope check

Decides, by computation over the actual exported Lean AIR, whether the kernel-checked
`nearAirV3D1` (33 tables: trie, scheduler, ChaCha, receipts, accounts, and D1's tx/unread-key
tables) can be carried on the post-quantum SWIRL/WHIR stack instead of re-proving its semantics
from scratch in `pq-wasm-base`.

The question this answers is **not** "does D1 have ≤ 32 AIRs". It is "which limits are hard
(protocol/algebra/Lean), which are pinned cost choices, and what does carrying D1 actually
cost."

## Input hashes (this run)

```
9f92e7b1b5fbc6ea  /tmp/d1air33.json     np-lean-export-v3d1 @ lane/v3-d1-a7b
17909e8d4777443b  /tmp/d1layout33.txt   np-lean-export-v3d1 --layout 2
b19407e81d389879  /tmp/d0air.json       np-lean-export-v3 @ lane/v3-domain-bounds
a672ed219b62a76f  /tmp/d0layout.txt     np-lean-export-v3 --layout 2
```

## Run

The check reads the compiled Lean exporters, so no Lean rebuild is needed.

```sh
# 1. Export the actual AIRs (lane/v3-d1-a7b has the newest D1 definitions).
B=/data/illia/nearproof-wt/v3-d1-a7b/examples/np-udr-stark-v2/conformance/.lake/build/bin
$B/np-lean-export-v3d1 > /tmp/d1air33.json
$B/np-lean-export-v3d1 --layout 2 > /tmp/d1layout33.txt

# D0a baseline (any tree whose exporter is current; v3-domain-bounds here).
B0=/data/illia/nearproof-wt/v3-domain-bounds/examples/np-udr-stark-v2/conformance/.lake/build/bin
$B0/np-lean-export-v3 > /tmp/d0air.json
$B0/np-lean-export-v3 --layout 2 > /tmp/d0layout.txt

# 2. Check.
python3 tools/d1-pq-envelope/check.py
```

Exit code 0 = every hard limit passes. The script prints `HARD`, `PIN`, `EDIT`, `COST`,
`BYTES`, `SHARDS`, `BASELINE` and `VERDICT` sections.

Point `--nv-model-dir` at a checkout of `lane/pq-recursion-sha384` to use that lane's calibrated
`extrapolate_nv2.py` for the L1/final numbers; otherwise the script falls back to a documented
linear model and says so in the `src` column.

## What it found (2026-10-19, `nearAirV3D1` @ `lane/v3-d1-a7b`)

### Hard limits: all pass

| limit | value | bound |
|---|---:|---|
| tables | 33 | `< 2^32` |
| max `maxLog` | 22 | `<= 22` |
| max constraint degree (formal) | 6 | `<= 16` (`nearAirV3D1.wf 16`) |
| max multiplicity bits | 1 | `<= 25` |
| `multBound` | `2^29.74` | `<= 2^36` |
| `fpBound` | `2^34.91` | `<= 2^36` |
| message + bus fields | 36 | `<= 2^7 = 128` |
| max per-bus count mass | `2^27.39` | `< p = 2^30.91` |

So the AIR is *algebraically admissible* on the PQ stack. Nothing here needs a proof system
change.

### Pins: two cost breaks, no impossibility

| pin | value | pinned | note |
|---|---:|---:|---|
| AIR count | 33 | 32 | not an NV or Lean limit |
| degree | 8 | 8 | pass |
| stacked width `W` | 3,822 | 24 | **159×** — a *per-GPU-slice* pin |
| opened base columns | 7,026 | 1,024 | 6.9× |
| interaction fields | 35 | 16 | NV allows 128 |

The `W <= 24`, `opened <= 1024` numbers in `DESIGN-BASE §3` describe a **narrow execution
segment**, not a NEAR transition. D1 is a state/receipt layer, so it is intrinsically wide.
Exceeding those pins is a cost decision.

### One protocol parameter must change

`max_interaction_count` is pinned at `2^28`, but D1 needs `2^30` (N = `2^29.59` realistically,
`2^29.74` aligned). This is a security parameter, not a shape: raising it costs **2 bits** on the
backend's LogUp term and does **not** move any WHIR query count.

The backend formula (`logup_soundness`) gives **310.88 bits** at `2^30` / `log_max_message_length=7`,
against a `2^-270` non-query budget. So the change is safe and cheap.

Critically: **D0a needs this too** (N = `2^29.55`). The `2^28` pin is an artefact of the
direct-Wasm base assumption, not a property of the NEAR AIRs. Any D0a/D1-class AIR proof on the PQ
stack needs the same edit.

### Cost: the reason to shard

One D1-wide base proof is **11.9 G committed cells / 179 G x15-LDE cells**, and L1 over it is
**2.52 M program rows / 2.0 G cells / ~597 s / ~40 GB**.

Sharded into five groups, each shard's L1 is the same class as today's direct-Wasm L1:

| shard | tables | main | W | L1 program rows | ~L1 s |
|---|---:|---:|---:|---:|---:|
| exec + 2×SHA | 2 | 1,088 | 1,116 | 1,051,266 | 252 |
| trie | 9 | 762 | 853 | 908,234 | 218 |
| scheduler + ChaCha | 8 | 832 | 901 | 934,339 | 224 |
| receipts + accounts | 6 | 407 | 468 | 698,853 | 169 |
| D1 tx + unread keys | 8 | 424 | 484 | 707,554 | 171 |

`build_l1_linked` already hashes exactly this multi-AIR statement form, so sharded children link
into one L1 with no new statement format.

### L1's domain headroom shrinks with the base width

L1 is never transmitted, but its stacked height caps the WHIR blowup (BabyBear's x15 domain
requires `log_h + b <= 27`):

| base W | L1 n_stack | L1 stacked log_h | max b | L1 cells | ~L1 s | ~L1 GB |
|---:|---:|---:|---:|---:|---:|---:|
| 330 (direct-Wasm) | 21 | 23 | 4 | 0.51 G | 152 | 10 |
| 900 | 21 | 23 | 4 | 0.75 G | 224 | 15 |
| 1,800 | 22 | 24 | 3 | 1.13 G | 338 | 23 |
| 3,822 (one D1 proof) | 23 | 25 | **2** | 2.00 G | 597 | 40 |

A smaller `b` means more WHIR queries and a larger, slower L1 proof. Sharding keeps every L1 at
the direct-Wasm height.

### The transmitted final proof

The final is the **last NV level's** proof, so its size is set by that level's trace and shape, not
by the base width. The lane's validated numbers are the reference:

* converged fixed point, G2 + O-2, `L = 24`: **293,101 B** (model, `size_g2.py`);
* the same shape, measured **with binding on at every level** (the sound setting):
  **293,077 B**, G2 gate 2026-10-19 (`lane/pq-stream-commit/g2-gate/`); an earlier
  `bind = false` run measured 287,477 B, which is not the sound configuration;
* FINAL shape sweep: **287.9–300.2 KB** (README options (a)/(b)).

Chain length matters **structurally**: V_d pins the converged verifier program, so the final must
run at the fixed point. With a wide base that is L2 or later, so **≥ 3 NV levels** are needed. The
measured chain (G2 gate, 5 levels, 293,077 B) already has exactly this shape. A 2-level chain
would require V_d to pin a non-converged program, which is the G2 soundness gap the anchor
design closes.

## Cross-check against the parallel lanes

Two lanes did this independently on the same day:

* `lane/pq-d1-envelope` @ `7cd1a7135` — per-table envelope CSVs from the same Lean exports, plus
  an actual SWIRL proof of 23/30 D1 tables (`00-h10007-s3`, 1,261,284 B, 82 s, tamper 14/14);
* `lane/pq-state-port` @ `c69358866` — the full 25-table D0a port, no stand-in table,
  1.02–1.60 MB proofs, tamper 19/19.

Agreement: **all 33 per-table widths, maxLogs, interaction counts and message lengths match**
(this script's table vs `envelope-d1a7b.csv`), as do `multBound = 2^29.74` and the verdict that
the constraint polynomials carry over unchanged. Their `multBoundP = 1,256,435,420` is
`multBound` plus the public segments, which this script excludes.

Correction found by the cross-check: the formal max constraint degree is **6**, not 7. This
script's first version counted constants as degree 1; `ZkFormal.Air.Expr.degree` counts them as
0. Fixed, and the `[HARD]` table now also shows the two degree columns separately (formal
constraint degree 6, table degree 8 with aux groups).

Two definitional differences, both benign:
* their "fractions at the fixture" (2^27.92) uses per-fixture render heights; this script's
  "realistic" (2^29.59) floors D1-only tables at log 10 and keeps the six fixed tables at 2^22.
  Both bases are recorded; the pin comparison uses the conservative one.
* their "opened columns" counts next-row (rotated) columns; this script reports `2 × main`, which
  is the SWIRL stacking claim count.

## Verdict

1. **Port it.** Every hard limit passes; the only protocol edit is a 2-bit LogUp parameter that
   D0a needs anyway.
2. **Port the tables as shards, not the 33-table AIR as one proof.** The width pin is a cost
   boundary; five shards keep each L1 at today's scale.
3. **Require ≥ 3 NV levels** so the final runs at the converged fixed point (V_d pins it).
4. **This does not close G3.** Host/trie/receipt coverage on the PQ stack, 1 Pgas capacity and
   full chunk semantics are untouched. The check only says the *existing* D1 tables can be
   carried instead of re-derived.

## Caveats

* The `W`/`opened`/`interactions` pins are read from `pq-base-aggregation/DESIGN-BASE.md §3`.
  They are design pins for the narrow execution segment.
* The `max_interaction_count` failure is a *configuration* failure, not a soundness one; the
  script reports the security cost explicitly.
* L1/final numbers use `extrapolate_nv2.py`, calibrated on the measured e2e L1 (623,802 rows,
  0.51 G cells, 152 s, 10.1 GB). They are model figures, clearly labelled.
* The D1 export used here is the **33-table** one from `lane/v3-d1-a7b`. The older 30-table export
  in `lane/v3-d1-tables` is rejected by name count on purpose, so a stale binary cannot silently
  change the result.
