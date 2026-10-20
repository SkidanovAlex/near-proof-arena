# R lane: in-circuit SWIRL verifier on SHA-384/Ext12 (recursion)

Branch `lane/pq-recursion-sha384`. Dependencies are rebuilt by
`native/recursion/setup_recursion_deps.sh` (pinned upstream + `native/recursion/patches/`),
default root `/data/illia/nearproof-deps/pq-recursion`. All runs: CPUs 8-15/24-31,
`RAYON_NUM_THREADS=8`, `heavy` cgroup cap 16G unless stated.

## Milestone 1: stock OpenVM verifier sub-circuit, calibrated (measured)

Crate: OpenVM v2.1.0-rc.1 `crates/recursion` (`f08bf283`), stark-backend `d667af5`
(unpatched, as locked by OpenVM), BabyBearPoseidon2 (Ext4, Poseidon2 sponge + Merkle).
Test: `calib_tests.rs` (patch `openvm-stock-calib.patch`). It proves a Fib child,
builds `VerifierSubCircuit<1>` for the child VK, runs the debug constraint/bus checker,
proves and verifies the verifier circuit, then repeats one level up (the next child is
the verifier-circuit proof). Logs: `logs/calib-stock-*.log`.

Parameters (OpenVM production presets, 100-bit proven):
* child: `app_params_with_100_bits_security(20)`: l_skip 4, n_stack 16, log_blowup 1,
  k 4, queries [193, 88, 81], PoW (mu, fold, query) = (15, 5, 20).
* parent (every level): `internal_params_with_100_bits_security()`: l_skip 2,
  n_stack 17, w_stack 512, log_blowup 3, k 4, queries [68, 30, 20],
  PoW (20, 18, 20), LogUp PoW 19.

| level | child verified | committed cells (padded) | used cells | proof bytes | prove s |
|---:|---|---:|---:|---:|---:|
| 0 | Fib 2¹⁶ (app params) | — | — | 252,221 | 0.8 |
| 1 | Fib proof | 12,586,802 | 10,139,209 | 291,081 | 4.4 |
| 2 | L1 proof | 8,819,952 | 7,289,396 | 256,201 | 3.6 |
| 3 | L2 proof | 8,787,184 | 6,813,832 | 256,201 | 3.8 |
| 4 | L3 proof | 8,787,184 | 6,813,832 | 256,201 | 3.9 |

The leaf-params child (l_skip 4, n_stack 17, log_blowup 2) gives L1 18.3M cells /
335,865 B, then the same fixed point (8.79M cells, 256,201 B) from L2 on. Peak RSS
1.0–1.4 GB. The debug checker passes at every level.

**Fixed point (L3), per AIR, padded cells (height × width):**

| AIR | height | width | cells | used rows | share |
|---|---:|---:|---:|---:|---:|
| Poseidon2Air | 16,384 | 301 | 4,931,584 | 12,353 perms | 56.1 % |
| SymbolicExpressionAir (cached child-VK DAG + main) | 32,768 | 12+12 | 786,432 | all | 8.9 % |
| FinalPolyQueryEvalAir | 16,384 | 45 | 737,280 | 16,164 | 8.4 % |
| InitialOpenedValuesAir | 8,192 | 89 | 729,088 | 4,352 | 8.3 % |
| Eq3bAir | 16,384 | 25 | 409,600 | 9,253 | 4.7 % |
| MerkleVerifyAir | 8,192 | 38 | 311,296 | 6,254 | 3.5 % |
| TranscriptAir | 4,096 | 44 | 180,224 | 2,461 | 2.1 % |
| InteractionsFoldingAir | 4,096 | 37 | 151,552 | 3,661 | 1.7 % |
| ExpBitsLenAir | 8,192 | 16 | 131,072 | all | 1.5 % |
| OpeningClaimsAir | 2,048 | 63 | 129,024 | all | 1.5 % |
| ConstraintsFoldingAir | 4,096 | 25 | 102,400 | 2,249 | 1.2 % |
| 28 other AIRs | | | 188,624 | | 2.1 % |

**Hashing vs field arithmetic.** Hash AIRs (Poseidon2 + MerkleVerify + Transcript)
are 5.42M of 8.79M cells (62 %) at the fixed point and 44 % at L1. Everything else
(sumchecks, eq tables, constraint DAG, WHIR folding, final-poly evaluation, opened-value
batching), the "arithmetic" part, is 3.36M cells with Ext4.

**What this predicts for the SHA-384/Ext12 port (model, not measured).** The
arithmetic part is dominated by extension-field columns. Going from Ext4 to Ext12
roughly triples it, to about 10M cells. One Poseidon2 permutation is one 301-cell row.
One SHA-512 compression is 19,448 cells (L3 milestone 1). The verifier needs a few
thousand compressions, which is 60–200M cells. So hashing will be about 85–95 % of
the SHA-port verifier, and the fixed point is set by the in-circuit SHA count, as
`levers_model.py` assumes. The OpenVM verifier's layout of the non-hash part is
nearly free by comparison.

## Milestone 2: verifier ported to SHA-384/Ext12 (measured)

Tree `openvm-sha384` (patch `native/recursion/patches/openvm-recursion-sha384.patch`;
the workspace points at the pinned, patched stark-backend and Plonky3 Ext12 trees).

**What changed in `crates/recursion`:**
* The child config is `sha384::config::Sha384Config`. It matches
  `airbender/direct-wasm/native_sha384_config.rs` byte for byte: framing, rejection
  sampling, flush/observe semantics, leaf and node formats, and digest codec. Three
  tests check this. The recorded native transcript vectors reproduce. A differential
  test against a verbatim copy of the native file (`native_ref.rs`; setup `cmp`s it)
  covers random leaves, nodes and 4,000 random transcript operations. The setup script
  also checks that the copy has not drifted from the native file. `grind` uses the
  trait default (search) instead of `assert bits == 0`, and `check_witness` is
  unchanged.
* D_EF = 12. The extension helpers (`utils.rs`) are now generic in X^12 − 31, and every
  hard-coded Ext4 literal and column array is gone.
* Digests in-circuit are 24 limbs: the SHA-512 words H0..H5, as 16-bit limbs. On the
  transcript bus, commit limbs carry kind 2, because `observe_commit` is a distinct SHA
  event.
* **SHA subsystem** (`sha384/airs.rs`, `jobs.rs`): the L3 compression AIR, with
  parameterised buses (442 columns × 44 rows per compression), plus:
  * `ShaMsgAir`: a byte packer, one row per message word. It frames
    `PREFIX‖tag‖units` from 4-byte units (canonical little-endian field elements, or
    big-endian limb pairs), places the 0x80 padding and the 128-bit length, and assigns
    unique job ids.
  * `ShaBlockAir`: one row per block. It chains from the SHA-384 IV and emits the digest.
  * `ShaByteAir`: the byte lookup table.
  * Every message of the native config fits this unit format. It is parameterised by
    unit stream, so 42-byte digests or coset-as-one-message leaves only change the
    producers.
* **Transcript**: Poseidon2 sponge → `TranscriptHashAir` (one row per SHA job:
  flush/commit/squeeze), `TranscriptObsAir` and `TranscriptSampleAir`. The sample AIR
  does the exact n < 2p rejection test. The hash AIR enforces the job grammar: a flush
  is followed by a commit or squeeze; a squeeze follows a squeeze only after all 12
  words are used; a rejected word forces a re-squeeze. A t_start chain ties jobs to
  transcript indices.
* **Merkle**: each `MerkleVerifyAir` row is one SHA-384("NPQ4NODE"‖L‖R) compression on
  the compression interface. The root-check row hashes nothing.
* **WHIR leaves**: `InitialOpenedValuesAir` and `NonInitialOpenedValuesAir` send their
  values as job units and receive the leaf digest.

**Correctness evidence** (`sha384/tests.rs`, `sha384/e2e_tests.rs`):
* SHA subsystem: 27 random jobs, with lengths at every padding boundary, plus direct
  compressions. Digests equal `Sha384::digest` of the framed message. The debug checker
  passes. 70 single-cell mutations are rejected.
* End-to-end: real SHA-384/Ext12 child proofs, Fib and an interactions fixture, each
  proven and natively verified. The ported circuit's traces pass the debug checker,
  covering all constraints and all buses.
* Mutations, all rejected by the circuit (debug builder), never by tracegen:
  * one flipped Merkle sibling digest: MerkleVerifyAir root check;
  * one flipped opened value: root check;
  * one flipped transcript sample, re-filled so its own row is consistent: the
    transcript bus disagrees with GkrInputAir, and the state-word bus disagrees with
    TranscriptHashAir;
  * one flipped commit limb: the transcript bus disagrees with ProofShapeAir, and the
    unit bus disagrees with ShaMsgAir.

**Measured, small child.** The child is Fib 2⁵ with test params (l_skip 2, n_stack 8,
k 3, log_blowup 1, 5-bit queries [13, 7, 6]); this is the stock tests' child size. The
verifier circuit has 45 AIRs and **15,458,850 committed cells**. It uses 716 SHA-512
compressions: 371 Merkle nodes, 345 job blocks over 93 transcript jobs and the leaf jobs.
The SHA AIR is 2¹⁵ × 442 = 14.48M cells (94 %). The next largest AIRs are ShaMsgAir
(0.37M), StackingClaimsAir (0.34M), ShaBlockAir (69k) and MerkleVerifyAir (49k).

The circuit was proven with the native PQ profile (l_skip 2, n_stack 18, k 3,
log_blowup 3, ListDecoding m = 3, 268 query bits, queries [210, 118, 82, 63, 51, 43];
calculator total 268.3 bits). Result: **1,318,194 B**, of which WHIR is 950,364,
relations (column openings) 329,996, GKR 34,328 and stacking 2,852. It took **20.3 s**
to prove (8 threads, optimized CPU backend), 0.086 s to verify, with **1.95 GB** peak
RSS (log `logs/m2-small-child.log`).

**Medium child (measured cells; proof not attempted).** The child is Fib 2¹⁰ with
n_stack 8, log_blowup 3, unique decoding at 100 bits (queries [121, 105, 102]). The
verifier needs 8,081 compressions: 5,267 Merkle nodes, 2,814 job blocks and 136
transcript jobs. That pads the SHA AIR to 2¹⁹ rows, for **237.5M cells**, and the debug
checker passes. Verifying a child costs about q·(2ᵏ − 1 + depth) node compressions plus
q·2ᵏ leaf blocks per round.

**Finding: column openings.** The ported circuit has **3,472 columns, and 6,696 of them
are opened (the rest are not rotated)**. That is ≈ 321 KB of Ext12 column openings,
independent of WHIR parameters. `levers_model.py` assumes about 300 columns (≈ 32 KB).
At this width a proof of this circuit cannot be under 300 KB, whatever the WHIR levers.
A final layer needs a much narrower final circuit (≲ 500 opened columns), for example:
* Ext12 arithmetic laid out over rows rather than as 12 columns;
* merged AIRs;
* or a protocol change that batches the column openings.

### Milestone 2 addendum: columns, next-row use, interactions, cells (measured)

Per-AIR table: `logs/m2-airtab.log` (`L2_AIRTAB`: height, width, need_rot,
interactions per row, rows × interactions, cells). The groups below are for L2, the
circuit that verifies a verifier proof; this run used the 2-instance SHA layout, see
below.

| group | columns | opened (×2 if next-row) | rows × interactions | cells |
|---|---:|---:|---:|---:|
| SHA compression (2 × 442) + table 18 | 902 | 1,804 | 12.7M | 130.4M |
| hash glue: block 134, msg 45, byte 2, Merkle 95, transcript 95 + 8 + 20 | 399 | 703 | 2.8M | 8.5M |
| verifier logic (37 AIRs, Ext12) | 2,622 | 5,091 | 2.7M | 10.0M |
| **total** | **3,923** | **7,598 (≈ 365 KB)** | **18.2M (L = 25)** | **148.9M** |

* With one SHA instance (the default now, `VerifierConfig::sha_instances = 1`):
  3,481 columns, 6,714 opened (≈ 322 KB).
* Stock OpenVM (Ext4, Poseidon2) at its fixed point: 1,537 columns, 2,670 opened,
  1.02M interactions (`logs/calib-stock-app-internal.log`).
* Going to Ext12 roughly doubles the verifier-logic columns: about 1,236 → 2,622.
* 37 of the 46 AIRs reference the next row.
* GKR: the formula 72L² + 264L + 248 predicts 37.5 KB at L1 (L = 21; measured
  34,328 B) and 51.8 KB at L2 (L = 25; measured 48,056 B).

The cells split is reported in every run (`*_CELLS_SPLIT`). At L2 the SHA compression
AIRs are 130.4M cells and everything else is 18.5M. Of that 18.5M, 8.5M is SHA glue
and only about 10M is verifier arithmetic: SymbolicExpression 5.2M, Eq3b 1.3M,
InteractionsFolding 1.4M, and so on.

## Milestone 3: recursion fixed point (measured, at a reduced query target)

**What fits in 24 GB.** At the PQ target (268 query bits, log_blowup 3) only the first
level is provable here. Run `logs/m3-L2-at-268.log`:
* L1 is proven: 1,318,194 B.
* L2, the circuit verifying that real 268-bit L1 proof, needs **30,332 compressions**
  (20,089 Merkle nodes, 10,243 job blocks over 832 transcript jobs) and **958.5M cells**.
  Of those, 926.9M are SHA. The debug-free tracegen takes 7.8 GB peak.
* Proving L2 would take roughly 100 GB. Extrapolated from the measured 24.8 GB at
  193M cells, that is ≈ 130 B/cell, linear in cells.

So the fixed point was run as a fully proven chain at a 20-bit query target. Parent
params at every level: l_skip 2, n_stack 18, k 3, log_blowup 3, ListDecoding m = 3,
queries [16, 9, 7, 5, 4, 4]. The circuit used two SHA instances to halve the
power-of-two padding. The L0 child is Fib 2⁵ with test params. Log:
`logs/m3-chain-T20.log`. Peak RSS was 24.8 GB, at L4.

| level | verifies | compressions (nodes / job blocks / transcript jobs) | cells | proof B (gkr / relations / whir) | prove s |
|---:|---|---|---:|---:|---:|
| 1 | Fib child | 716 (371 / 345 / 93) | 15.46M | 487,030 (34,328 / 372,292 / 76,892) | 20 |
| 2 | L1 proof | 6,388 (1,573 / 4,815 / 801) | 148.9M | 573,702 (48,056 / 374,116 / 141,916) | 194 |
| 3 | L2 proof | 7,403 (1,573 / 5,830 / 1,053) | 164.1M | 581,542 (48,056 / 374,116 / 149,084) | 205 |
| 4 | L3 proof | 7,516 (1,573 / 5,943 / 1,033) | 193.0M | 597,222 (48,056 / 374,116 / 163,420) | 254 |

The native verifier accepts every level's proof, and every level's circuit is built
from the real previous-level proof.

**Per level:** Merkle work is fixed by the parameters (1,573 nodes). Job blocks and the
transcript grow slightly, then settle; compressions converge (6.4k → 7.4k → 7.5k).
Cells grow 149M → 164M → 193M only through power-of-two padding of individual AIRs.
Proof bytes are within 4 % from L2 on. Relations are constant at 374 KB, because the
column count is fixed by the circuit, not the child.

At this low target, about 4k of the ~7.5k compressions are transcript absorption of
the child's column openings: 7.6k Ext12 openings is ≈ 365 KB of flush messages. So
columns cost twice: once as proof bytes, and again as next-level SHA work.

**Measured against the model** (`final_layer_model.proof_bytes` at the same shape):
* L1 at 268 bits: the model gives 1,077,697 B. Adding the second round-0 commitment
  (the cached child-VK trace; the model assumes one commit) gives 1,279,297 B, against
  1,318,194 B measured (−3 %).
* T = 20, L2..L4: with the 2-commit fix the model gives 520–542 KB, against 574–597 KB
  measured. The gap is GKR: the model's fixed 8,456 B against 48,056 B measured. The
  levers lane's 72L² + 264L + 248 closes it.
* The model's `verifier_sha_blocks` predicts 19,688 compressions to verify the 268-bit
  L1 shape, against 30,332 measured. The difference comes from the two commits (paths
  and leaves doubled in round 0) and from transcript absorption of 6.7k column
  openings: about 3k blocks, against the model's fixed 733.
* So c_fixed and c_query are not small. They scale with the child's columns.

**Conclusion on the final layer (measured, not modelled).** A final layer built on this
circuit cannot be under 300 KB, whatever the WHIR levers. Its column openings alone are
322 KB (1 SHA instance) or 365 KB (2), plus about 50 KB of GKR. The cheapest final
proof would be at least ≈ 450–500 KB even with an ideal WHIR part.

The < 300 KB target needs a different final circuit:
* ≲ 500 opened columns in total, and ≲ 2²² interactions;
* SHA in one narrow AIR;
* the Ext12 verifier logic merged into a few wide AIRs, or laid out over rows;
* no cached-VK commitment (`has_cached = false`, which needs a SHA port of
  `dag_commit`) or a single commitment, to halve the round-0 paths.

The penultimate layers can stay on this circuit, since only the final layer's columns
are on the wire.
