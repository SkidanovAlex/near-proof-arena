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
