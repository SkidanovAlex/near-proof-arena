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
