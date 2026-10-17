# L3 milestone 1: narrow SHA-512/384 compression AIR (measured)

Crate: `research/near-compression/native/sha384-air/`. It runs on the pinned OpenVM
stark-backend (SWIRL: LogUp-GKR interactions + WHIR) and proves with the native
SHA-384/Ext12 config (`airbender/direct-wasm/native_sha384_config.rs`, BabyBear
`X^12-31`, ListDecoding m=3, 268 query bits). Machine data: `report.json` and `logs/`.

**Headline (measured):** **442 committed columns × 44 rows = 19,448 committed base-field
cells per compression** when the rows fill a power of two. At N = 1,024 and N = 4,096 the
height pads up, giving 28,288 cells per compression. The design floor for word bits alone
(a, e and W bits) is 15,360 cells, so this layout is 1.27× that floor. The lane AIR it
replaces had about 419k cells (5,234 columns × 80 rows).

## Design

The AIR is the SHA-512 compression from FIPS 180-4 §6.4.2. SHA-384 uses the same
compression; the consumer chooses the SHA-384 IV and reads output words 0..5. Each
compression is one segment of 44 rows with **two rounds per row**:

| row r | a/e slots (A0, A1, E0, E1) | W slots |
|---|---|---|
| 0, 1 | input state: a₋₄,a₋₃ / a₋₂,a₋₁ = H3,H2 / H1,H0 (e: H7..H4) | unused (zero) |
| 2..41 | a, e of rounds 2r−4, 2r−3 | W of rounds 2r−4, 2r−3 (block words for r ≤ 9) |
| 42, 43 | output state H′ = H + final words (feed-forward) | unused (zero) |
| pad (r = 44) | zero | zero |

**Why two rounds per row.** The backend gives each constraint a two-row window. Maj
and Ch need the bits of three consecutive words in that window. With two words per row,
every needed triple fits in two adjacent rows, and no word is stored twice. One round
per row would need a duplicated history word, about 320 bits per round.

**How words and additions are represented.**
* Words are bits, because Σ0, Σ1, σ0, σ1, Ch and Maj are bitwise. XOR3 and Maj are
  degree-3 polynomials and Ch is degree 2, so these outputs are expressions and cost no
  committed cells.
* 64-bit sums use three limbs of 22, 21 and 21 bits. Each limb has a carry, which is
  range-checked by lookup into [0, 64). The top carry implements the mod-2⁶⁴ reduction.

**Getting values from more than one row back.**
* For slot 1, d and h come from `D`, a packed copy of the previous row's slot-1 words.
* For slot 0, the row stores `S`, the unnormalised limb sum
  h + Σ1 + Ch (+ Σ0 + Maj for a; + d for e), computed from the row before it.
* W[t−7] arrives over a permutation bus keyed by the global row counter `g`. So does
  V = W[t−16] + σ0(W[t−15]), which the sender computes from its own row and the next one.
  The output rows get the input-state words and the final words the same way.
* Received values need no range check, because the bus forces them to equal the
  sender's expression.

**Control.** A 64-row table AIR supplies, for each row index r, eight row flags and the
round-constant limbs for both slots (`K0`, `K1`). Its rows are built from one-hot
vectors u and v, rotated by transition constraints, so the table needs no preprocessed
commitment. In this backend a preprocessed trace is a separate commitment and would add
a Merkle opening to every WHIR query. The same table also serves as the [0, 64) range
table.

**Row sequencing.** Constraints on r and `g` force complete segments 0..43, laid back
to back, followed by padding to the end of the trace. Every column with no role on a
row is constrained to zero. The intent is that every cell of an accepted trace is
determined by (input state, block); this is tested by mutation, not proven.

**Interface (bus 3).** Each message is (cid = g − r, idx, four 16-bit limbs):
* idx 0..7: input state (the chaining input);
* idx 8..23: block;
* idx 24..31: output state.

A verifier circuit chains blocks by reusing output words as the next input words. The
test consumer (`HarnessAir`) is filled from `sha2::compress512`, independently of the
AIR trace.

The maximum constraint degree is 4, with 848 constraints and 43 interactions per row.

### Columns per row (main AIR, 442)

| group | columns |
|---|---:|
| bits of a (2 slots), e (2 slots), W (2 slots) | 384 |
| partial sums S (a, e; 3 limbs each) | 6 |
| packed copies D (a, e) | 6 |
| carries (slot-1 a/e, slot-0 a/e, 2 schedule words; 3 each) | 18 |
| received limbs (V for 2 slots, W[t−7] for 2 slots); output rows reuse them for H | 12 |
| K limbs (2 slots) | 6 |
| r, g, 8 flags | 10 |

Other AIRs: the table is 64 × 18 (1,152 cells, constant). The test harness is 7 columns
× 32 rows per compression, which is a consumer-side cost, not a SHA cost.

### Alternatives considered (not built)

To compare layouts, the column count is converted into cells using the model: each
final-circuit column costs about 96 B, and each unit of c_sha costs about 6–7 B of final
layer (the slope between 12k and 24k). So one column is worth about 14 cells.

| layout | cols | cells/comp | ≈ cells + 14·cols |
|---|---:|---:|---:|
| 1 round/row (duplicate pairwise-XOR history bits) | ~350 | ~28k | ~33k |
| **2 rounds/row (built)** | **442** | **19,448** | **25.6k** |
| 4 rounds/row (d, h also in the window) | ~840 | ~17.6k | ~29k |

* **Byte or nibble lookups instead of bits:** the rotation amounts are not byte-aligned
  (28/34/39, 14/18/41, 1/8/7, 19/61/6). Each word would have to be split into pieces,
  and every Σ, σ, Ch and Maj output would be committed. The estimated cost is at least
  that of the bit layout, with many more interactions.
* **Spread (sparse) encodings** do not fit a 31-bit field for 64-bit words.

## Measurements

All runs: RAYON_NUM_THREADS=8, CPUs 8-15/24-31, `heavy` 16G cap, CPU backend, n_stack=20,
k=3, log_blowup=3. Queries per round: [210, 118, 82, 63, 51, 43, 37]. The backend's
calculator reports 268.3 total bits (LogUp 332.6, proximity 321.9).

| N | main height | cells/comp | proof B | gkr | relations | whir (auth / initial / codeword) | prove s | verify s | peak RSS |
|---:|---:|---:|---:|---:|---:|---|---:|---:|---:|
| 1,024 | 2¹⁶ | 28,288 | 874,845 | 37,544 | 48,952 | 785,644 (584,448 / 47,040 / 151,296) | 67.7 | 0.027 | 7.2 GB |
| 1,489 | 2¹⁶ | 19,454 | 881,613 | 37,544 | 48,952 | 792,364 (584,448 / 53,760 / 151,296) | 72.0 | 0.079 | 7.6 GB |
| 4,096 | 2¹⁸ | 28,288 | 1,024,317 | 44,408 | 49,432 | 926,764 (584,448 / 188,160 / 151,296) | 198.6 | 0.027 | 15.4 GB |
| 5,957 | 2¹⁸ | 19,451 | 1,031,085 | 44,408 | 49,432 | 933,484 (584,448 / 194,880 / 151,296) | 201.2 | 0.028 | 15.9 GB |

* **N = 16,384 was not run.** Peak memory doubles from 2¹⁶ to 2¹⁸ rows, so 2²⁰ rows
  extrapolates to about 45 GB, over the 16G cap.
* **Other profiles at N = 1,024:** log_blowup=1 gives 1,927,917 B; n_stack=18 gives
  919,417 B.
* **What dominates these proofs:** they are SHA-only proofs, and WHIR Merkle
  authentication paths make up most of them (584 KB, fixed by the query counts). The
  relations part is 2 × 48 B per column. These proof sizes are not the final layer.

## Tests (`selftest`, `negative`, `cargo test`)

* **Reference check.** The generator's native round function matches `sha2::compress512`
  on 10,000 random inputs.
* **Trace outputs.** Outputs read back from the trace's output rows match
  `sha2::compress512` for 1,008 compressions: 1,000 random, plus the vectors
  SHA-384 and SHA-512 of "abc", "" and a 200-byte message (two blocks, chained through
  the trace's own outputs). All digests match `sha2`.
* **Debug checker.** The backend checker (constraints, then LogUp multiset balance)
  passes on a 65,536-row trace with 1,008 compressions.
* **Single-cell mutations: 7,208 / 7,208 detected.**
  * The trace has 3 compressions plus padding.
  * Rows mutated: trace row 0; segment rows r = 0, 1, 2, 3, 9, 10, 17, 33, 38, 40, 41,
    42, 43; the first padding row; the last row.
  * Every column was mutated (bit flip, or +1).
  * Table rows 0, 7, 31, 43, 44, 63 and four harness rows were also mutated.
  * Per category: a/e/W bits 6,144, S 96, D 96, carries 288, received limbs 192, K 96,
    flags 128, r 16, g 16, table 108, harness 28.
* **Constraint-consistent edits: 10 / 10 rejected by a bus.** Each edit keeps every
  constraint satisfied, so only LogUp can reject it. The cases:
  * received V0, V1 and W[t−7] limbs;
  * K limbs;
  * received input-state and final words on the output rows;
  * a carry ≥ 64;
  * a pure range-check violation (W₇₉ bit 63 flipped, top carries re-solved to ±½ mod p);
  * a different block, with a fully consistent AIR trace, against the original consumer
    messages;
  * the same for a different input state.
* **Consistent output forgery.** Flipping an output bit in both the AIR and the
  consumer's copy is rejected by a constraint.

## Implied final layer (levers_model estimate, not measured)

`levers_fixed_point.py` calls `levers_model.fixed_point(c_sha, 2000, 2²⁰, pen, fin, m=8,
digest)`. As a check, it reproduces the model log's 12k row (444,481 B and 355,883 B).

| c_sha | penultimate SHA blocks | final cells | today (268/268, 48 B) | all levers (236/226, 42 B) |
|---:|---:|---:|---:|---:|
| 19,448 (dense, this AIR) | 10,488 / 9,015 | 2²⁷·⁶⁴ / 2²⁷·⁴³ | **502,609** | **398,173** |
| 28,288 (padded) | 11,687 / 10,461 | 2²⁸·³⁵ / 2²⁸·¹⁵ | 549,481 | 433,741 |

The model assumes 300 columns for the whole final circuit. This AIR alone has 442
columns plus 18 for the table, so it adds at least 15 KB (96 B per column above 300)
before counting any other verifier AIR.

## What remains

* **Shave rows and columns:**
  * merge the two feed-forward rows into one (−2.3% cells);
  * drop the 16 control/K columns if the backend gets periodic columns that need no
    extra commitment (−3.6%);
  * skip bits for W₇₈ and W₇₉.
* **No AIR soundness proof.** The mutation tests are sampled: 16 rows of a
  3-compression trace, plus the targeted edits.
* **Integration is not done:** wiring into the recursive verifier circuit (Merkle and
  transcript consumers) and the cid convention cid = 44·index.
* **N = 16,384** needs more than 16 GB on this backend; it should be measured on a
  bigger host or with a lower-memory profile.
