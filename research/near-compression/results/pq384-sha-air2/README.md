# SHA-512 compression AIR v2: packed digits (measured + modelled)

Crate: `research/near-compression/native/sha384-air/` (branch `lane/pq-sha384-air2`, from
`lane/pq-sha384-air`). This replaces the v1 AIR, which is in `../pq384-sha-air/` and has
442 bit columns × 44 rows. It runs on the same pinned backend and proof profile: SWIRL
stark-backend, BabyBear Ext12, SHA-384 transcript and Merkle hash. The digit width k is a
runtime parameter, `NEARPROOF_SHA_K` = 1, 2 or 3; the default is 3.

The aim is a small **final** proof, not a small SHA-only proof. The final circuit pays for
this AIR through four quantities:
* cells per compression C;
* columns;
* columns read at the next row;
* interactions.

It also pays through the backend's `max_constraint_degree`.

## Result

| | v1 (bits) | **v2 k=3** | v2 k=2 | v2 k=1 |
|---|---:|---:|---:|---:|
| main columns | 442 | **171** | 231 | 423 |
| table columns | 18 | 13 | 13 | 13 |
| rows per compression | 44 | 44 | 44 | 44 |
| **cells per compression (dense)** | 19,448 | **7,524** | 10,164 | 18,612 |
| columns read at the next row (main) | 438 | **144** | 204 | 396 |
| interactions per row | 43 | **14** | 14 | 14 |
| constraint degree | 4 | 21 | 9 | 8 |
| constraints / DAG nodes | 848 / – | 320 / 12,707 | 440 / 9,513 | 824 / 9,061 |
| **modelled final layer, z=32 + 42 B (L)** | 336,453 | **283,692 (−52.8 KB)** | 291,389 (−45.1 KB) | 330,145 (−6.3 KB) |
| modelled final layer, today's settings (T) | 400,018 | 335,116 (−64.9 KB) | 352,494 (−47.5 KB) | 393,462 (−6.6 KB) |
| SHA-only proof, N = 1,024 (measured) | 874,845 B | 828,957 B | 831,693 B | – |
| SHA-only prove time, N = 1,024 (measured) | 76.7 s | 779 s | 185 s | – |
| SHA-only prove time, N = 256 (measured) | 48.8 s | 237 s | 53.8 s | 42.3 s |

How these numbers were obtained:
* **Measured:** column, row, next-row, interaction, degree and DAG counts come from keygen
  (`AIR … next_row_cols=…` lines). Proof bytes and times come from real proofs, verified
  natively.
* **Profile and machine:** n_stack=20, log_blowup=3, 268-bit target; RAYON 8 threads on
  CPUs 8-15/24-31, shared with other agents.
* **v1 baseline:** re-run today with an identical result (874,845 B), at 76.7 s. The v1
  N = 256 time (48.8 s) was read from the terminal; it has no log file.
* **Modelled:** the "final layer" rows. They use `score_designs.py` (output in
  `score_designs.txt`), which is ext2's fixed point with the levers lane's measured laws.

**What the SHA-only proofs show:** they are dominated by the WHIR authentication paths
(584 KB, fixed). They only confirm the parts that do not depend on WHIR:
* relations: 48,952 → 36,424 B (k=3);
* GKR: 37,544 → 31,256 B;
* WHIR initial values: 47,040 → 20,160 B.

They are not a measure of the final layer.

**Chosen design: k=3** for size. k=2 is the fallback if prover time matters. k=2 costs
about 7.7 KB more in the model, and its prove time is 2.4× v1's at N = 1,024. k=3's prove
time is 10× v1's on this CPU backend (an interpreted DAG over Ext12, with d−1 = 20 cosets
in round 0).

## Design

**Rows.** The row layout is unchanged from v1:
* 44 rows per compression, 2 rounds per row;
* rows 0–1 hold the input state;
* rows 2–41 hold rounds 0–79;
* rows 42–43 hold the output state.

**Words as digits (the main lever).** Each 64-bit word is stored as `ceil(64/k)` base-2^k
digits. With k=3 that is 22 cells instead of 64.
* **Range check:** each digit has the polynomial range check ∏(v−m), of degree 8.
* **Limbs:** for additions, the three limbs (21/21/22 bits) are linear in the digits.
* **Bit signs:** Σ, σ, Ch and Maj need bits. Each is evaluated on the bit sign σ = 1 − 2b,
  which is an odd polynomial of the centred digit u = v − (2^k−1)/2: σ = u·S(u²), of
  degree 2^k − 1. XOR3 is the product of three signs, and Maj and Ch are cubic or
  quadratic in signs. The constraint degree is therefore 3(2^k − 1), which is 21 for k=3.
  No gate multiplies these constraints.
* **DAG size:** the sign form cut the DAG from 22,415 to 12,707 nodes, for the same degree.

**Bus residuals instead of stored operands.** v1 stored received values in columns so that
a constraint could use them. In v2 the constraint itself is sent as a residual message,
and the bus forces the residual to equal the sender's value:
* `a` additions (both slots): the residual is looked up against the round-constant table
  (`BUS_K`). This removes the 6 K columns.
* slot-1 `e = a − T2 + d`: the residual is matched against `d`, sent by the row two back.
  This removes D_a.
* slot-0 `e`: the residual is matched against `d − T2`, which that same row computes from
  its two-row window. This removes S_E.
* schedule: the residual is matched against W[t−7]. One message, sent with the next row,
  carries both slots. This removes the 6 received W[t−7] columns.
* feed-forward: the residual is matched against the input-state words. This removes the
  12 received IV columns. The final words of row 40 travel to the free W/V cells of
  row 42.

Interactions can read the next row in this backend, and v1's V message already did.

**Other cuts:**
* **Carries:** range-checked by polynomial, so the [0, 64) range table and its 18 lookups
  per row are gone. Signed carries use offset 4.
* **Where carries and received V live:** row x stores the values used by row x+1's
  additions, so they are read only at the current row.
* **Flags:** two flags (F_FIN, F_DA) are now derived from a single F_TAIL.

**Interactions per row (14):**
* control table;
* K table;
* interface: 3 messages (word pairs);
* state send;
* feed-forward IV residual;
* final-word receive;
* d send/receive;
* V send/receive;
* W[t−7] send/receive.

**Main columns for k=3 (171):**
* 132 digits (6 words × 22);
* S_A (3);
* DE (3);
* V (6);
* carries (18);
* r and g;
* 7 flags.

**Columns read at the next row (144):** the digits, S_A, DE, r, g, and 4 flags. Carries,
V and 3 flags (27 columns) are read only at the current row.

**Interface (bus 3).** Each message is (cid = g − r, pair index, 3 limbs of word 2m,
3 limbs of word 2m+1), with limbs split at 21/42 bits for k=3 and 22/44 bits for k ≤ 2.
* pairs 0–3: input state;
* pairs 4–11: block;
* pairs 12–15: output state.

The consumer (`HarnessAir`, filled from `sha2::compress512`) uses this format. **The
recursion lane's consumer must adopt it:** 3 limbs per word, sent as word pairs.

## Alternatives scored (`score_designs.txt`)

* **1 round per row:** this needs a duplicated history word. It scores +4.2 KB in the
  model, because the extra cells outweigh the columns saved.
* **Spread/limb lookups:** rough estimate is 2 rounds per row, about 330 columns and
  220 interactions per row. The rotation amounts (28/34/39, …) force about 15 pieces per
  word, plus spread cells and outputs. This scores −22.5 KB, well behind packed digits,
  and pays L = 26 in GKR.
* **k=1:** bits with the v2 overhead cuts. This is built and gives −6.3 KB: the cuts alone
  are worth little, and the digits are what matter.
* **k=4:** degree 45. It scores −44.7 KB: the degree cost (+37 KB of round polynomials)
  overtakes the savings in cells and columns.
* **43 rows:** merging an output row would give a further −1.0 KB. Not built.
* **Degree vs columns:** each degree unit above 4 costs 48·(3 + n) ≈ 0.9 KB (n ≈ 16
  rounds). k=3 pays +15.5 KB for degree and still wins, because cells fall 2.6× and
  columns 2.5×.

## Tests (`selftest`, `negative`, `cargo test`; logs in `logs/`)

All of the following pass for k=3, k=2 and k=1:
* **Reference check:** the native reference matches `sha2::compress512` on 10,000 random
  inputs.
* **Trace outputs:** outputs read back from the trace match `sha2` for 1,008 compressions.
  These are 1,000 random, plus SHA-384 and SHA-512 of "abc", "" and a 200-byte message.
  The 200-byte message takes two blocks, chained through the trace's own outputs. All
  digests match.
* **Debug checker:** the backend checker (constraints, then LogUp balance) passes on the
  65,536-row trace.
* **Single-cell mutations: 5,921 / 5,921 detected for k=3, and 8,315 / 8,315 each for k=2
  and k=1.**
  * Rows mutated: trace row 0; segment rows r = 0, 1, 2, 3, 8, 9, 10, 17, 33, 37–43; the
    first padding row; the last row.
  * Every column was mutated, with two in-range edits per digit (low bit and top bit
    flipped).
  * Also included: +2^s out-of-range digit edits, 10 table rows and 8 harness rows.
* **Constraint-consistent edits: 13 / 13 rejected by a bus.** Every AIR constraint still
  holds after each edit:
  * received V0 and V1;
  * W[t−7] residuals for both slots;
  * K0 and K1 residuals;
  * d and d − T2 residuals;
  * the feed-forward IV residual on rows 42 and 43;
  * received final words;
  * a different block, and a different input state, against the original consumer.
* **Rejected by constraint:**
  * a consistent output forgery (AIR digit and consumer limb both edited);
  * a carry re-solved to ±½, now caught by the polynomial range check.

There is no AIR soundness proof. Mutation testing is sampled, as it was for v1.

## Next steps

* **Prover time for k=3:**
  * a compiled or GPU constraint evaluator (the CPU backend interprets the DAG);
  * or Gruen-style zerocheck rounds, which also cut 48 B per round.
  * The prover budget decides between k=3 and k=2.
* **Interface:** the recursion lane's SHA consumer must adopt the 3-limb pair interface
  (cid = 44·index).
* **Remaining size levers (modelled):**
  * 43 rows (−1 KB);
  * a 6-word-output mode for final-block SHA-384, where only 6 output words are consumed;
  * fewer flags.
* **N = 4,096+ measurements:** not run. Prove time scales about linearly at about
  0.75 s per compression for k=3 on this CPU.
