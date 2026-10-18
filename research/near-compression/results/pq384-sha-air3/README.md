# SHA-512 compression AIR v4: two base-4 words per row, degree 9

Lane `lane/pq-sha384-air3` (from lane/pq-recursion-sha384 @ 7cdc8c90e). Crate:
`research/near-compression/native/sha384-air4/`. NV copy: `crates/recursion/src/sha384/compress4_{air,trace}.rs`
in the `openvm-sha384` tree (patch `native/recursion/patches/openvm-recursion-sha384.patch`), generated
from the crate by `native/sha384-air4/port_nv.py`. Faithfulness argument: `FAITHFUL-v4.md`.

## Result

| | v2.1 (k = 3) [M] | **v4** [M keygen] |
|---|---:|---:|
| rows per compression | 43 | **128** |
| main columns | 171 | **83** |
| columns read at the next row | 144 | **73** |
| opened columns (main + next-row) | 315 | **156** |
| cells per compression | 7,353 | 10,624 |
| constraint degree | 21 | **9** (NvAir 8, so D = 9) |
| interactions per row | 14 | 17 |
| constraint DAG nodes | 12,718 | **5,848** |
| (d + 1) · rows · nodes per compression | 1.20e7 | 7.49e6 |
| table AIR | 64 × 13 (11 next-row) | 128 × 9 (7 next-row) |

**Modelled final layer** (`extrapolate_v4.py` = extrapolate_nv2.py with v4's census; `extrapolate_v4.txt`):

| regime | v2.1 | **v4** | change |
|---|---:|---:|---:|
| m = 3 | 326,547 | **315,811** | −10,736 |
| m = 64 | 316,351 | **304,895** | −11,456 |
| O-2 | 303,701 | **292,541** | −11,160 |
| O-2 + program cut | 299,277 | **288,117** | −11,160 |

Where it comes from (O-2 + cut): relations −19,056 B (degree 21 → 9: −11.5 KB; 159 fewer
openings: −7.6 KB), WHIR +6,888 B and stacking +1,008 B (cells 2^25.96 → 2^26.38), GKR unchanged
(L = 24: 17 interactions on 2^20 SHA rows plus NvAir's 55 on 2^18 is 2^24.95, just below 2^25).

**Latency** (`latency_model.py` of lane/pq-prover-latency, design G, adversarial, N = 32,
z_inner = z_base = 24): post-execution tail **2.67 → 2.32 s** (mid GPU, −0.35 s), 0.81 → 0.79 s
(optimistic); final-layer zerocheck + LogUp-GKR 4.97 → 2.70 GPU-s. The SHA zerocheck work falls
58 % ((d + 1) × padded rows × nodes: 22 × 2^19 × 12,718 → 10 × 2^20 × 5,848); the rest of the tail
(NvAir zerocheck, NTT and Merkle hashing of ~35 % more cells) does not move or grows a little.

**Tests:** see "Tests" below (native selftest, mutation suite, unit tests, NV suites in 48-B and
42-B + coset modes).

## 1. Objective (step 1)

`objective.py` turns an AIR shape (rows/compression, columns, next-row columns, degree,
interactions/row, DAG nodes, plus its tables) into final bytes and latency:
* bytes: `extrapolate_nv2.py` (measured laws, within 0.5 % of the 268-bit chain) with its SHA
  terms replaced — cells, COLS/ROT (48 B each in relations), D = max(NvAir 8, SHA degree)
  (48·(D+1) per round polynomial), GKR over power-of-two heights of every AIR, n from the
  tallest trace — in the four regimes m = 3, m = 64, O-2 and O-2 + program cut;
* latency: `latency_model.py` (copied verbatim from lane/pq-prover-latency) with its SHA entry
  replaced by the shape: zerocheck (d + 1)·p2(rows)/4·nodes·0.42 Ext12-mul, GKR 40 per fraction.

Validation: for v2.1 it reproduces the four published finals exactly (326,547 / 316,351 /
303,701 / 299,277 B) and the latency lane's 2.67 s tail.

Marginal values (O-2 + cut; `score_v4.py`, sweeps in the commit log): one degree unit ≈ 960 B;
one opened column 48 B; one main column at 43 rows ≈ 160–210 B; 1,000 cells/compression
≈ 3–4 KB; interactions are free in bytes up to the L thresholds (O-2 + cut: ≤ 18/row at 2^20
SHA rows). So the prize is degree and openings, as long as cells do not grow much.

## 2. Design space (step 2)

Scores (`score_v4.py` → `score_v4.txt`; [M] measured, [E] shape estimated from the layout):

| design | cells | cols | rot | deg | m3 | O-2 + cut | tail |
|---|---:|---:|---:|---:|---:|---:|---:|
| v2.1 k = 3 [M] | 7,353 | 171 | 144 | 21 | 326,547 | 299,277 | 2.67 s |
| v2.1 k = 2 [M] | 9,933 | 231 | 204 | 9 | +480 | +632 | −0.88 |
| v2.1 k = 3 with rot 40 [E] | 7,353 | 171 | 40 | 21 | −4,992 | −4,992 | 0 |
| degree 8, mixed 1/2-bit digits [E] | 12,470 | 290 | 200 | 8 | +9,648 | +8,704 | −0.76 |
| wide k = 2, W rotation removed [E] | 9,675 | 225 | 150 | 9 | −3,232 | −3,000 | −0.88 |
| Q4: (a, a, e, e) rows + 4-W rows [E] | 10,176 | 159 | 130 | 9 | −6,496 | −6,384 | −0.82 |
| T3: 3-word single-type rows [E] | 9,890 | 115 | 96 | 9 | −10,176 | −10,400 | −0.61 |
| T2 k = 3 (tall, base 8) [E] | 8,448 | 66 | 47 | 21 | −6,944 | −6,392 | +1.40 |
| **T2 k = 2 (chosen) [M keygen]** | 10,624 | 83 | 73 | 9 | **−10,736** | **−11,160** | −0.35 |

What each axis does:
* **Digit base.** A k-bit digit's bit signs have degree 2^k − 1, and Σ0/Σ1/σ0/σ1 (XOR of three
  bits) and Maj multiply three bits from different digits: degree 21 for k = 3, 9 for k = 2.
  Degree ≤ 8 needs, in every XOR3/Maj triple, a 1-bit digit: the Σ0 triples {i+28, i+34, i+39}
  need ≥ 22 single positions per word, and Maj's same-position triples over three consecutive
  words need the single sets of the word layouts to cover all 64 positions. That is ≈ 43 cells per
  a-word instead of 32 (row "degree 8" above: +8.7 KB). Bits of degree ≤ 3 also cannot be packed
  denser than 2 per cell (a degree-d polynomial basis on a 2^k-point domain must contain the k
  coordinate functions; for d = 2, k = 2 and d = 3, k = 3 this forces the digit to be affine in its
  bits, contradicting v² ∈ span). So the polynomial floor is 32 cells/word at degree 9.
* **Splitting high-degree checks with committed columns.** The degree is in the bit products,
  not in the carry equations; committing an intermediate (e.g. ROTR28 ⊕ ROTR34) costs a whole word
  of digits per function. Not competitive.
* **Lookups for Σ/Ch/Maj.** Interactions are nearly free in bytes, but a lookup's output must be
  a cell (or absorbed by a per-chunk carry cell), and the rotations are not chunk-aligned (Σ1 and
  σ1 need 20–24-bit table inputs at nibble granularity). Every variant costs ≥ 100 cells/round
  against 96 for base-4 polynomials with free outputs.
* **Limb width.** p < 2^31 forces three limbs per 64-bit word; v4 keeps the 21/21/22 split (the
  interface and NV word format are unchanged; digit 10 straddles bit 21 and contributes its two
  bits, each cubic in the digit).
* **Row layout — the main lever.** Openings are per column and cost 48 B (96 B if read at the
  next row), so for a fixed number of digit cells a tall, narrow AIR opens fewer columns. Maj and
  Ch need three consecutive words of one type in a two-row window, so the narrowest layout is
  two words of one type per row (T2): A rows (a pairs), E rows (e pairs), W rows (schedule pairs).
  All rows share the same 64 digit columns, so the AIR opens 64 + 64 digit columns instead of
  132 + 132 (v2.1) or 128 + 128 (Q4). The cost is cross-row data: every 64-bit value a check needs
  from outside its window is stored as three limbs. T2 needs 15 aux cells per row after three
  tricks: (i) every addition is a bus residual matched by exactly one sender, so a remote
  operand costs 3 cells whether it is stored or matched; (ii) d + W is pre-summed by the row that
  holds one of them (A forwards slot 0, W forwards slot 1, balancing the load to 15 per row type);
  (iii) K is folded into the stored h limbwise (h + K, checked by a lookup against the control
  table), so the round constant costs no cell. Copying working variables to avoid next-row reads
  (the "copy" option) costs a full word of digits per copy per row and loses to rotation by ~3×.
* **Message schedule in a separate AIR.** A separate W AIR has its own columns (and rotated
  columns), so it adds openings; with one word per row it needs three transfers per word. Rejected
  in favour of W rows in the shared column set.
* **Latency trade-off.** A tall single AIR evaluates the union of all row types' constraint DAGs
  on every row (each row computes Σ0, Σ1, σ0, σ1 on its slots and Maj, Ch on its window), and it
  has 3× the rows. Q4 (four words per row) keeps 2^19 rows and gets −0.82 s, but only −6.4 KB;
  T2 gets −11.2 KB and −0.35 s; T3 sits in between (−10.4 KB, −0.61 s, estimate). Given the
  300 KB gate, v4 takes T2.

## 3. Design (step 3)

Segment of 128 rows (r = 0..127): A_j (r = j, 42 rows: a_{2j−4}, a_{2j−3}), E_j (r = 42 + j:
e_{2j−4}, e_{2j−3}), W_j (r = 84 + j, 40 rows: W_{2j+1}, W_{2j} — slots swapped so that both
forwards use s0), O_k (r = 124 + k: H'_{2k+1}, H'_{2k}). Columns: two 32-digit slot words,
15 aux, r, g, two kind digits (k1, k2) whose Lagrange products select one of 18 row kinds
(degree 8); the kind is pinned by the control lookup (r, k1, k2). Exact equations, per-kind roles
and interaction table: FAITHFUL-v4.md §1.

Checks (window = local row, next row; outputs always in the next row):
* **E rows** (rounds 2j − 2 out, 2j − 1 in, outputs E_{j+1}): e = (h + K) + (Σ1 + Ch) + (d + W),
  with h + K stored (checked by the K lookup in the window before), Σ1 + Ch of the out-round
  received from the window before, d + W received as the residual's match; carries stored.
* **A rows**: a = e + (Σ0 + Maj − d), with (Σ0 + Maj − d) of the out-round and d of the in-round
  received from the window before, e matched against the E row's pair.
* **W rows**: W_t = σ1(W_{t−2}) + V + W_{t−7}, V = W_{t−16} + σ0(W_{t−15}) received from 7 rows
  back, W_{t−7} pair matched from 3 rows back.
* **Feed-forward** on A0, A41, E0, E41 (rows with no round check): the slot pair plus the received
  H or final pair, reduced with stored carries, is matched against the O row's pair (so the O
  rows, which only hold canonical digits and send interface pairs 12..15, have no aux).
* **Padding**: all-zero rows satisfy everything and touch no bus (zero-valid; safe with
  tight heights).

**Interface** (bus 3, documented change): messages are unchanged —
(cid, pair, 3 limbs of word 2m, 3 limbs of word 2m + 1), limbs split at 21/42, pairs 0–3 input
state, 4–11 block, 12–15 output, all 16 sent once per compression. **cid = 128 · compression
index** (was 43), so the consumer's stride constant is 128 (`compress4_air::ROWS`; GLUE reads it).
The control/K table is `TableAir4` (128 rows, 9 columns: 7 counter bits and 2 multiplicities;
fields are multilinear extensions of the bits, no preprocessed commitment). `max_constraint_degree`
must be ≥ 9 (NV: 9).

## 4. Tests (step 3/4)

Native crate (`logs/selftest-v4.log`, `cargo test`):
TESTS_NATIVE

NV crate (`logs/nv-tests-48.log`, `logs/nv-tests-42.log`):
TESTS_NV

## 5. Files

* `objective.py` — byte/latency objective; `score_v4.py` / `score_v4.txt` — design space;
  `extrapolate_v4.py` / `extrapolate_v4.txt` — final bytes for v4 in the four regimes.
* `carry_bounds_v4.py` — exact limb-equation ranges and honest carry ranges (FAITHFUL-v4 C6).
* `FAITHFUL-v4.md` — the faithfulness argument.
* `native/sha384-air4/` — AIR, trace generator, reference, selftest / negative / prove, `port_nv.py`.
* `native/recursion/patches/openvm-recursion-sha384.patch` — NV tree with v4 (new
  `sha384/compress4_{air,trace}.rs`; circuit, hash, GLUE and tests switched; v2.1 files kept).
* `prover-latency/latency_model.py` — verbatim copy from lane/pq-prover-latency.

## 6. Open points

* The SHA trace is 2^20 rows at the fixed point (128 rows × ~6.5k compressions); n grows by one
  (+480 B, included) and the GPU zerocheck works on twice the padded height of v2.1.
* O-2 + cut sits at 2^24.95 interactions: one more interaction per row of the SHA AIR (18) still
  fits, 19 would cost L = 25 (+2.5 KB).
* Latency: the union DAG (5,848 nodes) is evaluated on every row; a two-AIR split (A/E rows and W
  rows) would cut it by ~15 % at +1.3 KB. Q4 (four words per row) is the latency-first alternative
  (−0.82 s, −6.4 KB).
