# FAITHFUL-v4: the v4 compression AIR computes SHA-512 compression exactly

Scope: `Sha512Air4` and `TableAir4` (native `native/sha384-air4/src/air.rs`; the NV copy
`crates/recursion/src/sha384/compress4_air.rs` is generated from it by `port_nv.py` with only bus
indices, a compression-id offset and a compatibility `Layout` handle changed). This replaces
§1(c)'s `Sha512Air v2.1` / `TableAir` items and items C1–C8 of FAITHFUL.md §2(c) on
lane/pq-nv-circuit-soundness. GLUE (C9) is unchanged except that its segment stride constant
`ROWS` is now 128 (it reads `compress4_air::ROWS`).

Notation: p = 2^31 − 2^27 + 1. A 64-bit word x has three limbs split at bits 21 and 42:
x = x0 + 2^21 x1 + 2^42 x2 with x0, x1 < 2^21, x2 < 2^22 (the NV k = 3 word format, unchanged).
"σ(b)" is the bit sign 1 − 2b. Tags: TP = 1, T1 = 2, TF = 3, TY = 4, TL = 5, TV = 6, TW7 = 7.

## 1. Specification

### Sha512Air4 (83 columns, degree 9, 17 interactions)

Columns: D0[32], D1[32] (base-4 digits of the row's two slot words s0, s1, little-endian);
X[15] (aux); r; g; k1; k2 (kind digits). Bus indices: ctl, k (lookups into TableAir4), lb
(permutation, "lookback"), iface (permutation, the interface to GLUE / the test consumer).

Segment (128 rows, r = 0..127), `kind_of(r)` (air.rs) and slot words:

| rows | kind | s0 | s1 |
|---|---|---|---|
| A_j, r = j ∈ [0, 41] | A0, A1, AMid (2..39), A40, A41 | a_{2j−4} | a_{2j−3} |
| E_j, r = 42 + j | E0, E1, EMid, E40, E41 | e_{2j−4} | e_{2j−3} |
| W_j, r = 84 + j ∈ [84, 123] | Wa (0..3), Wb (4..6), Wc (7), Wd (8..31), We (32..35), Wf (36..38), Wg (39) | W_{2j+1} | W_{2j} |
| O_k, r = 124 + k | O | H'_{2k+1} | H'_{2k} |

with a_{−1..−4} = H0..H3, e_{−1..−4} = H4..H7. Kind codes (k1, k2): A* = (1, 0..4), E* = (2, 0..4),
Wa..We = (3, 0..4), Wf, Wg, O = (4, 0..2), padding = (0, 0). Selectors
sel_κ = L_a(k1)·L_b(k2) with L the Lagrange basis on {0..4} (degree 8); pad = L_0(k1),
real = 1 − pad.

Words of a window (local row l, next row n): l0, l1, n0, n1. For each, bit signs
σ_{2i}, σ_{2i+1} of digit i are u(α + βu²), u = v − 3/2 (α, β per bit), and the limbs are
l0 = Σ_{i<10} 4^i d_i + 2^20·b_lo(d_10), l1 = b_hi(d_10) + Σ_{i=11}^{20} 2^{2i−21} d_i,
l2 = Σ_{i=21}^{31} 4^{i−21} d_i with b = (1 − σ)/2. Σ0, Σ1, σ0, σ1 are products of three signs
(rotations 28/34/39, 14/18/41, 1/8/>>7, 19/61/>>6), 2σ(Ch) = σf + σg + σe(σg − σf),
2σ(Maj) = σa + σb + σc − σaσbσc, and the limbs of a sign vector are (2^w − 1)/2 − ½Σ2^b σ_b.
lhs(out, c, off)_i = out_i + 2^{w_i}(c_i − off) − (c_{i−1} − off) (no carry-in for i = 0);
reduce(S, c)_i = S_i − 2^{w_i}c_i + c_{i−1}.

Constraints (all rows):
* digits: (u² − 1/4)(u² − 9/4) = 0, u = v − 3/2; carries X[6..12]: ∏_{m<8}(c − m) = 0;
  k1, k2: ∏_{m<5}(k − m) = 0.
* padding: pad·k2 = 0; pad·x = 0 for every digit, aux, r and g column.
* unused aux: (Σ_{κ not using X[0..6]} sel_κ)·X[i] = 0 for i < 6, likewise X[6..12], X[12..15]
  (the usage sets are `roles(κ).x_lo / x_mid / x_hi`).
* sequencing: first row r = g = 0; last row k1·(r − 127) = 0; transition:
  k1'(g' − g − 1) = 0, k1'(r' − r − 1)·r' = 0, k1'(r' − r − 1)(r − 127) = 0,
  k1·pad'·(r − 127) = 0, pad·k1' = 0.

Interactions (count = Σ over the kinds with the role of sel_κ × multiplicity; "−" = receive):

| # | bus | message | count (kinds) |
|---|---|---|---|
| ctl | ctl | (r, k1, k2) | real |
| K | k | (r, Xn[0..3] − limbs(l0), Xn[3..6] − limbs(l1)) | E0, E1, EMid |
| iface | iface | (g − r, idx, l1, l0), idx = 1 (A0), 0 (A1), 3 (E0), 2 (E1), r − 80 (Wa..Wc), r − 112 (O) | A0, A1, E0, E1, Wa, Wb, Wc, O |
| S1 | lb | (g, TP, l0, l1) | A1, A40, E1, EMid, E41, O: 1; E40: 2 |
| S3 | lb | (g, T1, l1) | A0, A1, AMid, all W |
| S4 | lb | (g, TF, l0 + X[12..15]) | A0, A1, AMid, all W |
| S6 | lb | (g, TY, Σ0(n1) + Maj(n1, n0, l1) − l0, l1) | A0, A1, AMid |
| S7 | lb | (g, TL, Σ1(n1) + Ch(n1, n0, l1)) | E0, E1, EMid |
| S8 | lb | (g, TV, l1 + σ0(l0), l0 + σ0(n1)) | Wa, Wb, Wc, Wd |
| S9 | lb | (g, TW7, l0, n1) | Wb, Wc, Wd, We |
| R1 | lb | (g + o1, t1, X[0..6]); (o1, t1) = (−1, TY) A1/AMid/A40, (40, TP) A0/E0, (−40, TP) A41/E41, (−7, TV) Wc..Wf | − those kinds |
| R2 | lb | (g + o2, t2, X[12..15]); (84, T1) A0/A1/AMid, (−84, T1) all W, (−1, TL) E1/EMid/E40 | − those kinds |
| R3 | lb | (g + 43, TP, lhs(n0, X[6..9], 4) − X[0..3], lhs(n1, X[9..12], 4) − M_in + X[3..6]), M_in = Σ0(n0) + Maj(n0, l1, l0) | − A1, AMid, A40 |
| R4 | lb | (g − 43, TF, lhs(n0, X[6..9], 0) − X[0..3] − X[12..15]) | − E1, EMid, E40 |
| R5 | lb | (g + 41, TF, lhs(n1, X[9..12], 0) − X[3..6] − L_in), L_in = Σ1(n0) + Ch(n0, l1, l0) | − E1, EMid, E40 |
| R6 | lb | (g − 3, TW7, lhs(n1, X[6..9], 0) − σ1(l1) − X[0..3], lhs(n0, X[9..12], 0) − σ1(l0) − X[3..6]) | − Wc, Wd, We, Wf |
| R7 | lb | (g + o7, TP, reduce(l0 + X[0..3], X[6..9]), reduce(l1 + X[3..6], X[9..12])); o7 = 125 A0, 83 A41, 85 E0, 43 E41 | − A0, A41, E0, E41 |

Degrees: Σ/σ/Maj messages 9, Ch 6, limbs 3, counts and keys/tags 8, constraints ≤ 9
(`when_transition`/`when_last_row` add 1). Keygen: degree 9, 177 constraints, 5,848 DAG nodes.

### TableAir4 (9 columns, 128 rows)

Columns: bits b0..b6, mult_ctl, mult_k. Constraints: bits boolean; first row all bits 0;
transition: b_i' = b_i ⊕ (b_0 ∧ … ∧ b_{i−1}) (as b + c − 2bc with c the product). Offers
(i, k1(i), k2(i)) on ctl and (i, K-limbs of rounds 2(i − 42), 2(i − 42) + 1 for i ∈ [42, 82),
else 0) on k with multiplicities −mult, where i = Σ 2^t b_t and every field is the multilinear
extension of its 128 values in the bits.

## 2. Proof: constraints ⇒ semantics

**Lemma SHA-faithful (v4).** In any trace satisfying Sha512Air4 and TableAir4, with the buses
ctl, k, lb and iface balanced as multisets over F_p (total count of any message < p), the real
rows of Sha512Air4 form N back-to-back segments of 128 rows from row 0, segment s has
cid = g − r = 128 s, and its 16 interface sends are exactly the pairs
(cid, m, w_{2m}, w_{2m+1}), m = 0..15, of (H, B, compress512(H, B)), where H (pairs 0..3) and
B (pairs 4..11) are the words its IV rows and its first eight W rows hold. Padding rows are all
zero and touch no bus.

### C1. Ranges

(u² − 1/4)(u² − 9/4) has the four distinct roots u = ±1/2, ±3/2 (char p ∉ {2, 3}), i.e.
v ∈ {0, 1, 2, 3}: every digit is that integer, every slot is a 64-bit integer with exactly one
base-4 digit vector, and its limbs (C5) are its canonical 21/21/22-bit limbs. Every carry
column X[6..12] ∈ {0..7}; k1, k2 ∈ {0..4}. Hence every selector sel_κ is 0 or 1, at most one
is 1, and pad ∈ {0, 1} with pad = 1 ⇔ k1 = 0.

### C2. Row structure

* Padding (k1 = 0): pad·x = 0 zeroes digits, aux, r and g, and pad·k2 = 0 zeroes k2. Every
  interaction count is a sum of real-kind selectors, all 0 here: padding sends nothing.
* Real rows (k1 ≠ 0): the ctl lookup has count real = 1 and must hit a TableAir4 entry (C3): a
  message that is not an entry would keep a non-zero net count (its counts are all +1, < p of
  them). So (k1, k2) = code(kind_of(r)) with r ∈ [0, 128); codes not assigned to a kind
  ((4, 3), (4, 4)) are not entries and are rejected.
* Sequencing: pad·k1' = 0 ⇒ real rows form a prefix. Row 0 has r = g = 0. Between real rows,
  k1' ≠ 0 forces g' = g + 1 and either r' = r + 1 or (r' = 0 and r = 127); since r' ∈ [0, 128)
  (ctl) the case r = 127 ⇒ r' = 0. k1·pad'·(r − 127) = 0 and the last-row rule make the last
  real row have r = 127. So the real rows are N full segments, r = row mod 128, g = row index,
  cid = g − r = 128·s, distinct per segment.

### C3. TableAir4

Bits are boolean, start at 0 and step by binary increment (the carry into bit i is
∏_{t<i} b_t), so row i holds the bits of i mod 128, and the offered fields — multilinear
extensions evaluated at boolean points — are exactly ctl_entry(i mod 128) and k_entry(i mod 128).
Free multiplicities only scale them. (k_entry: the script-free check is `bus_map_consistent`
plus the honest debug-checker runs; K is the FIPS 180-4 table, copied from v2.1, whose
cube-root definition sha_carry_bounds.py already checks.)

### C4. Lookback bus

Every send carries the sender's own g and one of seven tags, and a row has one send per tag, so
(g, tag) identifies at most one sending interaction. Every receive uses key g + o with a constant
o and a constant tag per kind (table above). `bus_map_consistent` (native unit test, run on the
`roles()` table the AIR is built from) checks, for every segment row:
* every receive key lands inside the same segment (0 ≤ r + o < 128), so with g = row index
  (C2) a receive can only match a sender of its own segment;
* the multiset of (sender row, tag) over all receives equals the multiset of active sends with
  their counts (S1 of E40 has count 2: received by A39's R3 and E0's R1);
* X[0..6] of every row is pinned by exactly one of R1 or the K lookup of the window before
  (rows E_1..E_40), X[6..12] is in use exactly on rows with a check, X[12..15] exactly on rows
  with R2; the other groups are zero (unused-aux rule).
Balance with these counts ⇒ every receive tuple equals its sender's tuple as field elements.
Consequences: every stored aux value equals its sender's expression (mod p), and every residual
equals the matching sender value (mod p).

The K lookup (count 1 on E0, E1, EMid, window (E_{j−1}, E_j)) forces, limbwise in F_p,
X_{E_j}[0..3] = limbs(e_{2j−6}) + limbs(K_{2j−2}) and X_{E_j}[3..6] = limbs(e_{2j−5}) +
limbs(K_{2j−1}) for j ∈ [1, 40] (k_entry of sender row 42 + j − 1).

### C5. Bit polynomials and limbs

For a 2-bit digit, σ_lo = (1, −1, 1, −1) and σ_hi = (1, 1, −1, −1) on v = 0..3 are odd in
u = v − 3/2, so u(α + βu²) interpolates each on all four values. The digit-10 bits are
(1 − σ)/2, so the limb formulas are exact. `sign_polynomials_exact` (native) checks every digit
value and that the sign-limb forms of Σ0, Σ1, σ0, σ1, Ch, Maj and the word limbs equal FIPS
180-4 on 200 random words; the honest debug-checker runs (1,008 compressions native, the NV
suites) exercise every message.

### C6. Field equations are integer equations

Every check is a linear limb equation E_i := R_i − S_i ≡ 0 (mod p), where S_i is the sender's
value (a canonical limb or a sum of two canonical limbs) and R_i is the receiver's residual. In
E_i replace every stored cell by the integer its sender's expression takes (congruent mod p,
C4): digits are 0..3 (C1), so every limb of a word or of a Σ/σ/Ch/Maj form is an integer in
[0, 2^w), and carries are 0..7. `carry_bounds_v4.py` computes the exact range of E_i:

| equation | limb | min E | max E | max\|E\|/p |
|---|---|---:|---:|---:|
| A out: a = e + (Σ0 + Maj − d), offset 4 | 0, 1 / 2 | −14,680,064 | 10,485,762 / 20,971,522 | 0.0073 / 0.0146 |
| A in: a = e + M_in − d_in, offset 4 | 0, 1 / 2 | −14,680,064 | 10,485,762 / 20,971,522 | 0.0073 / 0.0146 |
| E out: e = (h + K) + (Σ1 + Ch) + (d + W) | 0, 1 / 2 | −12,582,913 | 16,777,215 / 33,554,431 | 0.0083 / 0.0167 |
| E in: e = (h + K) + (Σ1 + Ch) + (W + d) | 0, 1 / 2 | −12,582,913 | 16,777,215 / 33,554,431 | 0.0083 / 0.0167 |
| W: W = σ1 + (W16 + σ0) + W7 | 0, 1 / 2 | −8,388,611 | 16,777,215 / 33,554,431 | 0.0083 / 0.0167 |
| FF: O = reduce(H + final) | 0, 1 / 2 | −16,777,215 / −33,554,431 | 4,194,309 / 8,388,613 | 0.0083 / 0.0167 |

Every |E_i| < 2^25.1 < p/59, so E_i = 0 over Z: **no false carry solution exists mod p**.
Summing 2^{off_i}·E_i telescopes to out + 2^64·C_2 = Σ operands (or the FF form), so out is
the 64-bit sum mod 2^64, and with out canonical (C1) it is the SHA-512 sum. Completeness (same
script, 300 random compressions): honest carries are 3..6 (A, stored + 4), 0..5 (E), 0..3 (W),
0..1 (FF), all inside [0, 8).

### C7. The compression is FIPS 180-4 SHA-512

Fix a segment. By C4–C6:
* **Schedule.** R6 at W_j, j ∈ [7, 38], with V from S8 of window (W_{j−7}, W_{j−6}) and W7 from
  S9 of window (W_{j−3}, W_{j−2}) gives, for t = 2j + 2 and 2j + 3 (all of 16..79),
  W_t = σ1(W_{t−2}) + W_{t−16} + σ0(W_{t−15}) + W_{t−7} mod 2^64 (slots are swapped in W rows:
  s1 = W_{2j}, s0 = W_{2j+1}).
* **Rounds.** For t ∈ [0, 79] let j = ⌊t/2⌋ + 1; E_j's window checks t (out-round t = 2j − 2,
  in-round t = 2j − 1):
  * R4/R5: e_t = (h_t + K_t) + (Σ1(e_{t−1}) + Ch(e_{t−1}, e_{t−2}, e_{t−3})) + (d_t + W_t) mod 2^64,
    with h + K from the K lookup (C4), L_out from S7 of window (E_{j−1}, E_j), L_in from the
    window itself, and d + W forwarded by A_{j−1} (slot 0: A's own s0 = a_{t−4} plus W_t
    received from W_{j−1} by S3/R2) or W_{j−1} (slot 1: its s0 = W_t plus a_{t−4} received from
    A_{j−1}). So e_t = d_t + T1_t.
  * R3 at A_j with E_{j+1}'s pair (S1): a_t = e_t + Σ0(a_{t−1}) + Maj(a_{t−1}, a_{t−2}, a_{t−3})
    − a_{t−4} mod 2^64 (Y and d_in from S6 of window (A_{j−1}, A_j)). So a_t = T1_t + T2_t.
  Rounds read only earlier words, so by induction every A/E slot holds FIPS 180-4's a_t / e_t
  for the segment's H and W.
* **Feed-forward.** R7 at A0, A41, E0, E41 (H or the final pair received by R1 from A40, A1,
  E40, E1): the O rows' slots are H'_i = H_i + final_i mod 2^64, final = (a79, a78, a77, a76,
  e79, e78, e77, e76).
* **Input.** The iface sends of A1, A0, E1, E0 are pairs 0..3 = (H0, H1) … (H6, H7) (each as
  (s1, s0)); those of W_0..W_7 are pairs 4..11 = (W_{2j}, W_{2j+1}); O_k sends pair 12 + k.
So the pairs 12..15 a segment sends are compress512(H, B) of the H and B its pairs 0..11 carry.

### C8. Interface: segments ↔ consumer compressions, no injected compression

Each real segment sends its 16 pairs once (kinds A0, A1, E0, E1, Wa–Wc, O; idx 0..15 once each,
`bus_map_consistent`), keyed by its distinct cid = 128·s. Each GLUE compression receives 16
pairs with one cid (FAITHFUL.md C8, with cid' = cid − 128 for chained blocks, GLUE's stride
`ROWS` = 128). Balance with counts ±1 ⇒ a bijection between segments and consumer compressions
with equal (H_in, B, H_out). A segment without a consumer (a consistent extra segment in the
tail, a duplicated or reordered one) leaves unmatched sends; padding sends nothing (C2).

### Padding and tight heights

An all-zero row satisfies every constraint (0 is a root of every range polynomial; every pad,
unused-aux and sequencing term has a factor k1, k1', pad·x or an aux cell), and every count
vanishes on it. The transition from the last real row (r = 127, k1 ≠ 0) to a zero row
satisfies k1·pad'·(r − 127) = 0. So committing only the real rows (tight heights) is sound and
complete: the uncommitted tail is all zero by definition.

## 3. Attack audit (tests)

| attack | outcome | test |
|---|---|---|
| out-of-range digit (+4), carry re-solved to ±½ (W79 bit 63 flipped, W and E top carries ∓½) | rejected by constraint (C1) | native `negative`: `digit_out_of_range`, `carry_range_half` |
| false carry solution mod p | impossible, max\|E\| ≤ 0.0167 p | `carry_bounds_v4.py` |
| every single-cell edit of every column on rows of every kind, padding rows, table and consumer | rejected | native `negative` (mutation totals in README) |
| constraint-consistent edits of each stored value / carry (19 kinds of transfer) | rejected by the bus | native `NEGATIVE_BUS ...` |
| different block word / input state with a consistent AIR trace, original consumer | rejected (iface) | native `interface_block_word`, `interface_input_state` |
| consistent output forgery (AIR digit and consumer limb) | rejected | native `consistent_output_forgery` |
| copy of a real row in padding; consistent extra segment after the last; same after a gap | rejected | native `NEGATIVE_PAD ...`; NV `nv_faithful_fake_and_reordered_segments` |
| row kind relabel (k1/k2 to every other value) | rejected | native mutation suite (`main/kind`) |
| every cell of the NV circuit's SHA AIRs perturbed (DOF) | rejected | NV `nv_dof_*` (v4 rows labelled `sha_row0..127`) |

## 4. What remains unproven

* The consumer's cids are distinct per compression (GLUE sequencing, FAITHFUL.md C9) — imported.
* LogUp's "count of any message < p" uses the trace-height bound; the LogUp/GKR soundness error
  is §2(f)'s term (v4 has 17 interactions per row on 2^20 rows instead of 14 on 2^19).
* K-table content: `k_entry` uses the same `K` array as v2.1 (whose definition is checked by
  sha_carry_bounds.py); v4 adds no new constants.
