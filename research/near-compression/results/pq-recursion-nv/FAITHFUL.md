# NV-faithful: the narrow verifier circuit arithmetises the native SWIRL verifier

Lane `lane/pq-nv-circuit-soundness`, 2026-10-18. **Audited version: lane/pq-recursion-sha384 @
3c9d479ab** (patch `native/recursion/patches/openvm-recursion-sha384.patch`, unified backend
`stark-backend-unified.patch`). The fixes below are on this branch only (not merged into
lane/pq-recursion-sha384). Target statement: Lemma 7.1 (F1–F6) of
`lane/pq-final-soundness` `final-soundness/PROOF.md` @ ae0ae8a7b.

Code: `crates/recursion/src/nv/` in the openvm-sha384 tree. New on this branch:
`faithful_dof.rs` (perturbation harness), `faithful_tests.rs` (ALU/BIND/app tamper, DOF, LogUp
counts), `faithful_sha_tests.rs` (SHA/GLUE), `faithful_tr_tests.rs` (transcript/Merkle).
Scripts: `scripts/sha_carry_bounds.py` (exact carry/residual bounds, 1,319 checks),
`scripts/run_faithful.sh` (everything; 48 B and 42 B + coset-leaf modes).

## 0. Result

**Lemma NV-faithful(i) (proved here for the branch head, modulo §6).** Let vk_i be NV_i's key,
P_i its program table (P_1 = app-verifier program, P_i = P_NV for i ≥ 2). Let T be a trace of
NV_i's four AIRs (NvAir, Sha512Air, TableAir, ByteAir) that satisfies every constraint on every
row (zero rows included), whose buses balance **mod p**, with program columns P = P_i and public
value pv0. Define

* dec_i(T) = π_{i−1}: each proof field is the c-cell of the program row that loads it (Load,
  LoadF, LoadBit for index/PoW bits, Horn wit for round-0 opened rows, the cells pushed by
  `load_commit`, Merkle sibling Loads). The row of each field is fixed by P_i, so dec_i is a
  fixed coordinate projection: deterministic, straight-line. With the multiproof lever the
  per-query sibling cells are re-encoded into the native multiproof stream.
* pv_i(T) = x_{i−1}: the child public-value cells (LoadF rows observed by Unit1), and level(x_i)
  = pv0.

Then:

* **(F1)** V′_{i−1}^{SHA-384}(vk_{i−1}, x_{i−1}, π_{i−1}) = 1, for the native verifier of the
  unified backend with the **current** transcript (not yet T\*, §2(d)(vi)), WHIR-Y, the ×15
  sampler, multiproof, coset leaves, 42-B digests and PoW, run with vk_{i−1}'s constants; every
  SHA-384 output used equals the true SHA-384 output (§2(c)). Exception: with the multiproof
  lever, re-encoding fails only if T itself contains a Merkle-compression collision, which is
  then read off T (additive ε_coll, §2(e)).
* **(F2)** vk_{i−1} (pre-hash, params, heights, constraint DAG) is a constant of P_i; the
  program/app binding check against P_NV (child level ≥ 2) or P_1 (child level 1) is ordinary
  ALU code of P_i (§2(b) B-4).
* **(F3)** level(x_i) = level(x_{i−1}) + 1 and the app-mode flag = [level(x_{i−1}) ≠ 1]
  (levels ≥ 2; level 1 exposes the constant 1). **The base-statement digest is not passed
  through: NV has one public value (gap G1, §6).**
* **(F4)** mod-p balance gives the intended multiset / subset semantics (§2(f)).
* **(F5)** all-zero rows satisfy every constraint and emit no interaction (§2(c), §1.1, §4).
* **(F6)** every SHA-384 evaluation that (F1) uses is a GLUE job whose compressions are 43-row
  segments of Sha512Air in T (§2(c) C8, §2(d), §2(e)).

**Additive error.** The lemma itself is deterministic given mod-p balance. The bus argument's
error (protocol Lemma 3.1, here with ℓ_msg = 15, N ≤ 2^25.05) is
**ε_LogUp ≤ ℓ_msg·N²/(2|F|) + 2N/|F| ≈ 2^−317.9**, |F| = p^12. With the multiproof lever add
ε_coll (a Merkle-compression collision found by the prover; straight-line extractable from T).

**Completeness.** For an honest π_{i−1} accepted by the native verifier, `NvCircuit::generate`
produces a satisfying trace (debug-checked on Fib, interactions, all levers, ×15, tight
heights, app rows; 48 B and 42 B). Native resamples when the ×15 sampler draws p − 1, NV
rejects: completeness error ≤ (#queries)/p.

(Sub-sections §1(c)–§2(e) were written per role and use the names F-c1 = B4, B-tr1 = B5,
B-tr2 = B6.)

**Soundness bugs found at 3c9d479ab (all fixed on this branch with tests, §5):**
B1 ALU op relabel via a fractional B-field range check (Zero→Bit, Mul→Nop);
B3 base-field loads with free extension coefficients (PoW check vacuous, child PVs);
B4 42-B commitment tail with two framings (transcript not a function of π);
B5 squeeze job ids free (two squeezes share an id);
B6 static transcript job op not bound to the program (commit ↔ flush relabel);
B2 (program generator) the child's LogUp trace-height constraint was not checked.
Each of B1, B3–B6 makes the circuit accept a trace whose child proof the native verifier
rejects (or, B4/B6, whose challenges are not the native ones); tests demonstrate acceptance at
3c9d479ab.

## 1. Specification of the NV relation

AIRs and heights at the fixed point: NvAir 2^18 × 70 (deg 8, 52 interactions/row), Sha512Air
2^18 × 171 (deg 21 at k = 3, 14 interactions/row), TableAir 64 × 13, ByteAir 65,536 × 5. Buses:
slot, job, digest, mem, bind, acc, bind2, acc2 (NvAir); ctl, k, lb, iface (SHA), word (GLUE ↔
compression words), byte (byte-pair table), sample, t.word (HASH ↔ SAMP). Public values: NvAir
pv0 = level; the other AIRs none.

### 1.1 NvAir: common columns, role layout, padding

NvAir (70 columns = 11 common + a 59-column pool) has one row per role row. The pool is
reinterpreted per role.

| col | name | meaning |
|---|---|---|
| 0–4, 6 | `ka kb kg kh ks kc` | role flags: ALU, BIND, GLUE, HASH, SAMP, app-binding (APPB) |
| 5 | `y` | row index on role rows; 0 on padding rows |
| 7–10 | `P0..P3` | program words; zero off ALU rows |

Constraints (every row, wrap-around window (h−1, 0) has `is_transition = 0`):

* C1 each flag boolean; `ksum = Σ flags` boolean (at most one role).
* C2 `first_row: y = 0`; `transition: ksum(next)·(y' − y − 1) = 0`; `(1 − ksum)·y = 0`.
* C3 padding rows are all-zero: `(1 − ksum)·x = 0` for every pool column x.
* C4 `(1 − ka)·P_j = 0`, j = 0..3.
* C5 role order: `stage = kb + 2kc + 3kg + 4kh + 5ks + 6(1 − ksum)`;
  `transition: Π_{i=0..6}(stage' − stage − i) = 0`. Since stage ∈ {0..6}, the difference lies in
  [−6, 6] and the product forces it into {0..6}: stage is non-decreasing, so the roles occupy
  contiguous regions in the order ALU < BIND < APPB < GLUE < HASH < SAMP < padding.

Public values: **one**, `pv0 = level` (§5, gap G1).

Interactions: each role's interactions are collected separately and merged into shared slots
per bus (`merge_push`): message = Σ_role flag·message_role, count = Σ_role count_role (every
role count already carries its flag), weight = max. Because the flags are boolean and at most
one is set (C1), the merged interaction on a row equals the active role's interaction, and
counts on inactive roles are 0. 52 interactions per row after merging.

### 1.2 ALU role (rows [0, 2^prog_log))

Pool view `AbCols`: `a[12] b[12] c[12]` (Ext12 coefficient vectors, basis 1, X, …, X¹¹ of
F[X]/(X¹² − W)), `h[8] g[4]` (opcode halves, op = 8·hi + lo), `wit`, `mult`, `rx ry rz`.

Program words (isa.rs): `P0 = A`, `P1 = B + op·2^20` (B < 2^20; for `Data` rows P1 is raw),
`P2 = k1`, `P3 = k2`. Selector `s(op) = ka·h[op mod 8]·g[op div 8]` (degree 3).
`opv = Σ_{op≠Nop} s(op)·op`, `bfield = P1 − opv·2^20`.

Constraints:

* A1 `ka·g(g−1) = 0`, `ka·(Σg − 1) = 0`; same for h. (one-hot halves)
* A2 result: `(ka − free)·(c_k − e_k) = 0`, k = 0..11, where
  `free = s(Load)+s(Smp1)+s(Smp12)+s(Acc)+s(Dig)+s(PowChk)+s(Acc2)+s(LoadBit)+s(LoadF)` and
  `e = (s(Mul)+s(Horn))·a·b + s(Add)(a+b) + s(Sub)(a−b) + s(DblAdd)(2a+b) + s(MulAddA)(a·b+a)
  + s(copy)·a + s(Const)·P0·1 + s(ConstX)·P0·X + s(Horn)·wit·1`,
  copy = {Unit1, UnitW, UnitWT, Unit12, Bit, Pv, UnitWS4, UnitWS2}. All other ops (Nop, Anchor,
  Job, Zero, NodeJob, Data, the undefined code 31) have e = 0, i.e. c = 0. Codes 0..30 are
  defined on this branch (29 = LoadF, 30 = UnitWT are new).
* A3 `s(Zero)·a_k = 0` (k = 0..11); `s(Bit)·a_k = 0` (k ≥ 1), `s(Bit)·a0(a0 − 1) = 0`;
  `s(Smp1)·c_k = 0` (k ≥ 1); `s(LoadBit)·c0(c0−1) = 0`; `(s(LoadBit)+s(LoadF))·c_k = 0` (k ≥ 1)
  [LoadF: this branch]; `s(Pv)·(a0 − pv0) = 0`; `s(Dig)·(2 − bfield)·c_k = 0` (k = 6..11).
* A4 B-field range (all ALU rows except Data): `nd = ka − s(Data)`;
  `nd·(bfield − rx − 256ry − 65536rz) = 0`; lookups `(rx, ry)` and `(rz, 16rz)` on the byte-pair
  bus with count nd [the second was `(16rz, 0)` at 3c9d479ab: bug B1].

Buses (count semantics: + = send / lookup, − = receive / key):

| bus | message | count | role |
|---|---|---|---|
| mem (lookup) | `(y, c)` | `−ka·mult` (key, weight 0) | memory write of row y |
| mem | `(P0, a)` | `Σ_{op reads A} s(op)` ∈ {0,1} | operand A read |
| mem | `(bfield, b)` | `Σ_{op reads B} s(op)` ∈ {0,1} | operand B read |
| slot ×12 (k) | `(chan, P2 + [Smp12]k, key2_k, kind, v0, v1, v2)` | send_k − recv_k | units (chan 1), samples (chan 0, received), anchors (chan 2), PoW word (chan 3, received) |
| job | `(P2, P0, 1)` | `s(Job) + s(NodeJob)` | leaf/node job start, tag P0, Merkle flag 1 |
| digest ×2 (h) | `(P2, P3 + h, c[6h..6h+6])` | `−s(Dig)` (h = 0), `−s(Dig)(bfield − 1)` (h = 1) | digest pairs |
| byte (lookup) | `(rx, ry)`, `(rz, 16rz)` | `nd` | B range |
| bind2 | `(y − app_base, P0..P3)` | `s(Data)` | app table rows → APPB |
| acc2 | `(c, P0)` | `−s(Acc2)` | APPB total + pinned length |
| bind | `(y, P0..P3)` | `ka` | every ALU row → BIND |
| acc | `(c, P0)` | `−s(Acc)` | BIND total + pinned length |

Slot details (isa.rs comments are normative): `chan = Unit1+UnitW+UnitWS*+Unit12+Horn+Job + 2·Anchor
+ 3·PowChk`; `kind = 2·(UnitW+UnitWS*) + KIND_SAMPLE·(Smp1+Smp12)`; `key2` = `P3+k` (Unit12),
`P3+2k` (UnitW), `P3+2k+12·b0` (UnitWS*: Merkle left/right by the bit read at B), `k` (Job), `P3`
(Unit1, Horn; k = 0); values: `c_k` (Unit12/Smp12), `c0` (Unit1/Smp1), `wit` (Horn), `(bfield, 0)`
as the byte length (Job, k = 0, 1), `(P0 = t_start, bfield = count, P3 = tag)` (Anchor; the tag is new, fix B6), `c[3k..3k+3]` limbs
(UnitW k < 2 or < 4 when B = 4, UnitWS4 k < 4, UnitWS2 k < 2, UnitWT k < 2 with the second unit of
kind UNIT_HALF = 3, fix B4), `c0..c2` (PowChk, received).

### 1.3 BIND and APPB roles

Pool view `BindCols`: `e1a e1b e2 acc` (Ext12), `pc0[4] pc1[4]`, `ya yb bl`. Row t covers ALU
rows y = 2t, 2t+1; `y2 = ya + 512·yb`. `τ = 1 + X`, `ptau(pc) = Σ_j τ^j pc_j`,
`wp = e2·(e1a·ptau(pc0) + e1b·ptau(pc1))`. For role flag k ∈ {kb, kc} (same code, buses
(bind, acc) resp. (bind2, acc2)):

* B1 `k·bl(bl − 1) = 0`; `last_row: k·(1 − bl) = 0`; `transition: k·(bl − (1 − k')) = 0`.
* B2 entry (`transition, k'(1 − k)`): `y2' = 0`, `acc' = 0`.
* B3 `transition, k·k'`: `y2' = y2 + 2`, `acc' = acc + wp`.
* B4 lookups: `(ya/2, 0)` byte (so ya ∈ {0, 2, …, 510}); mem `(ya, e1a)`, `(ya + 1, e1b)`,
  `(yb + 512, e2)`.
* B5 receive `(y2 + h, pc_h)` on bind (h = 0, 1); send `(acc + wp, y2)` on acc with count `k·bl`.

The E tables: `E1[x] = L_{x mod 2^l}(r0)·eq(r_1..r_{9−l}, x ≫ l)` at rows [0, 512) and
`E2[x] = eq(r_{10−l}.., x)` at rows [512, 512 + 2^(prog_log−9)) are ALU `Mul` rows that the
program fills once the child's batch point r is sampled (`bind_child_program`). At level 1 they
are `Nop` (zero).

<!-- (fork section)  §1 (SHA/GLUE part) and §2(c), §3(c), §5(c) of FAITHFUL.md. Audited version: 3c9d479ab. -->

## 1(c). Specification: SHA-384 subsystem (Sha512Air v2.1, TableAir, ByteAir, GLUE role)

Notation: p = 2^31 − 2^27 + 1. Digit width k = 3 (`NEARPROOF_SHA_K` default). A 64-bit word x
is held as nd = 22 little-endian digits (21 of 3 bits and a top digit of 1 bit), and as three
limbs split at bits 21/42: x = l0 + 2^21 l1 + 2^42 l2, l0, l1 < 2^21, l2 < 2^22 (`wl`).
"σ(v)" is the bit sign 1 − 2b.

### Sha512Air (171 columns, degree 21, 14 interactions/row; `sha384/compress2_air.rs`)

Columns per row: digits of six words a0, a1, e0, e1, w0, w1 (132); S_A (3); DE (3); V0, V1
(3 + 3); carries c1a, c1e, c0a, c0e, cw0, cw1 (6 × 3); r; g; flags F_IV, F_ROUND, F_SCHED,
F_OUT, F_TAIL, F_S01, F_S2. Derived: real = F_IV + F_ROUND + F_OUT, pad = 1 − real,
row0 = F_IV·(1 − r), F_FIN = F_TAIL·(41 − r), F_DA = F_IV + F_ROUND − F_TAIL.

Segment layout (43 rows per compression, r = 0..42): rows 0, 1 hold the input state
(row 1: a1 = H0, a0 = H1, e1 = H4, e0 = H5; row 0: a1 = H2, a0 = H3, e1 = H6, e0 = H7) and
in their W slots the outputs H'2, H'3 (row 0) and H'6, H'7 (row 1); rows 2..41 hold rounds
2(r−2), 2(r−2)+1 (slot 0, slot 1); rows 2..9 take W from the block, rows 10..41 from the
schedule; row 42 holds H'1, H'0, H'5, H'4 in a0, a1, e0, e1.

Constraints (all rows unless gated):
* digits: ∏_{m<2^s}(v − m) = 0 (s = 3, or 1 for the top digit); carries: ∏_{m<8}(c − m) = 0.
* zero rules: pad·(a, e digits) = 0; (1 − F_ROUND − F_IV)·(w digits) = 0;
  (1 − F_ROUND(n) − F_OUT(n) − row0)·(c1a, c1e, c0a, c0e) = 0; (1 − F_SCHED(n))·(cw, V) = 0;
  pad·(r, g, flags) = 0.
* sequencing: first row r = g = 0; last row (r − 42)·real = 0; transition:
  real(n)(g' − g − 1) = 0; real(n)(r' − r − 1)·r' = 0; pad(n)·real·(r − 42) = 0;
  (1 − r')·F_IV(n)·(r − 42) = 0; pad·real(n) = 0.
* S_A(n) = real(n)·(e0_l + Ch(e1_n, e0_n, e1_l)) + Σ1(e1_n) + Σ0(a1_n) + Maj(a1_n, a0_n, a1_l)
  and DE(n) = real(n)·e1_l, limbwise, on every window (cyclic).
* Σ/σ/Ch/Maj are evaluated on bit signs: σ_t(v) = u·S_t(u²), u = v − 7/2 (interpolated, degree
  7 per digit); XOR = product of signs; 2·σ(Ch) = σf + σg + σe(σg − σf); 2·σ(Maj) =
  σa + σb + σc − σaσbσc; limbs of a sign vector: (2^w − 1)/2 − ½Σ 2^b σ_b.

Residuals (window l, n): with lhs(out, c, off)_i = out_i + 2^{w_i}(c_i − off) − (c_{i−1} − off)
* res_a0 = lhs(a0_n, c0a, 0) − (S_A_l + W0_n); res_a1 = lhs(a1_n, c1a, 0) − (DE_l + Σ1(e0_n) +
  Ch(e0_n, e1_l, e0_l) + W1_n + T2), T2 = Σ0(a0_n) + Maj(a0_n, a1_l, a0_l);
* res_e0 = lhs(e0_n, c0e, 4) − a0_n; res_e1 = lhs(e1_n, c1e, 4) + T2 − a1_n;
* res_w0/1 = lhs(w_n, cw, 0) − (σ1(w_l) + V_l);
* res_out[q] = lhs(slot_q(n), carry_q, 0) − slot_q(l) (row 42); res_row0 = the four H'
  equations of rows 0/1 against a0_l, a1_l, e0_l, e1_l.

Interactions (count semantics: + = send, − = receive):
| bus | message | count |
|---|---|---|
| ctl (lookup) | (r, 7 flags) | +real |
| k (lookup) | (r, res_a0, res_a1) | +F_ROUND(n) |
| iface (perm) | (cid, idx_a, a1, a0) and (cid, idx_a + 2, e1, e0), idx_a = row0 + 12·F_OUT | +(F_IV + F_OUT) |
| iface | (cid, (F_ROUND − F_SCHED)(r + 2) + F_IV(13 + 2r), w0, w1) | +(F_ROUND − F_SCHED + F_IV) |
| lb (perm) | (g, ST, a0, a1, e0, e1) | +(F_IV·r + F_FIN) (rows 1, 40) |
| lb | (g, DA, a1, d − T2), d − T2 = a0_l − Σ0(a1_n) − Maj(a1_n, a0_n, a1_l) | +F_DA (rows 0..39) |
| lb | (g, V, w0 + σ0(w1), w1 + σ0(w0_n)) | +F_S01 (rows 2..33) |
| lb | (g, W7, w1, w0_n) | +F_S2 (rows 6..37) |
| lb | (g − 40, ST, res_out) | −F_OUT(n) |
| lb | (g + 40, ST, res_row0) | −row0 |
| lb | (g − 1, DA, res_e1, res_e0) | −F_ROUND(n) |
| lb | (g − 7, V, V0_l, V1_l) | −F_SCHED(n) |
| lb | (g − 3, W7, res_w0, res_w1) | −F_SCHED(n) |

with cid = g − r (+ cid_offset = 0).

### TableAir (13 columns, 64 rows) and ByteAir (5 columns, 65,536 rows)

TableAir: one-hot u[4], v[4], w[3] (boolean, sum 1), first row u0 = v0 = w0 = 1, transitions
advance u cyclically, v when u wraps, w when u and v wrap, so row i has index i mod 48. It
offers (ctl_entry(index)) and (k_entry(index)) with free multiplicities (−mult). ctl_entry(i) =
(min(i, 42), flags of row min(i, 42)); k_entry(i) = (i, K limbs of rounds 2(i+1)−4, 2(i+1)−3)
for i + 1 ∈ [2, 41], else (min(i, 42), 0).

ByteAir: columns x, y, z, inv, mult; z bool, z(x − 255) = 0, (x − 255)·inv = 1 − z; first row
(0, 0); x' = (x + 1)(1 − z), y' = y + z; last row (255, 255); offers key (x, y) with mult.
A single byte v is looked up as (v, 0).

### GLUE role (59 pool columns of NvAir, flag kg; `nv/glue.rs`)

One row per pair of message words of a job compression; row q ∈ 0..7 (bits q0, q1, q2) of
block k holds bytes 16q..16q+15 of the block (b[0..16], big-endian), `carry`/`carry2` = the next
row's b0/b1. Columns: start, job, q[3], cid, blk0, last, end, act, phase, uidx, b[16], carry,
lo[4] (low a5 = 5 bits of bytes 5, 13 and low a2 = 2 bits of bytes 2, 10), ulo[4] (same for the
unit views b1..b8, b9..carry; node42 rows 3–5: the shift-2 views), p[4] (padding-start per felt
slot), wd[2] (word unit over slots (0,1)/(2,3)), zm[4] (felt = p − 1), s[6] (state pair), nd
(node job), carry2, lo6, tr (Merkle job), hp (42-B tail in slot 2), hs (tail seen).

Constraints (all multiplied by kg): booleans for start, blk0, last, end, nd, tr, hp, hs, q, p,
wd, zm; end = last·[q = 7]; act = (1 − nd)(1 − hdr − end), hdr = blk0·[q ≤ 1]; nd ⇒ blk0 ∧ last;
start ⇒ q = 0, blk0, phase = uidx = hs = 0; hp = 0 unless 42-B mode. Slots s = 0..3 (bytes
b1..b4, b5..b8, b9..b12, b13..b15‖carry), with phb the running padding flag and
d_s = act(1 − phb) − p_s − [s = 2]hp:
* p_s ⇒ phb = 0, act, slot = (0x80, 0, 0, 0); act·phb ⇒ slot = 0; hp ⇒ phb = 0, act, wd[1] = 0,
  slot bytes 2, 3 = (0x80, 0);
* felt slot (is_felt = d_s − wd): lookup byte (0x78 − a3 − 1 + zm), zm(0x78 − a3) = 0,
  zm(a0 + a1 + a2) = 0; receive slot (1, job, uidx, kind, value) with
  kind = 2·wd + 3·hp + 0·felt **(after fix F-c1; before: 2·(wd + hp))**, value = felt |
  limbs_from_bytes(8-byte view, ulo) | tail view (b9, b10, 0…); count d_s (+hp);
* wd ⇒ d_{2w} = d_{2w+1} = 1; uidx += d_s + 2hp; phase' = phb.
* framing (prefix jobs): block 0 rows 0, 1 = the 32-byte prefix; end row: b0..b12 = 0,
  b13..b15 = (33 + 4·uidx − 6·hs)·8 (big-endian); [q = 6] ⇒ last = phase_after; job bus receive
  (job, b0 of block 0 row 2 (the tag byte) | 256 for node jobs, tr) at that row (row 0 for node).
* node jobs: row 0 bytes 0..7 = node prefix; 48 B: word 13 = 0x80‖0, words 14, 15 = 832; units
  word 2q → index 4q − 2, word 2q+1 → 4q (kind 2); 42 B: byte 92 = 0x80, bytes 93..111 = 0, words
  14, 15 = 736, units L0..L4 aligned, L5 = tail (b0, b1 of row 3), R0..R4 at byte shift 2, R5 =
  tail (b10, b11 of row 5).
* sequencing within a job (cont = kg·kg'·(1 − end)): job, nd, tr constant; q' = q + 1 mod 8;
  blk0' = blk0·[q ≠ 7]; cid' = cid + 43·[q = 7]; phase', uidx' carried; b0' = carry, b1' =
  carry2; last' = last unless q = 7; start' = 0; hs' = hs + hp. Region: kg ∧ kg' ∧ end ⇒
  start'; kg ∧ ¬kg' ⇒ end; ¬kg ∧ kg' ⇒ start'; last row ⇒ end.
* state: block 0, q < 4: s = SHA-384 IV pair q.
* iface receives: (cid, 4 + q, w0, w1) count kg; (cid, q, s) count kg(1 − q2);
  (cid − (1 − q2)·43, 12 + (q mod 4), s) count kg((1 − q2)(1 − blk0) + q2·last).
* digest send: (job, q mod 4, s′) count kg·last·q2·(1 − q0q1) (rows 4, 5, 6 of the last block),
  s′ = s except, in 42-B mode with tr = 1 on row 6: s′3 = s′4 = 0, s′5 = s5 − lo6.
* lookups: (b_{2k}, b_{2k+1}) for k < 8; (lo·2^{8−a5}, lo·2^{8−a2}) pairs for lo and ulo;
  (lo6·4, 0).


<!-- (fork section)  tr-fork section: §1 (HASH/SAMP spec), §2(d), §2(e), audit/bugs for (d)(e). Audited: 3c9d479ab
     (patch openvm-recursion-sha384.patch), unified backend stark-backend-unified.patch. -->

## §1 (part) — HASH and SAMP roles of NvAir: columns, constraints, buses

Notation: `g(x) = kh·x` on HASH rows, `ks·x` on SAMP rows; `nkh`, `nks` are the next row's flags;
"transition" constraints are gated by `is_transition`. All interactions are role-gated and merged
into shared slots by `merge_push` (message = Σ role·message, count = Σ role-gated counts; the
roles are mutually exclusive, `Σk ∈ {0,1}`, so on every row the slot carries exactly the active
role's message and count). Rows of one role are contiguous (monotone stage), HASH before SAMP.

### Buses touched (all `PermutationCheckBus` except `byte`, a `LookupBus`)

| bus | message | producers (+) | consumers (−) |
|---|---|---|---|
| slot, chan 1 (unit) | `(1, job, uidx, kind, v0, v1, v2)`, kind 0 = felt (v0), 2 = word (3 air2 limbs) | ALU `Unit1/Unit12/UnitW/UnitWS*/Horn/Job`; HASH (units 0,1 = (48,0); state words 2..13 of job `nxt`; length units 14,15) | GLUE (one per unit slot of the job's message) |
| slot, chan 0 (sample) | `(0, tidx, 0, KIND_SAMPLE=1, v, 0, 0)` | SAMP (one per accepted candidate) | ALU `Smp1` (tidx P2), `Smp12` (P2+k, k<12) |
| slot, chan 2 (anchor) | `(2, job, 0, 0, t_start, cnt, tag)` (**tag added by fix B-tr2**) | ALU `Anchor` (P2, A=P0, B, P3) | HASH static rows (op_f+op_c+op_p) |
| slot, chan 3 (PoW) | `(3, job, 0, 0, l0, l1, l2)` = PoW output word 0 limbs | HASH op_p rows | ALU `PowChk` (P2) |
| job | `(job, tag, tr)` | HASH (tr = 0), ALU `Job/NodeJob` (tr = 1) | GLUE job-start row |
| digest | `(job, pair j, 6 limbs)` | GLUE last block, pairs 0..2 | HASH (`receive_digest`, the 18-limb state_out), ALU `Dig` |
| t.sample | `(job, t_start, cnt, last_word, last_half, last_acc)` | SAMP last row of a run (+) | HASH op_s row (−) |
| t.word | `(job, wi, l0, l1, l2)` | HASH op_s row, `rdw[i]` for word i | SAMP row (one per row) |
| byte (lookup) | `(x, y)`, both bytes | ByteAir table (key, multiplicity) | SAMP `(b_{2k}, b_{2k+1})`, `(lo5·2^3, lo2·2^6)`, `(u0, u1)` |

Multiplicity semantics: every HASH/SAMP count is a boolean column or a product of booleans
(`kh·rdw[i]`, `ks·acc[h]·h1`, …), so each row contributes 0 or ±1 per message; balance is
"#sends = #receives per message over the whole trace". Total counts ≤ rows·slots < 2^24 ≪ p, so
the integer multiset statement follows from the field statement (no wrap; cf. §2(f)).

### HASH role (`Hash2Cols`, 39 columns after fix B-tr1; one row per transcript job)

Columns: `is_first, op_f, op_c, op_s, op_p` (op one-hot: flush / commit / squeeze / PoW), `job`,
`nxt` (next row's job), `hn` (has next), `t_start, cnt`, `state_out[18]` (output state as
6 words × 3 air2 limbs), `rdw[6]` (state words read by SAMP, a prefix), `last_word, last_half,
last_acc, full`, **`ns` (squeezes before this row; fix B-tr1)**.

Constraints (all ×kh): H1 booleans (`is_first, op_*, last_acc, last_half, hn, rdw[i]`);
H2 `Σop = 1`; H3 `is_first·t_start = 0`; H4 `op_c·(cnt − 18) = 0`; H5 `rdw[0] = op_s`,
`rdw[i+1]·(1 − rdw[i]) = 0`, `Σrdw = last_word + op_s` (so `rdw[i] = [i ≤ last_word]`,
`last_word ≤ 5`); H6 `last_acc, last_half` only on squeezes; H7 `full = rdw[5]·last_half`;
H8 `rej·(1 − full) = 0` with `rej = op_s − last_acc`; H9 entry into the region forces
`is_first`, interior rows have `is_first = 0`; H10 `hn = nkh`; H11 transition (both HASH):
`n.job = l.nxt`, `n.t_start = l.t_start + l.cnt`, no flush→flush, flush has a next row,
squeeze→squeeze only if `full`, `rej` ⇒ next row is a squeeze; H12 (fix B-tr1)
`is_first·ns = 0`, `n.ns = l.ns + l.op_s`, `op_s·(job − 2^25 − ns) = 0`.
Interactions: job start `(job, tag, 0)`; units 0,1 = `(48, 0)`; state words of `nxt` at
units 2..13 (count `hn`); length units 14,15 = `(4·cnt | digest_bytes, 0)` on static rows;
PoW word-0 send (op_p); digest receive (18 limbs = `state_out`); anchor receive
`(2, job, 0, 0, t_start, cnt, tag)` on static rows; sample-bus receive (op_s); word-bus
sends `rdw[i]`.

### SAMP role (`Samp2Cols`, 33 columns; one row per state word read, two LE-u32 candidates)

Columns: `job, wi, t_job, mbefore, is_first, is_last, b[8]` (BE bytes of the word),
`lo5, lo2`, `h1` (candidate 1 read), per candidate h: `g` (c3 ≥ 0xF0), `z, iz`
(is_zero(c3 − 0xF0)), `zv, iv` (is_zero(c1·2^8 + c2·2^16)), `zc, ic` (is_zero(c0² − c0)),
`acc`.

Constraints (×ks): booleans; runs `is_first … is_last` (entry forces is_first; last row of
region is_last); `(1 − h1)(1 − is_last) = 0`; `is_first·wi = is_first·mbefore = 0`; within a
run `job, t_job` constant, `wi += 1`, `mbefore' = mbefore + acc0 + h1·acc1`; byte lookups on
`b`, `(lo5·8, lo2·64)`, `(u0, u1)` with `u_h = g(c3 − 0xF0) + (1 − g)(0xEF − c3)`;
is-zero gadgets; `acc_h = 1 − g + g·z·zv·zc`. Interactions: word-bus receive
`(job, wi, limbs_from_bytes(b, lo5, lo2))`; sample sends `(0, t_job + mbefore (+acc0), 0, 1,
LE(c), 0, 0)` with count `acc_h·read_h`; last row sends the run summary on t.sample.


## 2. Proof: constraints ⇒ semantics

### 2(a) ALU: constraints ⇒ field semantics, op bound to the program row

Fix a satisfying trace T with program columns = P (hypothesis of Lemma 7.1). Let y be an ALU
row (ka = 1).

**A-1 (one op per row).** A1 gives exactly one lo and one hi index with h = g = 1, so exactly one
selector s(op) equals 1, for op = 8·hi + lo ∈ [0, 32). On non-ALU rows every selector is 0
(factor ka).

**A-2 (op = ⌊P1 / 2^20⌋, B = P1 mod 2^20).** On a non-Data row, A4 and the byte-pair table
(§2(c): the table holds exactly the pairs [0,256)²) give rx, ry ∈ [0, 256) and rz ∈ [0, 256) with
16·rz ∈ [0, 256), i.e. rz ∈ [0, 16) as integers. So bfield ≡ B* := rx + 256ry + 65536rz with
B* ∈ [0, 2^20) an integer. Then P1 ≡ B* + opv·2^20 with opv ∈ [0, 32), so the right side is an
integer < 2^25 < p. The honest P1 is an integer B + op·2^20 < 2^25 (isa.rs asserts B < 2^20;
`Instr::words`). Two integers < p that agree mod p are equal; by uniqueness of division by 2^20,
opv = op and B* = B. The undefined code 31 has opv = 0, so it can only label rows with op = 0
(Nop), where they impose exactly Nop's semantics (c = 0, no reads, no messages). Data rows:
`s(Data) = 1` forces c = 0 and sends `(y − app_base, P)` on bind2; a Data label on a row outside
the app region, or a missing Data label inside it, leaves bind2 unbalanced (APPB receives exactly
`(x, T[x])` for x ∈ [0, n), §2(b)). So the op executed on every row is the op of P[y].

*At 3c9d479ab this step failed (bug B1):* the lookup `(16rz, 0)` only gives 16rz ≡ t (a byte),
i.e. rz ≡ t/16 mod p, so 65536rz ≡ 4096t and B* ranges over [0, 1110015]. Any row with
B ≤ 61439 could be relabelled op → op − 1 with B' = B + 2^20. Exploitable instances: Zero →
Bit (`a = 0` weakened to `a0 ∈ {0,1}, a1.. = 0`), Mul → Nop (product replaced by 0). Test
`nv_alu_relabel_zero_to_bit` builds a child proof with Gruen s(3) = 1 (native verifier
rejects) and a trace that passed the debug checker before the fix.

**A-3 (operands).** For an op that reads A (resp. B) the lookup `(P0, a)` (resp. `(B, b)`) has
count 1. By (F4) / §2(f) every looked-up message is a key `(y', c(y'))` of some ALU row y'.
Keys have pairwise distinct first components (C2: y is the row index), so a = c(P0) and
b = c(B): the operands are the memory values of the addressed rows. Ops that do not read an
operand ignore it (A2 does not mention it; the DOF run confirms these cells are inert).

**A-4 (result).** For the active op, A2/A3 give exactly the isa.rs semantics:
`c = a·b` (Mul, Ext12 product: `ext_field_multiply` with the `BinomiallyExtendable<12>`
constant W of BabyBear, the same EF as the native verifier's `Sha384Config::EF`), `a+b`, `a−b`,
`2a+b`, `a·b+a`, `a` (copies, incl. UnitWT), `P0` / `P0·X` (Const/ConstX), `a·b + wit` (Horn), `0`
(Nop/Anchor/Job/Zero/NodeJob/Data), with the side conditions `a = 0` (Zero), `a ∈ {0,1}` (Bit),
`c ∈ {0,1}` (LoadBit), `c ∈ F` (LoadF), `c ∈ F` (Smp1, plus the received sample), `a0 = level`
(Pv). Free results: Load (any Ext12), LoadF, LoadBit, and the bus-bound Smp1/Smp12 (slot),
Dig (digest), PowChk (c0..c2 from the hash chain, chan 3), Acc/Acc2 (acc buses).

*No wrap-around:* every ALU op is an operation of F or of Ext12; the native verifier computes
in the same field, so field arithmetic is the intended semantics and nothing wraps. The only
integer-valued ALU quantities are B (A-2), bits (Bit/LoadBit/LoadF-free c0 with c ∈ {0,1}),
and recompositions from bits (indices, PoW limbs; §2(d)).

*Base-field loads (bug B3, fixed):* at 3c9d479ab `Builder::load_f` emitted `Load`, so a value the
native verifier holds in F (PoW low limb, child public values, inverse witnesses) could carry
unobserved coefficients 1..11. `Builder::pow`'s check `l0 + x1·X + x2·X² = PowChk word` was then
vacuous (coefficients 1 and 2 of the l0 load absorb any limb). New op `LoadF` (code 29, c1..11
= 0); test `nv_alu_base_load_pow` (accepted with the pre-fix program, rejected now).

**A-5 (memory is a function).** Each address y ∈ [0, 2^prog_log) has exactly one value c(y);
reads of y always return it; mult is a free key multiplicity (count weight 0), which LogUp
lookups allow (§2(f)). Reads of an address ≥ the number of ALU rows have no key and fail.

**Consequence (ALU execution lemma).** Let Π(P) be the straight-line program of P (op, A, B,
k1, k2 per row). For every satisfying T there is a choice of free inputs
W = (Load/LoadF/LoadBit results, Horn wit, and the bus-received values of
Smp1/Smp12/Dig/PowChk/Acc/Acc2) such that the column c is exactly the execution of Π(P) on W,
and every assertion (Zero, Bit, LoadBit, LoadF, Smp1, Pv, Dig with B = 1) holds. The slot,
job and digest messages the ALU emits are the ones Π(P) prescribes for these values. What binds
W to the native verifier's values is the content of §2(d), §2(e) and §2(c).

### 2(b) Program binding

Within one NV trace:

**B-1 (executed = committed).** By A-2 and A-3 the op, the operand addresses and the keys of
row y are read from P[y]; by C2 row y executes at address y. So the executed program is P.

**B-2 (no skipped, reordered or duplicated rows; length pinned).** Let L = 2^prog_log.
* P[L − 1] = Acc row with P0 = L − 2 ≠ 0, so ka = 1 there (C4), and by C5 every earlier row has
  stage 0, i.e. ka = 1: all of [0, L) are ALU rows, in order, at addresses 0..L−1.
* Rows ≥ L have P = 0 (hypothesis P = program table, zero beyond L). If such a row had ka = 1
  it would be a Nop-equivalent ALU row (A-2 with P1 = 0) that sends `(y, 0)` on bind.
* BIND (B1–B3): one contiguous region (C5), first row y2 = 0, step 2, exactly one row with
  bl = 1 (the last). The bind bus is a permutation: the BIND rows receive `(2t + h, pc_h)` for
  t < n_b, and every ALU row sends `(y, P[y])` once. Hence the ALU rows are exactly
  [0, 2n_b) and pc = P. The unique Acc row (A-2: op bound to P1, and P has one Acc row) receives
  `(acc_total, y2_last)` and asserts y2_last = P0 = L − 2, so n_b = L/2 and the ALU region is
  exactly [0, L). (Extra ALU rows beyond L are therefore impossible.)
* (ya, yb) is the honest split of y2: ya ∈ {0, …, 510} even (B4). If ya ≠ y2 mod 512 then
  yb = (y2 − ya)/512 mod p; the lookup `(yb + 512, e2)` needs yb + 512 to be an ALU address
  < 2^17, i.e. (ya_true − ya)·512⁻¹ ≡ m (mod p) with |m| < 2^17, i.e. ya_true − ya = 512m as
  integers (both sides < p/2 in absolute value), impossible for 0 < |ya_true − ya| ≤ 510. Test
  `nv_bind_tamper`.
* So acc_total = Σ_{y < L} E1[y mod 512]·E2[y ≫ 9]·Σ_j τ^j P_j[y] = Σ_{x < 2^H} w_r(x)·Σ_j τ^j
  P_j[x] restricted to x < L, where w_r is the opening kernel (`nv_opening_formula`).

**B-3 (APPB).** Identical argument with (bind2, acc2), Data rows in [app_base, app_base + n),
Acc2 at row L − 2 with P0 = n − 2. Without an app table there is no Acc2 and no Data row, and
any APPB row would leave acc2/bind2 unbalanced, so the region is empty.

**B-4 (across levels: what makes P = P_i).** The program asserts, for the child,
`flag·acc_total + (1 − flag)·(ACC2 + w_r(L−1)·ptau(Acc words)) = p̂`, with
`p̂ = Σ_j τ^j·open_child(P_j)(r)` and `flag = [child level ≠ 1]` (flag = (cl−1)·inv with
`(cl−1)(1 − flag) = 0`; inv is a LoadF witness). Because 1, τ, τ², τ³ are F-linearly
independent (τ = 1 + X has degree-12 minimal polynomial), Σ_j τ^j(P_j − P'_j) is a non-zero
polynomial in r whenever the base-field tables differ, so by Schwartz–Zippel the check
implies child P = own P (flag = 1) or = app table T_app ∪ {Acc row} (flag = 0), up to
(2^{l_skip} − 1 + n)/|Ext12| per candidate. That error and the soundness of the opening belong
to the protocol proof (Lemma 3.6, "V′"); here we only need that NV arithmetises V′
(the binding check is ordinary ALU code, so A-4 applies). The final native verifier checks the
top proof's openings against P_NV; induction downwards gives P = P_i at every level, which is the
hypothesis "program columns = P_i" of Lemma 7.1.


## 2(c). Proof: the SHA subsystem computes SHA-384 / SHA-384/336 exactly

**Lemma SHA-faithful.** In any trace satisfying Sha512Air, TableAir, ByteAir and the GLUE role
with all buses balanced (as multisets over F_p, total count of any message < p), for every
GLUE job J with job-bus message (id, tag, tr):
1. its rows determine a byte string M_J and the unit sequence (u_0, u_1, …) received on the
   slot bus for `id` in index order; M_J = PREFIX ‖ tag ‖ enc(u_0) ‖ enc(u_1) ‖ … for a prefix
   job (enc(felt) = 4 LE canonical bytes, enc(word) = 8 BE bytes, enc(tail) = its 2 bytes), and
   M_J = NODE_PREFIX ‖ L ‖ R for a node job (48- or 42-byte digests);
2. the digest pairs sent on the digest bus for `id` are exactly SHA-384(M_J) (words H'0..H'5),
   truncated to 42 bytes (low 6 bytes of H'5 zeroed) iff 42-B mode and tr = 1 — with one
   exception: limb 2 of H'5 is sent as s5 − lo6 with lo6 pinned only by its consumers (C9.8);
3. no other message appears on the digest bus.

Assumptions imported from the other roles (proved in §2(a)/(d)): job ids offered on the job bus
are pairwise distinct; the producers (ALU, HASH) send each (job, unit index) at most once.

### C1. Ranges

Each digit polynomial ∏(v − m) has the 2^s distinct roots 0..2^s − 1, so every digit is that
integer; likewise every stored carry ∈ {0..7}. Hence every word slot is a 64-bit integer with
exactly one digit vector (base 2^k is a bijection), and its limbs (linear in digits) are its
21/21/22-bit limbs.

### C2. Row structure

pad·flag = 0 and pad = 1 − Σ(F_IV, F_ROUND, F_OUT) give: if real ≠ 1 then pad ≠ 0, so all
flags vanish and real = 0. So real ∈ {0, 1}. On real rows the ctl lookup (count 1) forces
(r, flags) = ctl_entry(i) for some i, so r ∈ [0, 42] and the flags are row r's. (A non-entry
message would need its counts, all +1, to sum to 0 mod p: impossible with < p rows.) The
transition rules then force: real rows form a prefix of the trace (pad·real(n) = 0), start at
r = 0, g = 0, step r' = r + 1 except r' = 0 after r = 42, and the last real row has r = 42. So
the real rows are N back-to-back segments with r = row mod 43 and g = row index; cid = g − r =
43·(segment index) is distinct per segment. Padding rows are all zero (pad·(r, g, flags) = 0 and
the zero rules), so they send nothing on any bus (every count is a flag combination).

### C3. Tables

TableAir row i is pinned to index i mod 48 (one-hot recurrences), so its offered messages are
exactly ctl_entry / k_entry values; free multiplicities only scale them. ByteAir: z = [x = 255]
(z(x − 255) = 0 and (x − 255)·inv = 1 − z), so the rows enumerate (0,0), (1,0), …; the last row
must be (255, 255) and y never decreases or wraps (< p·256 rows), so the height is exactly 65,536
and the keys are [0, 256)² (`sha_carry_bounds.py` byte_air).

### C4. Lookback bus

Every sender key is the sender's own g with a tag; every receiver key is g − 40, g + 40,
g − 1, g − 7, g − 3 with a fixed tag. With g = row index (C2) each receiver's message can only
match the unique row at that key, and that row sends with count exactly 1 (flags of the row
positions: ST at rows 1 and 40, DA at 0..39, V at 2..33, W7 at 6..37, matching the receivers
at rows 42, 0, 2..41, 10..41, 10..41 of the same segment). Counts are ±1, so balance ⇔ each
receiver's residual tuple equals the sender's tuple as field elements.

### C5. Bit polynomials

For an s-bit digit, σ_t(v) = u·S_t(u²) with u = v − (2^s − 1)/2 is interpolated on the top half
of the range; complementing v negates u and flips every bit, so the odd form is exact on all
2^s values. `nv_faithful_sign_polys` checks every digit value at every position for k = 1, 2, 3,
and that the sign-limb forms of Σ0, Σ1, σ0, σ1, Ch, Maj equal FIPS 180-4 on random words
(ROTR/SHR amounts 28/34/39, 14/18/41, 1/8/>>7, 19/61/>>6). So each such limb is the integer limb
of the true function value.

### C6. Field equations are integer equations (carry checks at degree 21)

The degree-21 part only produces bit signs; every addition check is the **linear** limb
equation E_i := out_i + 2^{w_i}(c_i − off) − (c_{i−1} − off) − R_i − T_i ≡ 0 (mod p), where
R_i is a limbwise sum of operand limbs (each pinned to an integer by C1/C5, S_A/DE by their
defining equalities, V by the bus) and T_i is the received target (K by the k-table lookup, d
and d − T2 and W[t−7] and the IV/final words by C4) — all integers in known intervals.
`scripts/sha_carry_bounds.py` computes the exact integer range of E_i for every equation and
limb:

| equation | limb | min E | max E | max\|E\|/p |
|---|---|---:|---:|---:|
| a0: a = S_A + W + K (S_A = 5 limbs) | 0, 1 / 2 | −14,680,064 | 16,777,215 / 33,554,431 | 0.0083 / 0.0167 |
| e0: e = a + (d − T2), offset 4 | 0, 1 / 2 | −12,582,913 | 12,582,913 / 25,165,825 | 0.0063 / 0.0125 |
| a1: a = h + Σ1 + Ch + W + T2 + K | 0, 1 / 2 | −14,680,064 | 16,777,215 / 33,554,431 | 0.0083 / 0.0167 |
| e1: e = a − T2 + d, offset 4 | 0, 1 / 2 | −12,582,913 | 12,582,913 / 25,165,825 | 0.0063 / 0.0125 |
| schedule: W = σ1 + V + W7 (V unreduced) | 0, 1 / 2 | −16,777,219 | 16,777,215 / 33,554,431 | 0.0083 / 0.0167 |
| feed-forward (rows 42 and 0/1) | 0, 1 / 2 | −8,388,613 | 16,777,215 / 33,554,431 | 0.0083 / 0.0167 |

Every |E_i| < 2^25.0 < p/59, so E_i ≡ 0 (mod p) ⇒ E_i = 0 over Z: **no false carry solution
exists mod p**, for any digit/carry values in range. Summing 2^{off_i}·E_i telescopes:
out + 2^64·C_2 = Σ_i 2^{off_i}(R_i + T_i), i.e. out ≡ (sum of operand words) mod 2^64, and with
out ∈ [0, 2^64) it is the SHA-512 sum. (The script also checks completeness: honest carries lie
in [0, 6] for a, [−2, 1] for e (stored +4), [0, 3] for W, [0, 1] for the feed-forward, all
inside [0, 8).)

### C7. The compression is FIPS 180-4 SHA-512

By C6, for each round row n (rows 2..41) slot 0 computes a = T1 + T2, e = d + T1 with
h = e0_{n−2}·(via S_A), Ch(e1_{n−1}, e0_{n−1}, e1_{n−2}), Σ1, Σ0, Maj on the previous four
a/e words in time order (row l slot 0 < row l slot 1 < row n slot 0 …), K from the k-lookup
keyed by r_l = r_n − 1 (entries 1..40 carry K[2r_n − 4], K[2r_n − 3]; the script checks these
cover rounds 0..79 once and that the K table and SHA384_IV equal their cube/square-root
definitions), d from the row two back (C4). Slot 1 likewise. W: rows 2..9 from the block
(iface pairs 4..11), rows 10..41 by W_t = σ1(W_{t−2}) + W_{t−7} + σ0(W_{t−15}) + W_{t−16}
(V from row n − 8, W[t−7] from rows n − 4 / n − 3). The feed-forward gives H'_j = H_j + (state
after 80 rounds)_j on rows 42 and 0/1. With the input state and block fixed by the iface pairs
0..11, the pairs 12..15 sent by the segment are exactly compress512(H, B).

### C8. Interface: segments ↔ GLUE compressions, no injected compression

Each real segment sends its 16 pairs once (rows 0, 1, 2..9, 42), keyed by its distinct cid.
Each GLUE compression (8 rows) receives 16 pairs with one cid: block pairs 4..11 (every row),
input pairs 0..3 (q < 4), and its output pairs 12..15 either on the next block's rows q < 4
(as that block's input, cid' = cid − 43, the previous compression of the same job, since cid
steps by 43 inside a job) or on its own last-block rows q ≥ 4. Balance with counts ±1 ⇒ a
bijection between segments and GLUE compressions with equal (H_in, B, H_out). So:
* every GLUE compression's output is compress512 of its input and block (C7);
* a segment with no GLUE consumer (a "fake compression", e.g. a consistent extra segment in the
  zero tail, or a copy of a consumed one) leaves 16 unmatched sends — rejected; zero-padding
  rows send nothing (C2), so they cannot inject anything; a reordering changes cids — rejected
  (`nv_faithful_fake_and_reordered_segments`, three cases, all rejected by bus 3);
* chaining: block k > 0's input = block k − 1's output; block 0's input = the SHA-384 IV
  (constraint on s for blk0, q < 4).

### C9. GLUE: the hashed message is the native framed message

C9.1 *Bytes.* b0..b15 are bytes by pair lookups; carry/carry2 equal the next row's b0/b1 under
cont, and every carry that is read (slot 3 on act rows, node42 R1/R3 views) is on a cont row.

C9.2 *Limb splits (×256 argument).* The lookups give V5 := 2^{8−a5}·lo5 and U2 := 2^{8−a2}·lo2 as
bytes — this alone does **not** make lo5, lo2 small integers (lo5 = V5/8 is a non-integer field
element unless 8 | V5; this is the pattern the parent found in the ALU rz check). Multiply the
three limb formulas by 256:
256 l0 = 256 b7 + 2^16 b6 + 2^21 V5, 256 l1 = 8 b5 − V5 + 2^11 b4 + 2^19 b3 + 2^21 U2,
256 l2 = 64 b2 − U2 + 2^14 b1 + 2^22 b0. The right sides are integers of magnitude < 1.08·10^9
< p. (a) If the limbs equal canonical limbs L_i (block words: received from the SHA iface; state
words: from SHA), then |256 L_i − RHS| < p (script), so the equations hold over Z; mod 8 the
second gives 8 | V5 and mod 64 the third 64 | U2; then the equations are the base-256 /
base-2^5 / base-2^2 digit expansions and force b = BE bytes of L0 + 2^21 L1 + 2^42 L2.
(b) For arbitrary limb values (word units from ALU cells), two solutions have |ΔRHS| < p, the
same mod-8/mod-64 step gives ΔV5 ≡ 0 (8), ΔU2 ≡ 0 (64), and the digit argument gives Δb = 0: the
byte string is a function of the cell. `nv_faithful_limb_split_exhaustive` (Rust, 45 words) and
`split_exhaustive` (Python, 27 words) enumerate all 2^16 (V5, U2) per word and find exactly the
canonical solution; `nv_faithful_limb_split_fractional` builds the natural attack (lo5 −= 1/8,
b6 += 32: limb 0 and every lookup unchanged) and it is rejected (limb 1 moves by 1/256). **No
fix needed** for lo/ulo.

C9.3 *Felts are canonical.* zm = 0: 0x78 − a3 − 1 is a byte ⇒ a3 ≤ 0x77 ⇒ felt < 0x78000000 = p − 1; zm = 1: a3 = 0x78, a0 = a1 = a2 = 0 ⇒ felt = 0x78000000 = p − 1 (script: exhaustive over
a3, zm). So felt ∈ [0, p) and felt ≡ c0 pins the canonical LE bytes (`nv_faithful_noncanonical_felt`:
x + p encodings rejected, p − 1 accepted).

C9.4 *Units and padding.* By induction from start, phase ∈ {0, 1} and d_s ∈ {0, 1}. Every active
slot before padding is a unit receive (felt, half of a word, or the 2-byte tail) at the running
index uidx; after padding every byte is 0; the padding slot is 0x80 000000 (or the tail's
0x80 00). Since the producers send each (job, index) at most once and GLUE receives indices
0, 1, 2, … contiguously, balance forces GLUE to receive exactly the producer's unit set, in index
order, with equal kind and value; padding starts right after the last unit. The kind field makes
the encoding unique: felt (0) ≠ word (2) ≠ tail (3, after fix F-c1).

C9.5 *Framing and length.* Rows 0, 1 of block 0 are PREFIX (32 bytes, from `sha_levers().prefix()`,
v4 default or v5-w{42,48}-c{0,1}), byte 32 is the tag, received on the job bus against the
producer's tag (ALU `Job`: P0; HASH role: 3/4/5/7), units start at byte 33. The end row is
b0..b12 = 0, b13..b15 = 8·(33 + 4·uidx − 6·hs): both sides < 2^27 < p, so this is the integer
message length in bits (tail units count 2 bytes: 8 − 6). [q = 6] ⇒ last = phase_after: padding
has begun by byte 112 of the last block and not before byte 112 of any earlier block, i.e. the
FIPS 180-4 minimal padding (0x80 may sit in row 7 of a block, which then needs one more block).
This equals `hash_parts_message(tag, parts)` when the producer's units are the parts with
their 8-byte LE length prefixes (felt units (len, 0)); `nv_faithful_tail_framing_unique` checks
equality with the native `hash_parts_message` for a commit job. Leaf (tag 0), coset leaf (6),
flush (3), commit (4), squeeze (5), PoW (7) all use this path.

C9.6 *Node jobs.* nd is tied to job-bus tag 256 (prefix-job tags are bytes, so the two kinds
cannot be confused); nd ⇒ one block, act = 0 (no regular receives: d_s = 0 forces p = hp = wd = 0),
row 0 = NODE_PREFIX ‖ first word, fixed padding and length 832 (48 B) / 736 (42 B), and the 12
fixed-index word receives cover every message byte (rows 3–5 in 42 B use the shift-2 views and
the carry/carry2 links); a tail view limbs_from_bytes([x0, x1, 0…]) = (0, 0, 2^14 x0 + 2^6 x1) is
the word with its low 6 bytes zero. So M = NODE_PREFIX ‖ wire(L) ‖ wire(R) = native
`node_message`.

C9.7 *Digests.* The digest send happens only on rows q = 4, 5, 6 of a job's last block, with s =
the received output pairs 12..14 of that compression = H'0..H'5 = SHA-384(M_J) (C8 chaining from
the IV). Job ids are unique (assumption), so these are the only digest messages for `id`.
Truncation: 42-B mode and tr = 1 (declared by the producer: ALU leaf/node jobs 1, HASH 0) zeroes
limbs 0, 1 of H'5 and subtracts lo6 from limb 2 (bits 42..63): native `truncate_digest` zeroes
bytes 42..47 = bits 0..47 of H'5 (script: 21 + 21 + 6 = 48).

C9.8 *lo6 is pinned by its consumers, not by GLUE.* lo6·4 is a byte, so lo6 = v/4 for a byte v
— not necessarily an integer, and even when it is, GLUE does not tie it to s5 mod 64. Every
consumer of digest pair 2 of a Merkle job equates the received limb with a canonical tail limb
T = 64·t, t < 2^16: node jobs receive it through the tail view (C9.6), and the Merkle root check
(`merkle_path`: Zero(cur.hi − root.hi)) compares it with the commitment cell, whose word 5 is a
tail unit of the commit job (C9.4, after fix F-c1). Then s5 − v/4 ≡ T ⇒ v ≡ 4(s5 − T) and
|v − 4(s5 − T)| < p ⇒ v = 4(s5 − T), s5 − T ∈ [0, 64): the truncation is exact. This argument
relies on the list of consumers (`nv/builder.rs::dig` callers: `node`, `merkle_path`); a new
consumer of a 42-B digest must keep this property (or GLUE should pin lo6, e.g. one extra pair
lookup of the two bytes of (s5 − lo6)/64). `nv_faithful_lo6_pinned` (42-B run): lo6 + 1 and
lo6 + 1/4 are rejected by a canonical consumer.

**Proof of the lemma:** items 1 from C9.1–C9.6; item 2 from C7, C8, C9.7–C9.8; item 3 from C9.7
(digest sends are role-gated GLUE rows only). ∎

Native correspondence: SHA-384 = compress512 with SHA384_IV (C8), FIPS padding (C9.5), output
H'0..H'5 (48 B) or 42 B truncation (C9.7); framed messages = `hash_parts_message` (C9.5); nodes =
`node_message` (C9.6); `digest_words` = big-endian H words, which is the limb order of the cells.

## 3(c). Attack audit (SHA / GLUE)

| attack | outcome | test |
|---|---|---|
| out-of-range digit / carry re-solved to ±½ or mod p | impossible (C1, C6) | S-lane mutation suite; `nv_faithful_sign_polys` |
| false carry solution mod p | impossible, max\|E\| ≤ 0.0167 p | `sha_carry_bounds.py` |
| consistent extra segment in zero tail / duplicate of a consumed one / swapped segments | rejected (bus 3) | `nv_faithful_fake_and_reordered_segments` |
| fractional lo/ulo split keeping limb 0 and all lookups | rejected (×256 argument) | `nv_faithful_limb_split_fractional`, `_exhaustive` |
| non-canonical felt bytes (x + p) | rejected | `nv_faithful_noncanonical_felt` |
| lo6 ± 1, lo6 + 1/4 on a 42-B Merkle digest | rejected via consumer | `nv_faithful_lo6_pinned` |
| **42-B commit tail framed as a full 8-byte word** | **accepted before fix F-c1**; rejected after | `nv_faithful_tail_framing_unique` |
| byte, split, flag, state single-cell mutations | rejected | `nv_hash2_rejects_mutations` (78 cases) |

## 5(c). Soundness bug found and fixed

**F-c1 (42-byte mode): the framing of a commitment's digest tail was a prover choice.** The ALU
pushed word 5 of a 42-B commitment (top 2 bytes, low 6 bytes zero) as an ordinary word unit
(kind 2), and GLUE accepted a kind-2 unit either as a full 8-byte word (`wd`) or as the 2-byte
tail (`hp`, with the −6-byte length correction). Both framings are internally consistent
(units, padding, bit length, block count), so the transcript state after every 42-B
`observe_commit` (child main commitment, every WHIR round commitment, …) could be either
SHA-384(native message) or SHA-384(message with the 42-byte digest part replaced by 48 bytes).
Consequence: the in-circuit challenges were not a function of π (Lemma NV-faithful false as
stated), and a cheating prover gained one bit of grinding per commit job (≈ 2^{#commits}
multiplicative loss in the RO soundness bound). Squeeze/flush jobs had the converse 2^-48-chance
ambiguity (a full state word with zero low 6 bytes accepted as a tail).
* **Fix:** a new unit kind `UNIT_HALF = 3`. GLUE's tail receive uses kind 3 (word receives keep
  kind 2); new ALU op `UnitWT` (code 30; 29 is the parent's `LoadF`) = `UnitW` with B = 2 except
  that its second unit has kind 3; `observe_commit_cells` uses it in 42-B mode. Node-job tails
  are unchanged (their framing is fixed by q). No new columns; NvAir degree unchanged
  (`nv_degrees` passes); slot interaction count unchanged.
* **Test:** `nv_faithful_tail_framing_unique`: honest commit job accepted; the full-word
  re-framing (same producer units) accepted before the fix (log: test failed at the "rejected"
  assertion), rejected after.
* **Regression:** with the fix, in both 48-B and 42-B + coset-leaf modes: `nv_faithful_*` (7),
  `nv_hash2_*`, `nv_circuit_fib_debug`, `nv_circuit_interactions_debug`, `nv_circuit_tamper`,
  `nv_program_*`, `nv_opening_formula`, `nv_degrees`, `nv_lever_tamper`, `nv_whir_lever_tamper`,
  `nv_tight_heights`, `nv_zero_tail_plain` all pass.

**Audit of the `lookup(x·2^k)` pattern in this scope** (the parent's ALU rz finding):
* GLUE lo/ulo splits: non-integer solutions exist for the lookups but cannot reproduce the
  limbs (C9.2) — sound, no fix.
* GLUE lo6·4: non-integer lo6 possible in GLUE alone; sound only through its consumers (C9.8).
* felt gap / zm: the looked-up value is an integer combination of bytes — no scaling, sound.
* Sha512Air / TableAir: no lookups with scaling (polynomial range checks) — n/a.
* Out of scope but same pattern: SAMP role `lookup_pair(lo5·2^3, lo2·2^6)` (transcript2.rs:488);
  C9.2(a) applies if its limbs are matched against SHA output limbs.

## What remains unproven in (c)

* Job-id distinctness on the job bus and "each (job, unit) sent at most once" by the producers
  are imported from §2(a)/(d).
* C9.8 is a whole-program property (consumers of 42-B digests); it holds for the audited
  program but is not enforced locally.
* LogUp's "count of any message < p" uses the trace-height bound; the GKR/LogUp soundness error
  itself is §2(f)'s term.
* k = 1, 2 layouts: the sign polynomials are tested, the carry-bound table is computed for k = 3
  only (limb widths 22/22/20 for k ≤ 2 give the same order of magnitude).

## §2(d) Transcript chain and sampling

### (i) The abstract invariant (what the HASH/SAMP/GLUE/SHA machinery realises)

Let the native transcript be the event log E = (e_0, e_1, …, e_{T−1}) produced by
`ShaTranscript` (observe felt, commit = 18 limb events, sample, PoW witness elements), with
state σ: σ_0 = H(2, ∅); flush σ' = H(3, σ ‖ felts); commit σ' = H(4, σ ‖ digest_wire);
PoW σ' = H(7, σ ‖ w) with check "first z bits of σ' are 0"; samples read the LE-u32 words of
squeeze outputs s = H(5, σ) in order, accepting n < 2p and returning n mod p, a fresh squeeze
after 12 words or after any non-sample event. Here H(tag, parts) = SHA-384(prefix ‖ tag ‖
(le64(len) ‖ part)*).

**Invariant D.** In any satisfying trace, the HASH rows, listed in order, are exactly the
oracle calls of the native transcript on the event log E* whose observed values are the
ALU cells pushed as units (`Unit1/Unit12/UnitW/Horn` at the static job ids) and whose PoW
witnesses are the `Unit1` cells of PoW jobs; every SAMP-emitted sample at tidx t equals the
native sample at t; and every ALU `Smp1/Smp12` cell equals the native sample(s) at its P2.
Each PoW job's output word 0 has its top z bits zero (after fix B3).

Which oracle inputs feed which challenge: the challenge at tidx t is a candidate word of the
squeeze output H(5, σ) where σ is the state after the last static job with t_start < t (or
the previous squeeze when 12 words are exhausted); candidate i of output word w is
LE(bytes 4i..4i+3 of word w).

### (ii) Proof of Invariant D from the constraints (concrete chain encoding)

Assumptions cited from other sections: (A1) GLUE maps a job's unit stream to the message
`prefix ‖ tag ‖ units` (felt = 4 LE canonical bytes, word = 8 BE bytes, 42-B tail) exactly and
consumes exactly the units 0..total of its job (§2(c)); (A2) the SHA AIR computes SHA-512
compression with the SHA-384 IV and the digest limbs are canonical air2 limbs (§2(c));
(A3) the ALU semantics of §2(a) (cells = program values) incl. B3 fix; (A4) bus balance
(§2(f), up to the LogUp error); (A5) program words are the honest program (§2(b)).

1. *Job ids are unique.* Leaf/node ids are program constants `0..n_jobs`, static ids
   `2^24 + i` are program constants via the anchors (each static HASH row receives exactly one
   anchor, each `Anchor` row sends one), squeeze ids are `2^25 + ns` (H12, fix B-tr1) with `ns`
   strictly increasing over squeeze rows. All < 2^26 ≪ p. Hence each id has exactly one GLUE
   job, and per-job bus messages cannot be exchanged between jobs.
   *Without B-tr1 (as audited)* two squeeze rows could share an id; the slot/word/digest buses
   then only balance the union of the two jobs' messages, so a GLUE job may hash a mixture of
   two chain states and a SAMP run may read words of the other job: the in-circuit challenges
   are then not the native ones. Test `nv_tr_squeeze_id_collision` (accepted before the fix).
2. *The op of each static row is the program's* (fix B-tr2: tag in the anchor). PoW rows are in
   addition pinned by the chan-3 send/receive with `PowChk`. *Without B-tr2* a commit row could
   be relabeled as flush (and a flush with 18 felts as commit): tag byte 4→3 and length unit
   48→72 change the hashed message while every constraint still holds; the prover gets a
   second transcript per commit (non-native challenges).
3. *Chain.* `n.t_start = l.t_start + l.cnt`, first `t_start = 0`: rows partition [0, T) in row
   order. Static intervals are the program's `(t_start, cnt)`; squeeze intervals contain
   exactly the sample tidx's (every SAMP sample must be received by an ALU `Smp*` at a program
   tidx, and the ALU receives each native sample tidx once). So the row order is the tidx
   order of E, up to (a) how a run of consecutive samples is split into squeezes and
   (b) zero-count squeezes.
4. *Squeeze segmentation equals native.* A squeeze reads candidates 0..last in order, its last
   read candidate is accepted unless all 12 were read (H8), a squeeze may follow a squeeze only
   if `full` (H11), and `rej` forces a following squeeze. Acceptance is the deterministic
   function of the bytes (`acc_h` gadget = `n < 2p`: c3 < 0xF0, or c3 = 0xF0 ∧ c1 = c2 = 0 ∧
   c0 ∈ {0,1}). Hence, given the input state, the number of squeezes and which candidate
   serves which tidx are exactly the native loop's; (b) only occurs when native also squeezes
   again (12 rejections).
5. *State induction.* The first row's state units come only from the ALU's `tr_first` push of
   the constant σ_0 (no predecessor sends to it; uniqueness, 1). Row k's GLUE job hashes
   `prefix ‖ tag_k ‖ (48,0) ‖ σ_{k−1} ‖ (len, 0) ‖ payload_k` (A1, units from row k−1's
   `state_out` through `nxt = job_k`, H10/H11), its digest is `state_out_k` (digest bus, A2).
   `tag_k` is the program's (2), `len = 4·cnt | digest_bytes`, payload = the ALU cells at that
   job's unit indices (felt canonical, A1). Hence `state_out_k = σ_k` of E*.
6. *Samples.* SAMP limbs `limbs_from_bytes(b, lo5, lo2)` equal canonical limbs of `σ_k`'s word
   (word bus, A2). The split lookups `(lo5·8, lo2·64)` alone allow non-integer `lo5, lo2`
   (x·2^k byte ⇏ x < 2^(8−k)); but `256·l1 = 8b5 − 8lo5 + 2^11b4 + 2^19b3 + 2^21·lo2`
   (and the analogue for l2) is an integer identity of magnitude < 2^30 < p when l1 is
   canonical, which forces `8·lo5 ≡ 8·b5 (mod 256)` ⇒ `lo5 = b5 mod 32`, and likewise
   `lo2 = b2 mod 4`; then the bytes are the unique BE bytes of the word. The emitted value
   LE(c0..c3) reduced in F equals native `n mod p`, at tidx `t_job + #accepted before`.
   ALU `Smp1` (c1..11 = 0 enforced) and `Smp12` (coefficient k ↔ tidx P2+k, matching
   `sample_ext = from_basis_coefficients_fn(|_| sample())`) receive them.
7. *PoW.* The `PowChk` cell = (l0, l1, l2) of σ_k's word 0 (chan 3, the pow job's id). The
   program asserts `cell = l0' + x1·X + x2·X²` with x_k recomposed from `keep_k` LoadBit rows,
   so `c1 = x1 < 2^keep1`, `c2 = x2 < 2^keep2` as integers (canonical limbs, A2), i.e. bits
   [64 − z, 64) of word 0 — the first z bits of σ' — are zero; coefficients 3..11 of the cell
   are forced to 0. This needs `l0'` to be a base element: **bug B3** (coordinator) — `load_f`
   was a plain `Load`, so l0'.c1, l0'.c2 absorb the top bits and the check is vacuous; test
   `nv_tr_pow_free_limb` (accepted on 3c9d479ab; passes after the LoadF fix). It also needs
   z ≤ 64 − o1 = 43 (limb 0 unchecked): now asserted at program generation. Wide PoW:
   `H(7, σ ‖ w0 ‖ w1)` with two `Unit1` cells, matching `check_witness_wide` of `ShaTranscript`.

### (iii) Program schedule = native schedule

The builder's transcript *is* a native `ShaTranscript` (`NvRecorder.inner`); each
observe/commit/sample/PoW call emits its fixed instruction(s) with the cell that the native
call consumes, so E* = the native event log of `verify` run on π* (the proof read off the
cells) iff `verifier.rs` calls the transcript in native order on the same quantities.
Checked by: end-state equality with `stark_backend::verifier::verify` for 6 lever sets ×
2 fixtures × {48 B, 42 B + coset leaf} (`nv_tr_native_schedule_levers`), and program
independence of proof values. WHIR order matches line by line (`whir.rs`): odd factor
observe; mu PoW, μ; per round k×(obs ev1, ev2, fold PoW, α); final poly | (commit, z0,
y0); query PoW (wide or single); q index samples (native samples all indices before
opening; NV interleaves only non-transcript rows); WHIR-Y `obs12(y_i)` before γ; γ.

*Program ≡ native on every proof element* (`nv_tr_every_proof_element`): for each of the
6,611 value elements of 3 lever sets × 2 fixtures (EF/F += 1, digest word bit flips; at 42 B
also), the native verifier accepts iff the program records no failure: 0 mismatches. Every
program failure corresponds to a `Zero`/equality row in-circuit.

### (iv) Query indices and the ×15 sampler

* c = 1: `decompose_index` loads 31 `LoadBit`s, asserts Σ 2^j b_j = s (field), and canonical
  (bits 27..30 all one ⇒ bits 0..26 zero, i.e. integer ≤ p − 1 = 15·2^27). Integers < 2^31 < 2p,
  so the bits are the unique canonical binary expansion; index = low `log_rs − k` bits =
  native `sample_bits`. zi_root = Π(1 + b_j(ω^{2^j} − 1)) = ω^index.
* c = 15 (wired; NV asserts c = 15): x ≠ p − 1 (top-4 AND = 0) ⇒ x < p − 1; y = x ≫ m,
  y = 15q + a, a ∈ [0,15) (4 bits, a = 15 rejected), q < 2^(27−m): both sides < p, so the
  integer division is unique; index = u0 + 2^m·a = x mod 15·2^m = native
  `sample_index_exact`; point ζ^a ω^u0 = native `query_root`. Divergence: native *resamples*
  on x = p − 1, NV rejects — completeness loss ≤ q/p, no soundness effect.
* Tamper tests: non-canonical index bits (x + p), index bit flip, a = 15 with q − 1.

### (v) Additive errors from (d)

None beyond the cited ones (LogUp/GKR ε_LU of §2(f); SHA AIR exactness of §2(c)). The
argument is exact: no collision resistance is needed for Invariant D.

### (vi) What changes under T* (GAPS G-1/G-2)

T*-1 (counter-mode squeeze B_j = H(5, κ ‖ le32(j)), next state = last block):
* HASH: squeeze rows no longer chain to each other: within a run every block job receives the
  same κ state units (needs a run-constant copy of κ — 18 limb columns, or the run's source
  row sending κ with multiplicity = #blocks) plus a felt unit le32(j); `nxt`/`hn` linkage,
  H11 squeeze→squeeze rule, `ns` (becomes block index j, reset per run, still unique ids via
  (run, j)), units 0,1 / length framing of the squeeze message change; the row after the run
  takes the *last block* as its state.
* SAMP: unchanged per block (word bus from each block's output).
* Builder/replay2/transcript model and native ShaTranscript change together.
* Proof steps to redo: (ii).1 id scheme, (ii).4 segmentation, (ii).5 state induction (state
  after a run), the "which inputs feed which challenge" map in (i).
T*-2 (PoW on the first z bits of B_1 = H(7, σ ‖ w ‖ le32(1)), indices from the remaining words):
* the PoW job becomes a sample source: op_p rows need `rdw`/t.sample/word-bus machinery with a
  start offset (skip the candidates covering the first z bits), extra length/le32(j) units,
  and continuation blocks B_j with tag 7; anchors for PoW jobs must cover the query tidx's.
* `PowChk`/LoadBit logic unchanged if the z bits stay in word 0 (z ≤ 43); `Builder::pow`,
  query `smp1` tidx bookkeeping and replay2 change.
* Proof steps to redo: (ii).3–4 (sample intervals now inside PoW rows), (ii).7.

## §2(e) Merkle / multiproof / coset leaves / tight heights

**What is opened.** For query i of round r the program (a) derives the index bits from the
in-circuit sample (§2(d)(iv)); (b) puts the opened values into leaf jobs: round 0 via `Horn`
(c = acc·μ + wit, and wit is unit `2 + c` of leaf job j — the *same* cell is hashed and folded),
rounds ≥ 1 via `Load` + `Unit12` (12 felt units of the value hashed and the value folded);
leaf job framing = `hash_parts(0, [felts])` (length unit = program constant 4·width, GLUE
consumes exactly the pushed units), or with the coset-leaf lever one tag-6 job with all 2^k
rows in coset order (= `hash_coset`); without it the 2^k row digests are combined by node jobs
in `tree_compress` order; (c) receives each leaf digest by `Dig` (digest bus, pairs 0,1 | 2,
B ∈ {2, 1} program constants; c[6..12] = 0 for B = 1); (d) for each level a node job
(`NodeJob`, NODE_TAG = 256 outside byte tags; GLUE node framing NPQ4NODE/v5 prefix, §2(c))
whose units are `UnitWS4/UnitWS2` of the current digest at uidx `12·bit` and the `Load`ed
sibling at `12·(1 − bit)`; bit is a `LoadBit` cell (boolean) read as operand b, `1 − bit` a
`Sub` row; (e) asserts the final digest cells equal the commitment cells, which are the cells
observed into the transcript (`load_commit` → `UnitW` of the commit job; canonical limbs by
GLUE word units; at 42 B word 5 has zero low bytes, matching the truncated `Dig` limb
`l2 − lo6`).

**Claim E.** In a satisfying trace, for every query the values folded are exactly the values
hashed into a leaf whose authentication path (direction bits = the index bits, LSB first,
depth `log_rs − k + ceil_log2(c)`) recomputes the observed root. This is native
`merkle_verify(root, index, hash_coset(rows), path)` for each query; fold = native
`binary_k_fold` (twiddles, x^{2^j}, x^{-1} witnessed with x·x^{-1} = 1, ½ factor), zi = zi_root^{2^k}.
Nothing else can be opened: the index is the canonical decomposition of the native sample,
leaf/node ids are distinct program constants, so `Dig` of job j is the digest of exactly the
units the program pushed to job j (A1, A2, uniqueness as in (d)(ii).1).

**Multiproof.** NV verifies one full path per query (the witness generator decompresses the
stream). Extraction builds the native canonical stream from the per-query sibling cells.
Native `merkle_multiproof_verify` then accepts unless two queries' paths disagree on a shared
node (or two queries at one index open different leaves) while both reach the root — which
exhibits a SHA-384(-truncated) compression collision *inside the trace* (straight-line).
Additive term ε_coll = Pr[the prover finds a collision of the Merkle compression]
(≈ q_H^2/2^{8·digest_bytes}, quantum q_H^3/2^{8·digest_bytes}); needed only with the multiproof
lever. Without multiproof the native check is per-query and no CR is needed.

**Tight heights.** The committed height is observed as a program constant after log_height
(native order), and the chunk factors (c, δ) in the stacking kernel are program constants of
the layout; the `nv_tr_every_proof_element` and `nv_tight_heights` tests cover the arithmetic
(honest equality + every-element mutation equivalence), not a symbolic proof of the formula.

**Tamper tests (e):** Merkle L/R swap at level 0, other leaf at query 0's index, sibling digest,
opened value, multiproof digests, x15 variants (`nv_tr_hook_tamper`, `nv_tr_x15_hook_tamper`,
existing `nv_circuit_tamper`, `nv_whir_lever_tamper`).

## Attack audit (d)/(e): tests (all in `nv/faithful_tr_tests.rs`, status on 3c9d479ab + fixes)

| test | classes | result |
|---|---|---|
| `nv_tr_squeeze_id_collision` | squeeze #1 given squeeze #0's id; fresh squeeze id | rejected (collision **accepted before B-tr1**) |
| `nv_tr_anchor_tag` | commit row relabeled flush | rejected |
| `nv_tr_tamper` | reorder two static jobs (consistent relink), anchor t_start / cnt, samples at shifted tidx, candidate 1 skipped, acceptance flipped, fewer words read, chain cut | all rejected |
| `nv_tr_pow_tamper` | PowChk c[3], PoW output limb, PoW LoadBit | all rejected |
| `nv_tr_pow_free_limb` | failing PoW (vk claims +16 bits) accepted via l0 cell c1/c2 | **accepted on 3c9d479ab (bug B3)**; needs the coordinator's LoadF fix |
| `nv_tr_hook_tamper` | non-canonical index (x+p), index bit flip, Merkle L/R swap, other leaf | all rejected |
| `nv_tr_x15_hook_tamper` | a = 15, L/R swap, other leaf (x15 + multiproof child) | all rejected |
| `nv_tr_native_schedule_levers` | transcript end state = native, 6 lever sets × 2 fixtures, 48 B and 42 B+coset | pass |
| `nv_tr_every_proof_element` | program ≡ native on 6,611 single-element proof mutations (also at 42 B) | 0 mismatches |

Witness-level attacks use test-only hooks (`verifier::Tamper`, `#[cfg(test)]` thread-local,
no effect in non-test builds) that make the program generator choose a cheating witness while
keeping every other cell consistent.

## Soundness bugs (d)/(e)

* **B-tr1 squeeze job ids unconstrained** (HASH). Fix: column `ns`, `is_first·ns = 0`,
  `n.ns = l.ns + op_s`, `op_s·(job − 2^25 − ns) = 0`; trace gen fills `ns` and asserts the
  numbering. No width change (HASH 38→39 < pool 59), degree unchanged (NvAir 8).
* **B-tr2 static-job op not bound** (commit ↔ flush relabel). Fix: anchor message carries the
  tag: ALU `v2 += s(Anchor)·P3`, HASH receives `tag`; builder anchors set P3 = TAG_FLUSH /
  TAG_COMMIT / TAG_POW (program words change; all NV tests pass).
* **PoW bit-range precondition**: `assert!(bits <= 64 − limb_off[1])` in `Builder::pow`
  (limb 0 is not range-checked by the PoW gadget).
* By reference (coordinator): B3 `load_f` free coefficients (PoW vacuous, test above); ALU
  B-field `rz·16` byte range (Zero→Bit / Mul→Nop relabels); missing
  `trace_height_constraints` / params-equality checks; child public values are free observed
  cells (statement gap).

## What remains unproven in (d)/(e)

* Port fidelity of GKR / batch-constraint / stacking arithmetic is established by
  differential tests (honest end state, every-element mutation equivalence) — not by a
  line-by-line symbolic proof. The WHIR part was checked line by line.
* (A1)/(A2) are cited from §2(c) (GLUE framing, 42-B tails/node42 mode, canonical limbs).
* T*-1/T*-2 re-proof (list above).

### 2(f) LogUp / bus semantics (F4)

The protocol proof's Lemma 3.1 gives balance mod p of every bus, with error
ε_LogUp ≤ ℓ_msg·N²/(2|F|) + 2N/|F|, |F| = p¹² ≈ 2^370.9. For NV: ℓ_msg ≤ 15 (max message
length incl. bus: NvAir 14, Sha512Air 15, ≤ 2^7 = the vk limit), N = Σ_air interactions·height
= 17,367,168 ≈ 2^24.05 at the fixed-point heights (2^18, 2^18, 64, 2^16), 2^25.05 at
(2^19, 2^19, 64, 2^16) (`nv_logup_counts`). With N ≤ 2^25.05, ε_LogUp ≤ 2^{3.9 + 50.1 − 1 − 370.9} +
2^{26.05 − 370.9} ≈ 2^−317.9. **This is the only additive term in Lemma 7.1** (the lemma
itself is deterministic given mod-p balance).

Mod-p balance ⇒ intended semantics:
* **Permutation buses** (slot, job, digest, iface, word, sample, bind, acc, bind2, acc2, ctl, k):
  every count is in {−1, 0, 1} on every row: selector sums (A-1), role flags, booleans; the
  non-literal ones are program constants (`(B−2)/2` for UnitW with B ∈ {2, 4}, `B − 1` for Dig
  with B ∈ {1, 2}) and GLUE/SAMP counts (§2(c), §2(d)). The verifier's trace-height
  constraint (checked by the native verifier for NV's own vk, and statically in the NV program
  for the child, finding B2) bounds Σ_bus weight·height < p per bus; all these interactions
  have weight 1, so for each message the integer sum of |counts| is < p, and ≡ 0 mod p implies
  = 0: integer multiset equality.
* **Lookup buses** (mem, byte, table): lookups have count ∈ {0, 1} and weight 1; keys have an
  arbitrary field count (mem `−ka·mult`, byte-table multiplicity column) and weight 0. For a
  looked-up message m that is not a key, the net count is #lookups(m) ∈ [1, p) ≢ 0. So every
  lookup is a key (subset semantics, stark-backend `LookupBus` / Soundness_of_Interactions
  Cor. 3.6).
* **Merged slots** (`merge_push`): the merged weight is the max over roles, so the per-bus height
  constraint is computed with a weight ≥ that of the active role; flags exclusive (C1).
* Message lengths ≤ 2^7 (asserted at keygen; `nv_logup_counts`).


## 3. Attack-surface audit (ALU, BIND, app binding)

Tests in `faithful_tests.rs` (status on the branch head; "at 3c9d479ab" = demonstrated
acceptance before the fix).

| attack | mechanism | result |
|---|---|---|
| Zero → Bit relabel, forged B field (rz = 255/16) | weakens `a = 0` to `a0 ∈ {0,1}`; child with Gruen s(3) = 1 | rejected; **accepted at 3c9d479ab** (B1) `nv_alu_relabel_zero_to_bit` |
| Mul → Nop and Mul → op 31, forged B field | product replaced by 0 | rejected; **accepted at 3c9d479ab** (B1) `nv_alu_relabel_mul_to_nop` |
| Const → undefined op; Data → Nop; Nop → Data | op binding, bind2 balance | rejected `nv_alu_relabel_misc` |
| public value ≠ level | Pv row | rejected `nv_alu_relabel_misc` |
| PoW low limb with extension junk | l0 coefficients absorb limb bits | rejected; **accepted with the 3c9d479ab program** (B3) `nv_alu_base_load_pow`, `nv_tr_pow_free_limb` |
| BIND alternative (ya, yb) split; premature bl; APPB table word | §2(b) B-2 | rejected `nv_bind_tamper` |
| ALU result, BIND acc, BIND program word, padding y / pool, Const→Load | existing | rejected `nv_circuit_tamper` |
| app table word (level 2 over a real L1 proof) | existing, 17 GB, not re-run here | rejected `nv_app_binding` |

SHA/GLUE and transcript/Merkle attacks: §3(c) below and the tables in §2(d)/(e).

## 4. Degree-of-freedom check (every cell)

`faithful_dof.rs`: for an honest trace set, every cell of every AIR is changed to v + d (d random
non-zero) and the change is classified *constraint* (a constraint is non-zero on one of the two
windows containing the cell), *bus* (the net interaction count of some (bus, message) changes —
exact multiset reasoning, the honest trace balancing first), or *undetected*. The evaluator
first re-checks the honest trace globally (0 failing constraints, 0 unbalanced messages). A
second, memory-coupled pass changes a result c_k[y] together with every memory read of y
(operands and E1/E2 copies) for every free-result row and samples of the others.

Run on the branch head, NV_DOF_CAP = 0 (all rows), log_rows 16:

| fixture | digests | cells | constraint | bus | undetected | unexpected | memory-coupled accepted |
|---|---|---:|---:|---:|---:|---:|---:|
| Fib | 48 B | 10,519,360 | 9,381,811 | 765,923 | 371,626 | 0 | 0 / 17,268 |
| interactions + Gruen GKR/zerocheck, derived claims, next-mask, WHIR-Y | 48 B | 10,519,360 | 9,362,219 | 790,608 | 366,533 | 0 | 0 / 17,568 |
| Fib + k1 = 1, keep-domain, multiproof, wide PoW, WHIR-Y, ×15 | 48 B | 7,717,696 | 6,632,351 | 670,423 | 414,922 | 0 | 0 / 15,600 |
| Fib + synthetic app table (Data / APPB / Acc2 rows) | 48 B | 10,519,360 | 9,380,135 | 767,407 | 371,818 | 0 | 0 / 17,376 |
| Fib | 42 B + coset leaf | 7,717,696 | 6,678,893 | 661,786 | 377,017 | 0 | 0 / 15,756 |
| interactions + levers (as above) | 42 B + coset leaf | 7,717,696 | 6,656,619 | 689,072 | 372,005 | 0 | 0 / 16,056 |
| ×15 + WHIR levers (as above) | 42 B + coset leaf | 7,717,696 | 6,656,506 | 645,280 | 415,910 | 0 | 0 / 14,376 |
| app table (as above) | 42 B + coset leaf | 7,717,696 | 6,677,217 | 663,270 | 377,209 | 0 | 0 / 15,864 |

Sha512Air and TableAir: **0 undetected cells** in every run. Every undetected cell falls in one
of these don't-care classes (checked mechanically per cell by `dont_care` / role tags, so a new
class fails the test):

| class | why it cannot affect the semantics |
|---|---|
| NvAir pool columns beyond the active role's view (ALU 6, HASH 20–21, SAMP 26) | read by no constraint or interaction of that role |
| ALU `a`/`b` of ops that do not read A/B; `wit` off Horn; `rx ry rz` on Data rows | not referenced by A2–A4 for that op |
| GLUE end row (q = 7, last block): `carry`, `carry2` | feed only the next row of the same job (gated by 1 − end) and inactive slots |
| GLUE rows q ≥ 4 of a non-last block: state pair `s0..s5` | on no bus (iface pairs only for q < 4 or the last block) |
| HASH last row (hn = 0): `nxt` | gated by hn |
| SAMP is-zero gadgets with operand 0: `iz`, `iv`, `ic` | `x·inv = 1 − z` leaves inv free when x = 0; z is forced to 1 |
| ByteAir rows x = 255: `inv` | `(x − 255)·inv = 1 − z = 0` |

**Undetected perturbations that matter: none.** Single-cell perturbation is necessary, not
sufficient: none of B1, B3–B6 is a single-cell freedom (each changes several cells
consistently), which is why the tamper tests above and in §2(c)–(e) exist.

## 5. Soundness bugs (all fixed on this branch; not merged into lane/pq-recursion-sha384)

Names used in the sub-sections above: F-c1 = B4, B-tr1 = B5, B-tr2 = B6.

| # | where | bug | fix | test | commit |
|---|---|---|---|---|---|
| B1 | uair.rs (ALU) | B-field range: lookup `(16rz, 0)` admits rz = t/16 mod p, so B ∈ [0, 1110015]; op → op − 1 relabels with B' = B + 2^20 on rows with B ≤ 61439: Zero → Bit accepts `a = 1`, Mul → Nop zeroes products. Present since the "op not bound to P1" fix (9b258a70a). | lookup the pair `(rz, 16rz)` | `nv_alu_relabel_zero_to_bit`, `nv_alu_relabel_mul_to_nop` | 2e36b0228 |
| B2 | verifier.rs (program generator) | native `TraceHeightsTooLarge` (LogUp count bound of the child) not checked | static assert at generation (heights are program constants) | — (static) | 2e36b0228 |
| B3 | builder.rs / isa.rs / uair.rs | `load_f`/`load_obs_f` were `Load` rows, all 12 coefficients free, only c0 observed: PoW leading-zero check vacuous; child PV cells used in the DAG carry unobserved extension parts | new op `LoadF` (29): c1..c11 = 0 | `nv_alu_base_load_pow`, `nv_tr_pow_free_limb` | 09fead0bc |
| B4 | glue.rs / hash.rs / isa.rs / uair.rs / builder.rs (42 B only) | commit word 5 sent as a word unit; GLUE accepts it as the 2-byte tail or as a full word, so each 42-B `observe_commit` has two transcript states | unit kind `UNIT_HALF = 3`; new op `UnitWT` (30) sends the tail with kind 3 | `nv_faithful_tail_framing_unique` | 274fe5ccf |
| B5 | transcript2.rs (HASH) | squeeze job ids free: two squeezes may share an id, mixing two chain states | column `ns`, `op_s·(job − 2^25 − ns) = 0`, `n.ns = ns + op_s` | `nv_tr_squeeze_id_collision` | 274fe5ccf |
| B6 | uair.rs / transcript2.rs / builder.rs | static-job op (flush/commit/PoW) not bound to the program: commit ↔ flush relabel changes tag and length unit | anchor carries the tag (P3) | `nv_tr_anchor_tag` | 274fe5ccf |
| H1 | builder.rs | PoW gadget leaves limb 0 unchecked | assert z ≤ 43 at generation | — | 274fe5ccf |

Program words change (LoadF, UnitWT, anchor tags), so P_NV changes; column count unchanged
(NvAir 70, HASH view 39 of 59), degrees unchanged (NvAir 8, SHA 21 at k = 3, 9 at k = 2).

## 6. What remains unproven or open

* **G1 — statement pass-through (F3, open, design change).** NvAir has one public value (level).
  The child's public values are LoadF cells observed into the transcript and used in the
  constraint DAG, so pv_i(T) can be *read off* T, but nothing links them to x_i: a level-d proof
  attests "there is an app proof under vk_app with *some* public values". The final verifier's
  "base-statement digest = claimed chunk statement" check has nothing to compare against. Fix
  (proposal, not done: it changes the public interface): level 1 computes D = SHA-384 of the
  app public values with a GLUE job and exposes D's limbs as public values; levels ≥ 2 expose
  the child's D unchanged (Pv-style rows `a = pv_k` for k = 1..; one opcode is left, 31, or a
  P2-indexed Pv). Until then Lemma 7.1 (F3) holds only for the level component.
* **T\*** (GAPS G-1/G-2): the audit is of the current chain transcript; §2(d)(vi) lists the
  columns, constraints and proof steps that change.
* **GKR / batch-constraint / stacking port fidelity** is established by differential testing
  (end-state transcript equality for 6 lever sets × 2 fixtures × 2 digest modes; 6,611
  single-element proof mutations with native-accepts ⇔ program-accepts, 0 mismatches), not by a
  line-by-line derivation. WHIR, the PoW, index and ×15 code were checked line by line. The
  tight-heights kernel in the univariate-skip encoding (PROOF S-10′ / GAPS G-6) inherits this.
* **lo6** (42-B truncation helper) is free inside GLUE and pinned only by its consumers (node
  tail views, root comparison); a new consumer of 42-B digests must re-check it (§2(c)).
* **Carry bounds** are computed for k = 3 (the default); k = 2 needs a re-run of the script.
* **Base-faithful** (layer 0) and **A-IC** are out of scope.
* `nv_app_binding` (17 GB peak) and the multi-level chain were not re-run on this branch (16 GB
  cap); the app rows are covered by the synthetic-table DOF run and `nv_bind_tamper`.

## 7. Later commits on lane/pq-recursion-sha384 to re-audit

One commit after 3c9d479ab touches the circuit (as of 2026-10-18 03:xx UTC):

* **32fb63327** "NV: unpadded program (ACC2/ACC at fixed early rows, even length), whole L1
  program as app table". It changes `builder.rs` (Acc/Acc2 allocated right after the data
  region, program length n even and < 2^prog_log), `uair.rs`/`nv_trace` (BIND covers the
  n-row program), the app table (whole L1 program incl. its Acc row). Re-check needed for §2(b)
  B-2: the step "P[L − 1] = Acc ⇒ every row of [0, L) is ALU" becomes "the Acc row at its fixed
  address is ALU (P ≠ 0), so every earlier row is ALU (C5); the BIND region pinned to n/2 rows
  by Acc's P0 = n − 2 receives `(y, P[y])` for every y < n, so all of [0, n) are ALU rows and no
  others" — the argument goes through unchanged in structure, but must be re-verified on the new
  code together with B-4's kernel (E2 now only over rows < n, the child's P must vanish beyond
  n). That commit does **not** contain any of B1, B3–B6: merging it with this branch needs the
  fixes re-applied (both edit `openvm-recursion-sha384.patch`).

Any later change to `nv/{uair,glue,transcript2,builder,verifier,isa}.rs` or
`sha384/compress2_*` must be re-checked against §2 and must keep the fixes; re-run
`scripts/run_faithful.sh` (the DOF test fails on any new undetected class).
