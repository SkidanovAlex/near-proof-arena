# pq-d1-envelope: can the classical NEAR AIRs be the post-quantum base layer?

Lane `lane/pq-d1-envelope`, from `integration/d1-tables` @ 86fab5fdd (D1 phase 1: `nearAirV3D1`, 30
tables). 2026-10-19, a one-day experiment.

Labels: **[M]** measured here, **[C]** computed from the Lean export by a script in this
directory, **[E]** estimate.

## 0. Verdict

**Yes, the classical tables can be reused, and the constraint polynomials do not change.** The
classical and PQ stacks share the base field (BabyBear). Every classical table is a row-local AIR
over that field with a cyclic next row and the selectors `isFirst`/`isLast`/`isTransition`, which
is exactly what SWIRL evaluates. Every bus multiplicity is a single bit, so the grand-product bus
becomes LogUp with count = that bit. The total worst-case multiplicity, `multBoundP` = 1.196·10^9 (2^30.16, public segments
included), is below p. That makes mod-p LogUp balance equivalent to the classical exact multiset
balance.

**Demo [M]:** 23 of the 30 `nearAirV3D1` tables were proven on the unified SWIRL backend and
verified by the native verifier. The tables are the Lean export as is (`np-lean-export-v3d1`,
interpreted, not rewritten). The traces are honest traces of the real D1a fixture
`public-d1/d1/00-h10007-s3` (13 transactions, 11 ops), rendered by the classical Rust generators.
The run used the seg-v1 shape at n_stack 18 with z = 24, a 268.2-bit target and 42-byte digests.
* The tables: SHA-256 ×2, all 7 trie tables, ChaCha/rng/shuffle, account, access key, bnd, srcp,
  qv, sort, tx, akm and the 3 relays.
* The proof is 1,261,284 B, proved in 82 s on 6 threads with a 1.6 GB peak, and verified in 0.16 s.
* The debug constraint checker passes.
* The public segments become a cached `TAPE` table whose commitment V_d recomputes. That check
  passes.
* Tamper results are in §5.

The seven tables left out are the five scheduler tables pinned at 2^22 rows (codec, scandist,
proc, mem, cmp), `rcptD1` (2^22) and `mrkD1` (2^19). They were left out for memory only, under the
lane's 16 GB cap; nothing about their constraints is different. Their bus traffic is supplied by a
synthetic `EXT` table, which is not sound and serves only as a stand-in.

**What does not carry over is the statement architecture around the AIR, not the AIR.**
1. The classical verifier puts verifier-computed messages on the buses (public segments, up to
   64 MiB of "tape"). SWIRL has no such mechanism.
2. The classical verifier recomputes that tape natively from claim + hint. The D1 hint carries
   the raw transactions, and the preparation runs Ed25519 natively (≈ 15 s at 4,096 transactions).
3. Six tables are rendered at a fixed 2^22 rows. They account for 99.6 % of the cells (W ≈ 150
   against the W ≤ 24 pin).
4. The D1 set is 5.5× over the 1,024 opened-column budget and needs 2^6 message length instead of
   2^4.

**Proof reuse:** the whole soundness side transfers verbatim. It is stated about
`HoldsP nearAirV3 (pubOf tape) tr` over `Fp`, with no reference to the protocol:
* `extractV3 : ExtractV3Stmt` (D0a);
* the D1 phase-2 `ExtractD1Stmt` work in progress;
* the completeness side `completeV3`, except its header and roll-alignment parts.

What must be built is one generic bridge, "SWIRL relation of the translated AIR ⇒ `HoldsP`", plus
the statement plumbing (§4).

**Recommendation (§6):** port the D0a/D1 state tables (trie, accounts, receipts, scheduler, SHA-256)
unchanged and keep direct-Wasm (lane/pq-wasm-base) for execution. Join the two on shared buses:
receipt → call boundary, storage/host-call bus → trie walk tables, gas/outcome back to receipts.
* Cost [E]: **12–20 agent-days** for the D1 tables standalone on PQ, including the Lean bridge.
* **+15–25 agent-days** for the join with direct-Wasm.
* Do not re-derive NEAR state semantics on the PQ stack.

## 1. The classical stack (np-udr-stark-v2), for reference

| item | classical (`np-udr-stark-v2`, `ZkFormal.Stark` / `ZkFormal.V2`) | PQ (unified SWIRL, DESIGN-BASE §3) |
|---|---|---|
| base field | BabyBear p = 15·2^27 + 1 (`source/src/field.rs`) | BabyBear: **same** |
| challenge field | Fp8 = F[X]/(X^8 − 11) | Ext12 = F[X]/(X^12 − 31) |
| IOP | univariate STARK, FRI over a coset LDE (2^22 rows → LDE 2^26), quotient split in `degree − 1` chunks, OOD at ζ and ωζ, SHA-256 Merkle/FS (RO model) | multilinear: zerocheck + LogUp-GKR, stacked WHIR (SHA-384, T*, 42-B digests) |
| AIR value | `ZkFormal.Air.Air` + `V2.AirP` (Lean is the single source; Rust reads `np-air-v2` JSON) | openvm `Air` + `InteractionBuilder` (here: the same JSON, interpreted) |
| rows | table `t` has 2^log rows, 1 ≤ log ≤ maxLog ≤ 22; `col c true` = row r+1 mod 2^log (**cyclic**) | 2^log rows, log ≤ l_skip + n_stack = 24; rotation is cyclic (`poly_common.rs`, "cyclic rotation kernel") |
| selectors | `isFirst`, `isLast`, `isTransition` (Lagrange interpolants; degree 1) | `is_first_row`, `is_last_row`, `is_transition`, **same** values on the domain |
| constraints | `Table.allConstraints` = user constraints + booleanity of every multiplicity bit; combined with powers of α | `assert_zero` each; batched by λ in the zerocheck |
| boundary constraints | none separate: boundary = selector · expr | same |
| bus | grand product over Fp8 with `auxGroup = 2`, multiplicity `Σ 2^k b_k` from bits (square-and-multiply chains for k ≥ 2), fingerprint `Σ α^j m_j + α^len (bus+1)` | LogUp-GKR, fraction `count / (γ − fp)`, fingerprint `Σ β^j m_j + β^len (bus+1)`: **same fingerprint shape** |
| bus semantics proved | `Holds.balance`: **exact multiset equality over ℕ** | mod-p sum per message (count_weight · heights < p per bus enforced by the verifier) |
| public input | `pub` = the prepared tape bytes (header reads `pub i`, i < numPub = 350) + **public segments**: the verifier itself sends/receives the tape records on buses (`pubMsgs`, `pubFit`, `maxPub` = 64 MiB) | public values per AIR, hashed into the tag-8 statement digest by L1; no verifier-side bus messages |
| statement | `prepD1 cb h` computed natively by the verifier from claim + hint (hint: raw txs, new txs, op bits, refunds; Ed25519 + SHA-512 native) | ctx + enc S_0 + enc S_S (DESIGN-BASE §4), V_d is light (0.1 s) |

Special primitives in the AIR:
* SHA-256 is in-AIR: `sha_t`/`sha_r`, 544 columns, 1,028 constraints, degree 4, two bins because
  of the classical 2^22 cap. It is NEAR's trie hash and must stay SHA-256; it has nothing to do
  with the PQ transcript hash.
* ChaCha20 is in-AIR (the scheduler RNG: `chacha`, `rng`, `shuf`).
* Ed25519 and SHA-512 are **native** in `prepD1` (D1 decision P-D1).
* There are no preprocessed or fixed columns. Range checks are in-row bit decompositions plus the
  `cmp` comparator table; there is no shared range table.

## 2. Per-table envelope [C]

`envelope.py` reads the Lean export and writes:
* `envelope-d0a.csv`: `nearAirV3`, 25 tables;
* `envelope-d1.csv`: `nearAirV3D1` phase 1, 30 tables, the export of lane/v3-d1-tables at phase 1
  (`out-v2/nearAirV3D1.json`, sha256 `db74ae50…`);
* `envelope-d1a7b.csv`: the 33-table variant of lane/v3-d1-a7b.

`fixture_cost.py` prices the real fixture heights (`fixture-cost-d1.txt`).

How to read the table:
* deg is the max constraint degree, with each selector counting 1.
* "opened (masked)" = width + columns read at the next row (SWIRL with the next-row mask).
* DAG nodes are counted per table after CSE. The SWIRL vk counts for the 23 proven tables total
  42,512.
* The fixture log is the classical render height on `00-h10007-s3`.

| # | table | family | width | maxLog | fixture log | constraints | deg | inter./row | max msg | rotated cols | opened (masked) | pub reads | DAG nodes | per-AIR envelope | SWIRL demo |
|---:|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---|---|
| 0 | sha_t | sha256 | 544 | 22 | 13 | 1028 | 4 | 17 | 34 | 541 | **1085** | 0 | 14616 | opened > 1024; msg > 16 (soft) | proved + verified |
| 1 | sha_r | sha256 | 544 | 22 | 13 | 1028 | 4 | 17 | 34 | 541 | **1085** | 0 | 14616 | opened > 1024; msg > 16 (soft) | proved + verified |
| 2 | node (A7) | trie | 188 | 22 | 13 | 480 | 4 | 23 | 34 | 147 | 335 | 0 | 1862 | msg > 16 (soft) | proved + verified |
| 3 | head | trie | 73 | 13 | 7 | 88 | 3 | 8 | 34 | 69 | 142 | 0 | 389 | msg > 16 (soft) | proved + verified |
| 4 | val (A7) | trie | 17 | 22 | 10 | 56 | 4 | 9 | 4 | 12 | 29 | 0 | 159 | fits | proved + verified |
| 5 | walk | trie | 56 | 22 | 10 | 82 | 4 | 6 | 7 | 8 | 64 | 0 | 396 | fits | proved + verified |
| 6 | uniq | trie | 53 | 22 | 10 | 78 | 4 | 2 | 4 | 42 | 95 | 0 | 337 | fits | proved + verified |
| 7 | ups (A7) | trie | 202 | 22 | 10 | 638 | 4 | 19 | 34 | 168 | 370 | 0 | 2794 | msg > 16 (soft) | proved + verified |
| 8 | chacha | scheduler | 272 | 22 | 1 | 381 | 4 | 4 | 20 | 67 | 339 | 0 | 3589 | msg > 16 (soft) | proved + verified (2 rows) |
| 9 | rng | scheduler | 158 | 22 | 1 | 200 | 3 | 2 | 20 | 45 | 203 | 0 | 1034 | msg > 16 (soft) | proved + verified (2 rows) |
| 10 | shuf | scheduler | 77 | 22 | 1 | 93 | 3 | 8 | 20 | 25 | 102 | 0 | 423 | msg > 16 (soft) | proved + verified (2 rows) |
| 11 | codec | scheduler | 91 | 22 | **22** | 255 | 4 | 16 | 34 | 52 | 143 | 0 | 865 | msg > 16 (soft) | EXT stand-in (memory) |
| 12 | scandist | scheduler | 119 | 22 | **22** | 261 | 4 | 10 | 11 | 28 | 147 | 0 | 1012 | fits | EXT stand-in (memory) |
| 13 | proc | scheduler | 64 | 22 | **22** | 119 | 4 | 11 | 20 | 34 | 98 | 0 | 427 | msg > 16 (soft) | EXT stand-in (memory) |
| 14 | mem | scheduler | 18 | 22 | **22** | 45 | 4 | 4 | 8 | 8 | 26 | 0 | 147 | fits | EXT stand-in (memory) |
| 15 | cmp | scheduler | 33 | 22 | **22** | 33 | 2 | 1 | 3 | 0 | 33 | 0 | 196 | fits | EXT stand-in (memory) |
| 16 | rcptD1 | receipts | 263 | 22 | **22** | 900 | 4 | 18 | 34 | 134 | 397 | 84 | 3285 | msg > 16 (soft) | EXT stand-in (memory) |
| 17 | acct | accounts | 16 | 19 | 7 | 40 | 4 | 13 | 6 | 8 | 24 | 0 | 121 | fits | proved + verified |
| 18 | akey | accounts | 7 | 16 | 1 | 19 | 3 | 3 | 3 | 4 | 11 | 0 | 58 | fits | proved + verified (2 rows) |
| 19 | bnd | receipts | 6 | 13 | 7 | 5 | 3 | 3 | 5 | 1 | 7 | 0 | 17 | fits | proved + verified |
| 20 | srcp (DD) | receipts | 63 | 22 | 10 | 134 | 4 | 5 | 35 | 46 | 109 | 0 | 502 | msg > 16 (soft) | proved + verified |
| 21 | size (A7) | trie | 57 | 4 | 4 | 74 | 4 | 2 | 2 | 8 | 65 | 4 | 379 | fits | proved + verified |
| 22 | qv | queue | 52 | 22 | 4 | 195 | **6** | 13 | 4 | 41 | 93 | 4 | 680 | fits | proved + verified |
| 23 | mrkD1 | receipts/merkle | 60 | 20 | 19 | 144 | 5 | 5 | 34 | 47 | 107 | 36 | 627 | msg > 16 (soft) | EXT stand-in (memory) |
| 24 | sort | receipts/merkle | 49 | 19 | 7 | 66 | 4 | 1 | 3 | 38 | 87 | 0 | 298 | fits | proved + verified |
| 25 | tx | d1-tx | 147 | 19 | 10 | 212 | 4 | 8 | 10 | 112 | 259 | 0 | 1235 | fits | proved + verified |
| 26 | akm | d1-tx | 70 | 22 | 7 | 181 | 4 | 8 | 5 | 37 | 107 | 0 | 702 | fits | proved + verified |
| 27 | kib | d1-relay | 7 | 22 | 10 | 3 | 2 | 2 | 6 | 0 | 7 | 0 | 19 | fits | proved + verified |
| 28 | plf | d1-relay | 34 | 13 | 4 | 4 | 2 | 3 | 34 | 0 | 34 | 0 | 44 | msg > 16 (soft) | proved + verified |
| 29 | rid | d1-relay | 9 | 19 | 1 | 9 | 2 | 2 | 3 | 0 | 9 | 0 | 46 | fits | proved + verified (2 rows) |

Every multiplicity is a single bit (`max_mult_bits = 1` in all 25 / 30 / 33 tables). There are no
preprocessed columns.

Variant a7b (lane/v3-d1-a7b, 33 tables):
* `nodeD1` 192 columns / 26 interactions, `uniqD1` 56 / 4, `kibD1` 15 / 3.
* Three new tables: `walkU` 58 columns, `nmem` 67 columns (message 33), `uval` 12 columns.
* All degree ≤ 4. The same verdicts apply. Interactions per row max 26.

### 2.1 Whole-AIR envelope [C]

| quantity | D0a (25) | D1 (30) | D1-a7b (33) | DESIGN-BASE §3 / NV today | verdict |
|---|---:|---:|---:|---|---|
| AIRs | 25 | 30 (+TAPE = 31) | 33 (+TAPE = 34) | ≤ 32 | D1 fits; a7b over by 2; **any join with direct-Wasm (12–18 AIRs) is over** |
| max degree | 6 | 6 | 6 | ≤ 8 | fits |
| constraints per AIR (max) / total | 1,028 / 6,442 | 1,028 / 6,851 | 1,028 / 7,079 | ≤ 2^14 | fits |
| opened columns incl. rotations (next-row mask) | 5,196 | 5,612 | 5,827 | ≤ 1,024 | **5.5× over** if the budget is per AIR set; only SHA (1,085) is over if it is per AIR |
| interactions per row (max) | 23 | 23 | 26 | NV verified 74 (pq-e2e-slice) | fits |
| message length (max, + bus) | 35 + 1 | 35 + 1 | 35 + 1 | ≤ 16 pinned (`log_max_message_length` 4) | **soft**: parameter 6 costs nothing (LogUp 331.3 bits in the demo vs target 268) |
| fractions Σ height·interactions, worst case (all at maxLog) | 2^29.55 | 2^29.64 | 2^29.74 | ≤ 2^28 | **soft**: 2^30 is still < p; about 2 LogUp bits |
| fractions at the real fixture | — | 2^27.92 | — | ≤ 2^28 | fits (just) |
| per-bus worst-case load, one side | max 2^27.0 (bus 0 recv) | 2^27.0 | — | < p (mod-p ⇒ ℕ) | fits on every bus (0 of 105 bus sides ≥ p) |
| committed cells at the fixture | — | 2.51 G (2^31.2) | — | W ≤ 24 at 2^24 (≈ 0.4 G) | **W ≈ 150** (99.6 % of cells are the six fixed 2^22 tables + mrk 2^19) |
| work at the fixture (cell-eq, E = 12) | — | 9.0·10^9 | — | — | 1.27 s on 1 H200, 0.04 s on 32 [E] |
| public values read by AIRs | 202 header bytes | 350 header bytes (`size` 202, `qv` 30, `rcpt` 84, `mrk` 36 max index) | same | NV hashes all PVs at L1 | fits (≈ 1.4 KB into tag 8) |
| public segments (tape) | 9 segments | 15 segments; fixture: 12,465 B, 3,097 messages, 2,407 distinct | same | none | **mismatch**, see M2 |
| min height | 2 rows | 2 rows (5 tables at 2 rows on the fixture) | — | NV: ≥ 4 rows (native SWIRL accepted 2 rows) | **mismatch for NV**, see M4 |
| preprocessed / cached | none | none | none | NV verifies both (lane/pq-nv-preprocessed, pq-recursion-sha384 @ 9159123be) | TAPE uses a cached trace |

## 3. Mismatch list (classical → SWIRL) and the cost of each

| # | mismatch | what changes | cost [E] |
|---|---|---|---|
| M1 | **Bus argument**: grand product with exact ℕ multiplicities → LogUp mod p | Count = the single multiplicity bit (`Σ 2^k b_k` in general); booleanity is already in the exported constraint list; send `+`, receive `−`; count_weight 1. Exactness needs every message's total multiplicity per side < p: the worst-case load per bus side is ≤ 2^27 from the tables (`envelope-*-buses.json`), and the
whole `AirP.multBoundP` = `multBound` + `pubBound` is 924,245,270 (D0a), 1,196,142,300 (D1) and
1,256,435,420 (a7b), all < p = 2,013,265,921. | Rust: done (demo). Lean: one `decide` fact `multBoundP < P` + the generic lemma (P1 in §4) |
| M2 | **Public segments** (the verifier puts the tape records on buses; `pubFit`, `maxPub` = 64 MiB) | A `TAPE` table: one row per distinct public message with its net count, interactions per (bus, length) key. The binding options: **(a)** cached trace whose commitment V_d recomputes from the tape (demo: works, as pq-wasm-base's CODE root), but the cached root must be carried up through every NV level to V_d; **(b)** hash the tape bytes in-AIR with the existing SHA-256 tables and expose the digest as PVs (≈ tape/64 compressions: 200 for the fixture, 10^6 at the 64 MiB bound); **(c)** derive the tape in-AIR from ctx (needs the hint data in-AIR, M3). | (a) 3–5 days incl. NV passthrough of the cached root; (b) 3–4 days (job wiring into `collect`) |
| M3 | **Hint + native `prepD1`**: the verifier receives the hint (raw txs + new txs, op bits, refunds; D1 hint ≤ 3,108 B on fixtures, up to ~8 MiB of tx vectors) and runs Ed25519/SHA-512 natively (≈ 3.6 ms/signature, ≈ 15 s at 4,096 tx) | Incompatible with a light V_d and the ≤ 300 KB final-proof target. Either V_d takes the transactions from public chain data (chunk body, bound by the header's tx root) and keeps the native prep, or the prep moves in-AIR (planned `sigV3` chip, V3-D3A-STUDY rec. 1: Ed25519 + SHA-512 AIRs). | design decision; in-AIR Ed25519 is weeks |
| M4 | **Heights**: classical 1 ≤ log ≤ maxLog (≤ 22) per table; SWIRL ≤ 2^24 stacked, NV needs ≥ 4 rows; per-table `maxLog` is **used by the soundness proofs** (capacity lemmas, `LinkWitness.witnessBytes_xOf`, the A7 bound B0) but SWIRL only enforces the stacked bound and the linear interaction constraints | (i) render ≥ 4 rows (`padLog22` already rounds to log ≡ 1 mod 3; a floor of 2 changes only the five 2-row tables), or NV small-height support; (ii) a per-AIR height cap check (`log_height ≤ maxLog_t`) in the vk / NV / V_d (NV's B2 already checks a child height limit). Without tight heights (zero rows beyond the declared height) no zero-row inertness proof is needed; keep power-of-two traces. | 1–2 days |
| M5 | **Fixed 2^22 renders** (codec, scandist, proc, mem, cmp, rcpt: 588 columns × 2^22 in every fixture; `ProcConcatGeometry.trace … height = 2^22 := rfl`), plus `padLog22` rounding (log ≡ 1 mod 3, a FRI roll-in artefact) | Soundness does not care (`HoldsP` for any log ≤ maxLog). Natural heights only touch the completeness renders (`Render/ChachaProcBus`, `CodecSanity`, `CodecChain`, the rcpt render) and would cut ≈ 99 % of the cells. Keeping them costs W ≈ 150 at 2^24 (NV per-query rows `7 + 2·⌈W/2⌉ + 5·depth`: ≈ 300 instead of ≈ 170) and memory. | keep: 0; natural heights: 5–10 days of render re-proofs |
| M6 | **Opened columns**: classical opens every column at ζ and ωζ; 5,612 claims at D1 with the next-row mask vs ≤ 1,024; SHA alone 1,085 (541 rotated columns) | no correctness issue; NV cost (stacking claims, ≈ 1–2 rows each) and DAG evaluation (≈ 51k nodes ≈ 51k NV rows at L1, vs 22k in the measured A2) | 0 (budget raise) or SHA re-layout (weeks; not recommended) |
| M7 | **Message length** 35 (+ bus) vs pinned 16 | `log_max_message_length` 4 → 6; NV evaluates fingerprints generically (`nv/verifier.rs`) | 0 |
| M8 | **Interaction count** 2^29.6 at worst-case heights vs 2^28 | raise `max_interaction_count` to 2^30 (< p); ≈ 2 bits of LogUp soundness out of 331; +2 GKR rounds in NV | 0.5 day (soundness re-run) |
| M9 | **AIR count**: 30 + TAPE fits 32; a7b (33) and any join with the direct-Wasm tables do not | raise the NV AIR cap (cost per AIR in the NV preamble), or merge `sha_t`/`sha_r` (identical AIRs; two bins only because of the classical 2^22 cap; merging changes `maxLog`, which touches capacity lemmas) | cap raise: NV-lane work, days; merge: not recommended |
| M10 | **Public values**: classical `pub i` reads the tape header (350 bytes) from one vector; SWIRL PVs are per AIR | each reading AIR gets `max index + 1` PVs (demo: `size` 202, `qv` 30 → duplicates); better: one header PV block (or the TAPE) and a header bus | 1 day |
| M11 | Challenge field Fp8 → Ext12; FRI/quotient chunks/`auxGroup`; SHA-256 transcript | protocol-only: no AIR content depends on them (`Table.auxDegree`, `quotCount` and the aux columns vanish; degree stays the user constraint degree, ≤ 6) | 0 |

No mismatch in the constraint form:
* no univariate-only constructs (no periodic columns, no quotient-domain assumptions, no
  `x`-dependent terms);
* boundary constraints are selector products;
* transitions use the cyclic next row on both stacks.

## 4. Proof reuse map

The classical certificate factors through `HoldsP` (`ZkFormal/V2/Air.lean:125`). It is a predicate
on a trace over `Fp` with **no challenges and no protocol**: heights, constraints on every row,
booleanity of the bits, `pubFit`, exact balance including public messages. So:

**Transfers verbatim** (if the PQ AIR is the same `AirP` value, which the demo ensures by
interpreting the Lean export):
* the AIR DSL and semantics: `ZkFormal.Air.Basic` (`Holds`) and `ZkFormal.V2.Air` (`AirP`,
  `PubSeg`, `pubMsgs`, `pubFit`, `HoldsP`);
* all table views and link proofs:
  * `ZkFormal.NearV3.{Tables, Extract, Link, Sched, Rcpt, Qv, Public, Candidates, Ids, Budget*}`;
  * `ZkFormal.Chacha.*`, `ZkFormal.Sha.*`;
  * `Assembly/{Good, FactorSound, LinkV3, LinkShape, LinkSource, A7SegMatch, ExtractV3Proof}`.
* **`extractV3 : ExtractV3Stmt`** (soundness: `prepD0 cb h = ok p → |tape| < P → HoldsP nearAirV3
  (pubOf tape) tr → ∃ k x, GoodV3 B0 cb k h p x`, then `factorSound` ⇒ `RelD0a`).
* The field-specific range facts survive because the base field is the same: u32 packing below
  P, the `(preparedBytes p oh).length < P` premise, 16-bit / 8-bit decompositions and the
  `2^29 < P` comparator bounds.
* The D1 phase-2 work in progress (`ZkFormal.NearV3.D1.*`, `ExtractD1Stmt`, `FactorSoundD1`,
  `LinkD1`). It is `HoldsP`-level, so every day spent there serves both backends.
* Completeness: `completeV3 : CompleteV3Stmt` (`Render/*`, the honest traces satisfy `HoldsP`)
  transfers. Its use of fixed heights (M5) is a choice, not a requirement.

**Does not transfer** (classical protocol; replaced by the SWIRL side):
* `ZkFormal.Stark.*` (Protocol, Verifier, Iop, Bcs, QueryBound, Laws, Statements, NpBounds);
* `ZkFormal.V2.G.*` / `V2.PG.*` / `Prover.Np.G.*` (`npVerifierP`, `admission_v2H`, `NpOkPg`);
* `NearAirCheckG2` (`nearAirV3_npOkPg_g2`), `nearV3_NVu`;
* the size bounds (`ZkFormal.Size.*`, `NearAirSize`, `v3MaxInner`, `nearAirV3D1_sizeMaxAligned`);
* `AlignedV3Stmt` / `RollAligned` / `trHdr` / `headerOk` (the header and roll-in parts of
  `RenderV3Stmt`);
* the hint wire codec (`Assembly/HintCodec`);
* the composition `nearV3_admission_of` → `nearV3_admission_final`.

The admission statement itself is classical-challenge-specific (`challengeParamsD0a`,
`.interp verifierDigest`); a PQ admission needs its own top theorem.

**New obligations** (these are the "re-prove" items; none touches a table proof):

| # | obligation | content | cost [E] |
|---|---|---|---|
| P1 | `holdsP_of_swirl` (generic in `AP : AirP`) | R_vk of `toSwirl AP` (constraints on all rows; per-message LogUp sum ≡ 0 mod p; heights) + TAPE rows = `pubMsgs AP pub` + per-AIR `log ≤ maxLog` + `multBoundP AP < P` + 1-bit multiplicities ⇒ `HoldsP AP pub tr`. Mod-p → ℕ: both sides < p (load bound) ⇒ equality. Bits: the booleanity constraints are in `allConstraints`. | 4–6 days |
| P2 | `multBoundP nearAirV3D1 < P` (and D0a) | one `decide +kernel` fact, as `nearAirV3D1_wf` | 0.5 day |
| P3 | BF2(a): the Rust SWIRL vk = the Lean `AirP` | the demo already interprets the Lean export; add the pq-wasm-base-style difftest (Lean expression values vs the vk's symbolic DAG at random points) or a codegen certificate | 1–2 days |
| P4 | TAPE / statement binding | (a) commitment binding of the cached TAPE root recomputed by V_d, or (b) SHA-256 digest of the tape in-AIR (the existing SHA table proofs give the digest; collision resistance becomes an assumption of the PQ statement) | 1–2 days (Lean side) |
| P5 | the SWIRL PIOP itself (vk accepts ⇒ R_vk) | not formalised for any PQ AIR (S-22 / BF2 in DESIGN-BASE §10). Shared with direct-Wasm, so no extra cost for the port. | — |
| P6 | PQ completeness: renders at ≥ 4 rows, TAPE generation | small; `CompleteV3Stmt` covers the trace | 1 day |

## 5. Demo [M]

* Code:
  * `research/near-compression/native/pq-d1-envelope/` holds the SWIRL interpreter of the
    classical `np-air-v2` export (`src/air.rs`), the driver (`src/main.rs`), `setup.sh` (an own
    copy of the pq-wasm-base unified SWIRL tree) and `run_demo.sh`.
  * `src/config.rs` is a verbatim copy of pq-wasm-base's (lines 1–669 of the openvm-sha384
    config).
  * `examples/np-udr-stark-v2/source/examples/d1dump.rs` is a cargo *example*, so nothing shipped
    changes. It runs `case_inputs_d1` / `render_cols` / `d1_tables`, which are the same
    generators as `npudr v3d1prove`, re-checks every classical constraint, and writes the traces,
    the public vector and `pubMsgs`.
* Shape: the seg-v1 shape at n_stack 18 (2^20 stacked height, W = 15), c = 1, b = 1, m = 16,
  k₁ = 1, k = 4, z = 24, a 268-bit target, 42-B digests, coset leaves, T*, and
  `log_max_message_length` 6. The soundness calculator gives **268.2 bits** (LogUp 331.3).
* Fixture: `oracle/fixtures/v3/public-d1/d1/00-h10007-s3`. Its tape is 12,465 B; the public
  messages are 3,097 in all, 2,407 distinct.

Results (`logs/prove-small.log`):

| | value |
|---|---|
| tables | 23 classical (SHA-256 ×2, node, head, val, walk, uniq, ups, chacha, rng, shuf, acct, akey, bnd, srcp, size, qv, sort, tx, akm, kib, plf, rid) + TAPE (cached, 2^11 × 47) + EXT (2^12 × 52) |
| cells | 11,351,046 |
| pre-check | every classical constraint on every row; every bus balances mod p (16,802 distinct messages); `EXT` only on buses of the excluded tables (asserted) |
| keygen | vk degrees = classical degrees (max 6, `qv`); 42,512 DAG nodes |
| debug checker | OK |
| proof | **1,261,284 B** (gkr 31,256 / relations 269,072 / stacking 2,660 / whir 956,964) |
| prove / verify | 82.1 s (6 threads, shared box) / 0.156 s; peak RSS 1.6 GB |
| V_d statement | the TAPE root recomputed from the public messages = the proof's cached commitment; header PVs = the claim's: OK |
| tables at 2 rows | chacha, rng, shuf, akey, rid: accepted by the native prover and verifier |

**Tamper suite (`logs/tamper-small.log`): 14/14 rejected.** Each case is re-proven from a mutated
trace and run through the native verifier and then V_d:
* +1 on one cell of node (twice), head, val, walk, uniq, ups, tx, akm, sha_t, size and srcp;
* a forged public message in TAPE;
* a changed header public value.

Every case fails at prove/verify, so no case reaches V_d. For TAPE that means the LogUp balance
breaks before the root check would be needed.

**What this checks and what it doesn't.** It checks that:
* every one of these classical constraint systems is accepted unchanged by SWIRL keygen, prover
  and verifier: degrees, cyclic next row, selectors, 2-row tables, PVs, interactions with
  35-field messages;
* honest classical traces satisfy them under LogUp;
* tampering is caught.

The EXT table is unconstrained, so the 7 excluded tables' bus partners are not proven here. Proving
all 30 needs the 2^22 tables, ≈ 2.5 G cells, which would not fit this lane's 16 GB cap.

The proof size (base layer, not sent to V_d) is driven by:
* WHIR at 536 round-0 queries;
* the relations part (269 KB), which scales with the number of AIRs and opened columns (M6).

## 6. Recommendation

**Port the D0a/D1 state tables unchanged; keep direct-Wasm for execution; join them on buses.**
Do not re-prove NEAR state semantics on the PQ stack, and do not port the classical protocol.

| option | what | cost [E] | verdict |
|---|---|---|---|
| A. port everything (incl. the classical statement/hint architecture) | 30 tables + TAPE, native `prepD1` in V_d | 12–20 agent-days | the AIR part is right; the native `prepD1` + hint conflicts with the light V_d / ≤ 300 KB (M3) |
| **B. port the state tables, direct-Wasm for execution (recommended)** | A's tables + statement binding via TAPE; Wasm EXEC/CODE/… from lane/pq-wasm-base; shared buses | **12–20** (D1 standalone on PQ) **+ 15–25** (join) agent-days | reuses `extractV3` and the D1 phase-2 proofs unchanged; direct-Wasm keeps its own Lean family theorems |
| C. don't port (re-derive state/trie/receipt AIRs for PQ) | new AIRs + new proofs | months (D0a took tens of lanes) | no reason: nothing in the AIRs is classical-specific |

Breakdown of B [E]:
* 3–5 days: TAPE binding + NV cached-root passthrough (M2).
* 1–2 days: heights — renders ≥ 4 rows and the per-AIR cap check (M4).
* 0.5 day: soundness re-run at message length 2^6 and 2^30 interactions (M7/M8).
* 4–6 days: P1.
* 0.5 day: P2.
* 1–2 days: P3.
* 1–2 days: P4.
* 1 day: P6.
* Optional, 5–10 days: natural heights (M5).

Prerequisite in all cases: the D1 phase-2 admission work, which is backend-independent.

**How the two would join** [E]:
* **Statement.** One base proof, with public values ctx ‖ enc S_0 ‖ enc S_S (DESIGN-BASE §4).
  enc S = the trie root (the classical tape header already carries the pre/post state roots and
  the outcome root) plus the TAPE root, or a SHA-256 tape digest. The classical header PVs become
  the statement's prepared header.
* **Bus ids.** The direct-Wasm buses 0–4 (STATE, FETCH, CH, R16, BYTE) collide with classical
  buses 0–4 (DIGEST, …). Offset one family; the classical buses go up to 71.
* **Call boundary.** `rcptD1` (or a new `call` table) sends a CALL message: receipt index r,
  receiver, method id, args digest, prepaid gas, deposit, code root. The Wasm BOUNDARY receives it
  as its entry state; today these are public values (the e2e-slice stubs G3/G4). The code root
  binds to the account's `code_hash` read through the account/trie walk.
* **Storage host calls.** `storage_read` / `storage_write` / `has_key` rows in the Wasm tables send
  (account, key, value, time) on a STORAGE bus. A new storage table answers it with walks on the
  existing trie buses: `walk` / `val` VBYTES for reads, `ups` for writes. That is the same pattern
  the D1 `tx` table uses with `walk` (W_TX walk ids) and `akm` with AKMEM.
* **Time.** The classical MEM time is `r + 1 + T0` (per receipt or op). The Wasm channel time is a
  global row clock. Use (receipt index, step) or a single global clock across both.
* **Outcome.** Gas burnt, result and promise receipts go back to `rcptD1`'s outcome/refund rows.
* **Shared range tables.** Wasm's RANGE16/BYTE can serve classical range lookups later (an
  optional cost cut).
* **Lean.** The D1a relation has no contract execution. The join needs the D3α-style composition
  (`runCall` inside receipt application), i.e. a receipt-level fold lemma (DESIGN-BASE BF4) over
  the D1 extraction and `wasm_base_sound`.

**Risks:**
1. M3 (statement architecture) is the real design work. The AIR port is not.
2. The mod-p margin of the global argument is only 1.68× at D1 (1.60× at a7b, 2.18× at D0a).
   `pubBound` counts `maxPub / width` = 2^26 for each width-1 segment. Raising a `maxLog`, adding
   interactions or adding segments can break it. A per-bus version of P1 still has a wide margin
   (table load ≤ 2^27 per bus side).
3. The fixed 2^22 tables make the base proof W ≈ 150 (memory, L1 cost) unless the renders are
   re-proved at natural heights.
4. The AIR count and opened columns exceed the pinned NV envelope once joined with direct-Wasm;
   the NV caps must rise.
5. P5 (the SWIRL PIOP) is unformalised, as for every PQ AIR.
6. D1 phase 2 is incomplete, and a7b adds 3 tables.

## 7. Files

* `envelope.py`, `envelope-{d0a,d1,d1a7b}.csv`, `envelope-*-buses.json` (the per-bus worst-case
  loads).
* `fixture_cost.py`, `fixture-cost-d1.txt`.
* `logs/prove-small.log`, `logs/tamper-small.log`.
* `../../native/pq-d1-envelope/` (the demo) and
  `examples/np-udr-stark-v2/source/examples/d1dump.rs` (the trace dump).

Reproduce:
1. `research/near-compression/native/pq-d1-envelope/setup.sh`
2. `AIR=<nearAirV3D1.json> research/near-compression/native/pq-d1-envelope/run_demo.sh <out> prove`

`nearAirV3D1.json` is the `np-lean-export-v3d1` export; it is not in git. The run used sha256
`db74ae50ac0cb5065ea6e30aa433fb785aed0cf375b2773680bac960af41f396`.

Nothing pinned was touched: the spec, the challenges, `nearAirV3` and the D0a certificate are
unchanged, and so is the shipped `np-udr-stark-v2` package (the new file is a cargo example).
