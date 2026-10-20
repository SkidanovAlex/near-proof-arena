# pq-e2e-slice: the first end-to-end vertical slice of the PQ chunk proof

Lane `lane/pq-e2e-slice`, branched from `lane/pq-recursion-sha384` @ bfad906ec (NV, T\*, tag-8
statement passthrough, O-2 certificate gating, SHA AIR v4, program cut 1).

**What ran end to end (test-size parameters, measured):**

> real Wasm execution (Lean prepare/step fixture) → base proof (direct-Wasm EXEC/CODE/RANGE +
> chunk-statement AIR) → L1 (NV level 1) → L2 (NV, program-bound to L1 via the app table) →
> FINAL (`Sha384CpuEngine::new_final`, program-bound to L2 at the fixed point) → native V_d.
> V_d verifies under the final domain, checks the level, recomputes the tag-8 statement digest from
> the claim (ctx, enc S_0, enc S_S), and checks the final proof's program openings against a pinned
> program.

V_d accepts the honest chunk, and rejects a wrong S_S, a wrong ctx, a wrong S_0, the claim of a
different chunk, a proof of a different chunk, a tampered final public value, an inner-domain
proof, a wrong pinned level and a wrong pinned program. A forged final proof (a program that
verifies nothing and exposes a false statement) is accepted by V_d **without** the program check
and rejected **with** it.

**The main finding (G1) blocks the pinned program at real settings:** the NV program depends on
the child proof whenever the child uses PoW, so the program check that makes V_d sound cannot be
pinned. Program binding worked in this chain only because the test-size inner levels have no PoW.

The slice is honest about what the chunk statement contains: the Wasm execution of one prepared
function call is proven by AIRs; ctx, the state roots and the receipt are statement-carried stubs
(gap list below).

Labels: **[M]** measured here, **[E]** estimate, **[P]** proposal.

## 1. The slice: what is proven, what is stubbed

### 1.1 Why this base relation

The PQ stack (unified SWIRL backend, SHA-384/Ext12) has exactly one real NEAR-execution AIR set:
the byte-packed direct-Wasm tables (EXEC 157 / CODE 114 / RANGE 24 columns) for prepared
straight-line code with `i32.const`, `i32.add`, `drop`, `end`, one function, ≤ 8 stack slots. It
is the only PQ-stack AIR with a semantic theorem (`packed_literal_family_public_run_call`,
DESIGN-BASE §10 BF1). There is no trie, storage, receipt, account or host-function AIR on the PQ
stack, so "a function call that writes one storage key" cannot be proven; the smallest honest
chunk transition is **one function-call receipt whose contract executes `i32.const 12;
i32.const 23; i32.add; drop; end`** (chunk A, Lean case `positive`), embedded in a chunk statement
whose remaining components are carried as public values.

A second chunk B (Lean case `wrap`: `i32.const -1; i32.const 1; i32.add; drop; end`, other ctx and
roots) has the same code length, hence **the same base vk**, and serves as "a proof for a different
chunk".

Fixtures are actual Lean `prepare`/`step` outputs (`PreparedCodeTableFixture.lean`), turned into
packed traces by the unchanged generator (`generate_native_literal_recursion.py --packed-bytes`);
`make_slice_fixture.sh` reproduces `fixture/`.

### 1.2 Base AIR set and statement layout

| AIR | width | public values | interactions/row | max msg | degree | proves |
|---|---:|---:|---:|---:|---:|---|
| Literal0 (EXEC) | 157 | 191 | 74 | 27 | 6 | execution rows; entry / final machine state and the code table enter as public values |
| Literal1 (CODE) | 114 | 0 | 14 | 25 | 3 | the prepared code table (fetch multiplicities) |
| Literal2 (RANGE) | 24 | 0 | 1 | 1 | 2 | byte range table |
| ChunkStmtAir | 1 | 68 | 0 | 0 | 1 | **STUB**: carries [ctx (18) ‖ pre_state_root (16) ‖ receipt digest (18) ‖ post_state_root (16)]; constrains nothing about them |

No preprocessed or cached traces; heights 8 / 8 / 256 / 4 (all ≥ 2^l_skip). [M]

**Chunk statement** (what V_d recomputes, `ChunkClaim::public_values`), hashed by L1 under tag 8
as `[num_airs=4, 191, 0, 0, 68, pv_0.., pv_3..]`:

| part | fields | encoding | proven by |
|---|---|---|---|
| ctx | chain_id, height, prev_block_hash, gas_price, protocol_version | 18 limbs of SHA-384₄₂ (native tag 10 [P]) | **stub** (no AIR reads it) |
| enc S_0 | pre_state_root | 16 × 16-bit | **stub** |
| | receipt (receiver, method, prepaid, wasm code hash) | 18 limbs of SHA-384₄₂ (native tag 11 [P]) | **stub** (not linked to the code table or the entry gas) |
| | machine entry state (fn, pc, sp, done, fail, gas, 8 stack slots) | 27 felts (`boundary()`) | EXEC (first row) |
| | prepared code (5 entries: pc, fn, opcode, imm, fee, kind) | 5 × 25 felts | CODE ↔ EXEC fetch bus |
| enc S_S | post_state_root | 16 × 16-bit | **stub** |
| | machine final state | 27 felts | EXEC (last row: done = 1) |

`e2e_claim_encoding` checks that V_d's encoding, computed from the Lean fixture (not from the AIR
rows), equals the generator's EXEC public values byte for byte, and that every claim field moves
the digest. [M]

## 2. Commands

```sh
# deps (own tree; never another lane's)
research/near-compression/native/recursion/setup_e2e_deps.sh          # NEARPROOF_PQ_DEPS=/data/illia/nearproof-deps/pq-e2e
cd $NEARPROOF_PQ_DEPS/openvm-sha384/crates/recursion
export CARGO_TARGET_DIR=$NEARPROOF_PQ_DEPS/target
HEAVY_MEM=20G /data/illia/nearproof-deps/bin/heavy cargo test --release -j 8 -p openvm-recursion-circuit --lib --no-run
B=<the openvm_recursion_circuit-* test binary>
# fast tests (seconds; L1 circuit debug 44 s)
RAYON_NUM_THREADS=8 $B nv::e2e_tests:: --test-threads 1
# the slice chain (test size; ~2 h on 8 threads on the shared box)
HEAVY_MEM=24G /data/illia/nearproof-deps/bin/heavy env RAYON_NUM_THREADS=8 \
  NV_LOG_ROWS=18 NV_PROG_LOG=17 PARENT_N_STACK=17 PARENT_BITS=10 \
  E2E_FIXED=262144,524288,128,65536 E2E_SAVE_DIR=<dir> \
  $B nv::e2e_tests::e2e_slice_chain --ignored --test-threads 1 --nocapture
# (without E2E_FIXED the driver first runs phase A: A1, A2 at natural heights, A3 generated)
# real-settings base probe (base proof at the pinned S-24 shape + L1 program and heights, no L1 proof)
HEAVY_MEM=24G /data/illia/nearproof-deps/bin/heavy env RAYON_NUM_THREADS=8 NEARPROOF_DIGEST_BYTES=42 NEARPROOF_COSET_LEAF=1 \
  BASE_L_SKIP=2 BASE_N_STACK=22 BASE_LOG_BLOWUP=1 BASE_LIST_M=16 BASE_K=4 BASE_K1=1 BASE_LOG_FINAL=7 \
  BASE_BITS=268 BASE_QUERY_POW=24 BASE_KEEP_DOMAIN=1 BASE_MULTIPROOF=1 BASE_WHIR_Y=1 BASE_GRUEN_GKR=1 \
  BASE_GKR_DERIVE=1 BASE_GRUEN_ZC=1 BASE_NEXT_MASK=1 BASE_TIGHT=1 NV_LOG_ROWS=21 NV_PROG_LOG=20 \
  $B nv::e2e_tests::e2e_real_base_probe --ignored --test-threads 1 --nocapture
```

Fixture regeneration: `results/pq-e2e-slice/make_slice_fixture.sh` (needs the Lean caches; with
`E2E_INSTALL=1` it also rewrites `nv/e2e_literal_gen.rs`). Tests that read the fixture use env
`E2E_FIXTURE` (default: this directory's `fixture/`).

Code (overlay `native/recursion/patches/openvm-recursion-e2e.patch` on
`openvm-recursion-sha384.patch`): `crates/recursion/src/nv/e2e.rs` (base AIR set, `ChunkClaim`,
`SliceBase`, V_d = `verify_chunk` + `check_final_program`, forgery helpers),
`nv/e2e_tests.rs`, `nv/e2e_literal_gen.rs` (generated AIRs). No file of the recursion lane is
modified except `nv/mod.rs` (two module lines).

## 3. Measured: sizes and times per level (test size)

All on CPU, `RAYON_NUM_THREADS=8`, on the shared box (load average ≈ 38 on 32 cores during the
runs, so wall times are pessimistic). Log: `logs/chain-t10.log` (phase B, V_d, tampers, chunk B),
`logs/chain-t10-phaseA.log` (phase A). Proofs: `proofs/` (A_BASE, A_FINAL, B_FINAL, FORGED_FINAL).

**Parameters (test size).**
* Base: `child_params_small` (l_skip 2, n_stack 8, k 3, log_blowup 1, queries [10, 4, 2], PoW
  mu/fold/query/logup = 3/2/1/2 bits), degree 6. 5.2 query bits.
* NV (L1, L2, FINAL; FINAL with `new_final`): l_skip 2, n_stack 17, k 3, log_blowup 3, 10 query
  bits, queries [7, 5, 3, 3, 2, 2], m = 64, O-2 certificate-gated (no certificates loaded, so every
  round falls back to O-1), no PoW, 48-B digests. NvAir 2^18 rows (`NV_LOG_ROWS=18`), program
  region 2^17 (`NV_PROG_LOG=17`; 2^16 overflowed at the bound L2, see below).

| level | verifies | binding | program rows | heights (NvAir, SHA, Table, Byte) | proof B (gkr / relations / stacking / whir) | prove s | peak RSS |
|---|---|---|---:|---|---|---:|---:|
| base (chunk A) | — | — | — | 8, 8, 256, 4 (EXEC, CODE, RANGE, STMT) | 54,061 (8,456 / 30,720 / 1,552 / 12,188) | 0.03–0.5 | < 0.1 GB |
| A1 (phase A) | base | none | 22,318 | 2^18, 2^17, 128, 2^16 | 115,097 (44,408 / 26,016 / 4,816 / 39,672) | 642 | 9.0 GB |
| A2 (phase A) | A1 | none (passthrough) | 45,598 | 2^18, 2^19, 128, 2^16 | 136,089 | 858 | 18.2 GB |
| A3 (generated only) | A2 | — | 50,558 | 2^18, 2^19, 128, 2^16 (= A2: fixed point) | — | — | — |
| **B1 = L1** | base | none (level 1) | 22,446 | 2^18, 2^19, 128, 2^16 (fixed) | 136,089 (48,056 / 26,496 / 7,792 / 53,560) | 1,200 | 18.2 GB |
| **B2 = L2** | B1 | app table = B1's program (flag 0) | 74,574 | fixed | 136,089 | 1,373 | 18.2 GB |
| **FINAL** (`new_final`) | B2 | own program = B2's (flag 1) | 74,574 | fixed | **136,089** | 1,381 | 18.2 GB |
| V_d | FINAL | — | — | — | — | **0.104** | — |
| forged FINAL | nothing | — | 776 | fixed | 136,089 | 1,251 | — |
| chunk B: B1 / B2 / FINAL | | as chunk A | 22,446 / 74,574 / 74,574 | fixed | 136,089 each | 1,236 / 1,473 / 1,217 | 18.3–18.7 GB |

* The FINAL program equals B2's program (asserted): the chain reaches the fixed point at L2, so
  base → L1 → L2 → FINAL is the minimal bound chain (FINAL level = 3).
* The bound L2 program is 74,574 rows against 50,558 for the same level unbound (A3): +47 %, all of
  it the app table (the 22,446-row L1 program as data rows) plus the E tables of the binding. With a
  2^16 program region the bound L2 overflowed (`logs/chain-t10-phaseA.log`, first attempt).
* Every level has the same proof size because every level has the same vk and fixed heights.

**V_d results** (`E2E_VD_*` lines of `logs/chain-t10.log`):

| case | V_d, program pinned | V_d, no program pinned |
|---|---|---|
| honest chunk A | accept | accept |
| wrong S_S: final gas + 1 | reject (digest) | reject (digest) |
| wrong S_S: post-state root (stub field) | reject (digest) | reject (digest) |
| wrong ctx: height + 1 | reject (digest) | reject (digest) |
| wrong S_0: contract immediate 23 → 24 | reject (digest) | reject (digest) |
| claim of chunk B, proof of chunk A | reject (digest) | reject (digest) |
| proof of chunk B, claim of chunk A | reject (program) | reject (digest) |
| final public value limb changed | reject (final verify) | reject (final verify) |
| inner-domain proof (B2) presented as final | reject (final verify: domain) | reject (final verify: domain) |
| pinned level 4 instead of 3 | reject | reject |
| program pinned to the L1 program | reject (program) | n/a |
| pinned program, one word changed | reject (program) | n/a |
| **forged FINAL**: a 776-row program that verifies nothing and exposes the digest of a false claim (final gas 1, post-state root 0x07…), proven under the honest final vk | **reject (program)** | **ACCEPT** |
| honest chunk B under chunk A's pinned program | **reject** (gap G1) | accept |

**Fast tests** (`logs/fast-tests.log`, all pass): `e2e_claim_encoding`, `e2e_base_shape`,
`e2e_base_tamper` (final gas, final done flag, entry gas, code immediate, code-length header: each
rejected by the base AIRs' constraints/buses), `e2e_l1_program` (L1 transcript = native; statement
= claim A, ≠ claim B), `e2e_l1_circuit_debug` (L1 circuit over the base proof: every constraint and
bus, NvAir 2^17), `e2e_finding_program_depends_on_proof` (G1).

## 4. Real settings

**Base at the pinned S-24 shape** (DESIGN-BASE §3: l_skip 2, n_stack 22, b = 1, m = 16, k₁ = 1,
k = 4, log_final 7, 268-bit target with z = 24 query PoW, keep-domain, WHIR-Y, multiproof, Gruen,
derived claims, next-row mask, tight heights, 42-B digests, coset leaves). Logs:
`logs/real-probe-b1.log`, `logs/real-probe-b2.log`. [M]

| base shape | queries | base proof B (whir) | prove s | peak RSS | soundness | L1 program rows | L1 jobs / Merkle nodes | L1 natural heights (NvAir fixed at 2^21) |
|---|---|---|---:|---:|---:|---:|---|---|
| pinned b = 1, m = 16 | [536, 256, 83, 50, 36] | 921,857 (889,134) | 254–548 | 9.3 GB | 268.2 | **623,802** | 22,751 / 21,789 | SHA 2^22 |
| alternative b = 2, m = 8 | [268, 173, 72, 46, 33] | 669,189 (636,466) | 268 | 15.8 GB | 268.4 | 400,280 | 14,421 / 13,828 | SHA 2^22 |

* The query counts reproduce `bound-base.out` for the pinned shape exactly.
* L1's program over the pinned base does not fit the default layout: with NvAir 2^21 the program
  region 2^19 overflows (`program exceeds 2^19 rows`), and NvAir 2^22 is refused by the ISA
  (`log_rows - 1 <= ADDR_BITS`, ADDR_BITS = 20). It fits only at NvAir 2^21 with the program region
  at 2^20, the ISA's ceiling.
* **L1 was not proven at real settings** (lane cap 24 GB). Expected peak [E]: the L1 trace is
  NvAir 2^21 × 74 + SHA 2^22 × 83 ≈ 503M cells. The recursion lane's r268 A2 (128M cells) peaked at
  58 GB, so ≈ 0.45 KB per cell gives **≈ 230 GB** for L1 over the pinned base and ≈ 190 GB over the
  b = 2 base. Both exceed this machine (125 GB). The main session should not schedule it here; see
  G2.
* L2 and FINAL at real settings are the recursion lane's r268 shapes plus binding; the measured
  r268 chain (416,171 B final) ran **without** program binding (phase A and FINAL with `bind =
  false`), see F2.

## 5. Gap list (ranked by risk)

Ranked by risk. Owner lane or "new work" with an estimate [E].

1. **G1 (critical): the NV verifier program depends on the child proof, so no program can be
   pinned and V_d is not sound.** [M]
   * Mechanism: under T\* a PoW-run block B_j (j ≥ 2) is a job with id `TJOB_SQUEEZE_BASE +
     tr_blocks` (B5), where `tr_blocks` counts every squeeze block so far, and each such block also
     emits ALU `Unit1` rows for the witness. Squeeze-block counts vary between proofs because
     sampling rejects a 32-bit word with probability ≈ 1/16. So the program words (job ids) and
     even the program length depend on the child proof whenever the child has PoW.
   * Evidence: base proofs of chunks A and B (same vk) give L1 programs of 21,675 vs 21,676 rows
     with 4,609 differing rows (first: a `Unit1` job id 2^25 + 132 vs 2^25 + 123). With every PoW at
     0 bits the two programs are identical (19,752 rows). The final programs of chunks A and B
     differ, so chunk A's pinned program rejects the honest chunk B.
   * Consequences: (a) L2's app table (= the L1 program) cannot be a constant once the base has
     PoW (DESIGN-BASE pins z = 24); (b) the inner fixed point breaks once inner levels have PoW
     (z = 24/32 in every real setting; my test chain had none, which is why it bound); (c) V_d
     cannot pin the final program, and without the program check a forged final proof of a
     776-row program that verifies nothing is accepted for a false claim (measured).
   * Owner: **recursion lane**. Fix candidates: number PoW-run blocks per PoW instance (static
     PoW index + j) instead of by the global block count, and move the j ≥ 2 witness units out of
     ALU rows (hash-chain role constants, or a fixed maximum with selectors); or deliver the
     global block index as a witness on the chain bus with the chain's `ns` counter as the
     uniqueness argument. 2–4 days [E] plus a re-audit of B5 and of `tr_pow_blocks`.
2. **G2 (high): L1 over the pinned base shape is at the ISA ceiling and far above this machine's
   memory.** 623,802 program rows (NvAir 2^21 = the ADDR_BITS = 20 limit), ≈ 503M cells, ≈ 230 GB
   [E]. b = 2 gives 400,280 rows. And with app-table binding, **L2 must carry the whole L1 program
   as data** (624k rows), so L2 overflows the ISA too (see F2). Owner: base/aggregation lane (shape
   choice) with the recursion lane (L1 binding mechanism, ADDR_BITS). New work: 1–2 weeks [E].
3. **G3 (high): statement stubs.** ctx (no AIR reads chunk-header fields), pre/post state roots (no
   trie or storage AIR on the PQ stack; the call writes no storage), the receipt (not linked to the
   code table; prepaid → entry gas, i.e. the prologue and gas pre-charge, unproven). They are
   bound only through the statement digest. Owner: base AIR work; new work, large: the D1 host,
   trie, receipt and account tables (`nearAirV3D1`, 33 tables) on the PQ stack, months [E].
4. **G4 (high): Base-faithful only for the 4-opcode slice.** The packed EXEC/CODE/RANGE tables have
   a Lean refinement to `runCall`; `ChunkStmtAir` and the composition into a chunk relation have
   none; BF2 (Rust vk = Lean AIR) is open. Owner: final-soundness / direct-Wasm lanes.
5. **G5 (medium): the contract code is part of the statement** (25 felts per instruction, linear in
   contract size, hashed by L1 and recomputed by V_d). It should become a code hash bound by a
   PREP / code-hash side proof (P-PERF-8), which is what `build_l1_linked` exists for. Owner:
   base/aggregation lane, together with G7.
6. **G6 (medium): the base vk depends on the code length.** The generated EXEC AIR asserts the
   code-length header (public value 8) and CODE's count-bit zeros are sized by the trace height, so
   each contract size class has its own vk, hence its own L1 program and app table. The Lean family
   theorem is length-generic but the generated Rust AIR is not. Owner: direct-Wasm lane; 1 week
   [E] for a length-generic AIR.
7. **G7 (medium): `build_l1_linked` not ported.** The base/aggregation overlay (against 46b7e62e2)
   leaves 28 rejected hunks on bfad906ec. With the main proof only, the slice's L1 is equivalent.
   The multi-chain restart must also be re-checked against G1 (it resets the sponge but the PoW-run
   numbering is global). Owner: base/aggregation lane; 2–3 days [E].
8. **G8 (medium): the native final-program check did not exist.** Nothing in the recursion lane
   checked the final proof's program natively (DESIGN §2.1 assumes it); `nv_chain` verifies the
   final and checks the statement only. `e2e::check_final_program` implements it (re-derives the
   final-domain batch point with the backend's `verify_zerocheck_and_logup`, evaluates the pinned
   program's multilinear extension natively, compares with the NvAir P0..P3 openings); tested
   (accepts honest, rejects the L1 program, one changed word and the forgery). Owner: recursion /
   final-soundness lanes to review and adopt; blocked on G1 for real use.
9. **G9 (low): process-global hash levers.** Digest width (`NEARPROOF_DIGEST_BYTES`) and coset
   leaves are process-global env switches; the statement digest V_d computes depends on them. V_d
   must pin them (fail-closed today, but a configuration hazard). Owner: recursion lane (make them
   vk/params fields).
10. **G10 (low): hash domains of ctx and receipt.** The slice uses native tags 10 and 11 [P]. DESIGN-BASE
   §4 puts ctx under tag 9, which is the range-digest domain. Needs a spec decision.
11. **G11 (low): `nv_program_fib`'s proof-independence check is vacuous.** Its "second proof" is
   byte-identical (deterministic prover), so it could not catch G1. Use two different witnesses, as
   `e2e_finding_program_depends_on_proof` does. Owner: recursion lane; hours.
12. **G12 (low): level PV is meaningful only with binding.** Unbound passthrough levels expose level 1
   at every level. Owner: recursion lane (documentation; resolved by G1's fix).
13. **G13 (low): prover completeness.** The base prover takes generator rows; no full-witness
   validation (BF6). Owner: direct-Wasm lane.

## 6. Findings that should change other lanes' plans

* **F1 (recursion lane, final-soundness): G1.** Program binding (DESIGN §2.1, app table, BIND) and
  V_d's program pin assume a proof-independent program. Under T\* with PoW it is not. This must be
  fixed before any bound chain at real settings, and before the final-soundness argument can rely
  on "every level runs the same program".
* **F2 (recursion lane): the measured r268 chain and its 416 KB final ran without program binding.**
  Phase A and FINAL in `nv_chain` use `bind = false`; only phase B binds. A bound chain adds the
  app table and E tables (+47 % program rows at L2 here). At real settings the app table is the
  whole L1 program; over a real base that is ~400–624k rows, which does not fit in L2's program
  (ISA ceiling 2^20). The L1 → L2 binding needs a mechanism whose cost does not scale with the L1
  program (e.g. a preprocessed program commitment, or a native check of a committed L1 program
  digest), and the size model should include binding rows.
* **F3 (base/aggregation lane): the pinned base shape decides whether L1 is feasible.** Measured L1
  program: 624k rows at b = 1 / m = 16 (927 queries), 400k at b = 2 / m = 8. The shape choice
  should weigh L1 program size, ADDR_BITS and L1 memory, not only base LDE cost.
* **F4 (base/aggregation lane): the statement layout works as designed.** The tag-8 message over all
  AIRs' public values in AIR order is what the recursion lane's L1 and `build_l1_linked` both hash.
  V_d's independent encoding (from the Lean fixture) matched the AIR's public values exactly.
  Multi-AIR statements need no change.
* **F5 (direct-Wasm lane): the packed AIR set sits inside NV's envelope** (degree 6, ≤ 74
  interactions/row, message length ≤ 27, 191 + 68 public values, no preprocessed traces). Putting
  the code table in public values sidesteps NV's no-preprocessed restriction but makes the
  statement linear in code size (G5) and the vk per code length (G6).
* **F6 (final-soundness): final-domain separation works end to end.** An inner-domain proof of the
  same vk is rejected by V_d; the final vk is shared by all chunks (pre-hash equal for A and B).

## 7. What was taken from other lanes

* `lane/pq-recursion-sha384` @ bfad906ec: the whole NV stack (branch base).
* `lane/pq-base-aggregation` @ 364aa29b3: **no commits taken.** Its overlay
  (`openvm-recursion-agg.patch`, against 46b7e62e2) leaves 28 rejected hunks on bfad906ec (builder,
  circuit, glue, isa, mod, tests, transcript2, uair, config: it predates B1–B6, the G1 passthrough,
  O-2, SHA AIR v4 and the program cut). With the main proof only, `build_l1_linked` hashes exactly
  the message the recursion lane's L1 already hashes (`[num_airs, len_i.., pv..]`, tag 8, `PvD`),
  so the slice's L1 is `build_l1_linked` with k = 1 and no links. The port is gap G7.
* Direct-Wasm lane: the packed literal AIR generator and the Lean fixture generator, unchanged.

## 8. Recommended next lanes

1. **Recursion lane: fix G1, then re-run a bound chain with PoW** (inner z = 24/32), and replace
   the app-table L1 → L2 binding with a mechanism whose cost does not grow with the L1 program
   (F2). After that, V_d's `check_final_program` (G8) can pin a program and the forgery test turns
   into a permanent rejection.
2. **Base/aggregation lane: choose the base shape against L1 cost** (F3, G2) and port
   `build_l1_linked` onto the current NV tree (G7) with a code-hash / PREP side proof, which also
   removes the contract code from the statement (G5).
3. **Direct-Wasm lane: a length-generic packed AIR** (G6), so one base vk covers every contract size.
4. **New work: PQ-stack host/state AIRs** (storage write, trie walk, receipts, accounts) to retire
   the statement stubs (G3), starting with one storage write so the slice's chunk has a real state
   transition.
5. **Scheduling:** a real-settings L1 needs ≈ 190–230 GB [E], more than this machine. Do not run
   it here; revisit after G1/F2/F3.
