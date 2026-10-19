# NV verifies children with preprocessed (and cached) traces

Lane `lane/pq-nv-preprocessed`, branched from `lane/pq-recursion-sha384` @ 07822685a, 2026-10-19.

Labels: **[measured]** = run here; **[model]** = `prep_model.py` on top of the recursion lane's
`extrapolate_nv2.py` and the `size_cut3.py` milestones; **[estimate]** = counted from the design.

## 0. Result

* **NV now verifies children with preprocessed traces** (vk-committed, the commitment is a constant
  of the NV program) **and with cached traces** (the commitment is a proof value, observed in the
  preamble). Each one is one more stacked commitment, opened in WHIR round 0 at the shared query
  points.
* **No AIR, role or ISA change.** Only the program generator (`nv/verifier.rs`) changes, and it uses
  existing ops only. For single-commitment children the generated program is **byte-identical** to
  the one before (instructions, values, SHA jobs and transcript state; checked for the Fib and
  Interactions fixtures in the default and all-lever modes, §5).
* **Native side.** Upstream SWIRL (stark-backend v2) already proves and verifies preprocessed and
  cached traces, and the unified research backend keeps that working under every lever. There was
  one bug: the cached-trace committers in `test_utils` used `k` instead of the round-0 folding factor
  `k1`, so a cached child could not be proven under the k1 lever. It is fixed in the 3-line overlay
  `stark-backend-prep.patch`.
* **Tests.** All pass: honest preprocessed child, tampered commitment, wrong vk constant, other
  table, cached children, the O-2 multi-commitment rule, and program ≡ native on every proof element.
  Each runs at program level, and the rejections also run at the full NV constraint level (debug
  prover). They run in the default and all-lever modes, in both digest modes (§5).
* **Demo.** A toy base in the pq-wasm-base FETCH style has a preprocessed CODE table (8-felt records
  `[pc, op, h, fee, x0..x3]`) and a preprocessed byte RANGE table. NV verifies it, and its NV program
  does not grow with the code. The public-value design grows by about 85–105 rows per record (§6).
* **Cost per extra child commitment** [measured law, §4]. For each round-0 query the parent adds
  `7 + 2^k1·⌈w/2⌉ + 5·depth` program rows plus `depth + 1` SHA compressions, where depth is the
  round-0 Merkle depth. The query bits, the fold and the final check are shared. The fixed part is
  about 110 rows.
  * At L1 over the pinned base (b = 1, q0 = 536, depth 28) this is **+80k program rows and +15.5k
    compressions per commitment**.
  * Over the b = 2 base it is +41k and +8.0k.
* **Final layer.**
  * **Scenario A** (the plan this lane recommends): only the base carries extra commitments. The NV
    fixed point and FINAL do not change, so the final stays at **287,557 B [model]** (measured
    provisional 287,477 B).
  * **Scenario B1** (program binding by commitment, §8): **295.7 KB [model]**, or 293.2 KB once
    about 1k program rows are cut to get back to L = 24. App-table binding with a real L1 costs
    315.7–321.4 KB.

## 1. How the native protocol handles a preprocessed trace (what NV mirrors)

Source: `stark-backend-unified/crates/stark-backend/src/verifier/{mod,batch_constraints,stacked_reduction,whir,proof_shape}.rs`.

| step | native | NV program (this lane) |
|---|---|---|
| vk | `VerifierSinglePreprocessedData { commit, hypercube_dim, stacking_width }` per AIR. The vk bytes, this included, are hashed into `pre_hash` (keygen `vk_pre_hash`). | `pre_hash` is the first constant observed (unchanged). `pd.commit` is read from the same vk. |
| height | `hypercube_dim + l_skip == log_height`, otherwise `PreprocessedTraceHeightMismatch`. | Static `assert_eq!` in the generator. Heights are program constants, so the check costs no rows. |
| preamble | Per AIR, in AIR order: `observe_commit(pd.commit)` **instead of** `observe(log_height)`. Then the tight height and each cached commitment `observe_commit(c)`, then the public values. | `const_commit(pd.commit)`: constant digest cells, observed (UnitW/UnitWT + Anchor; the same code as the pre-hash). Cached: `load_commit(c)`, the same code as the main commitment. Same order. |
| proof shape | One `StackedLayout` per extra part, in sorted-trace order, after the common-main layout. **O-2: more than one layout with a first-order round 0 is rejected** (`FirstOrderRound0MultiCommit`). | The native `verify_proof_shape` is called (static: vk + heights only). The rule is inherited, and the generator refuses the program. |
| openings | All common-main openings are observed first, then per trace its other parts (preprocessed, then cached), each by its opening mask. Evaluator: `Entry::Preprocessed` comes from part 1; `Entry::Main{part_index}` with partitioned main = cached parts first, common main last. | The same observation order (`part_cells`), and the same mapping in the DAG evaluation. |
| stacking | Claims: commit 0 (every trace's common main), then commits 1.. in order. λ² powers over the concatenation. `q_coeffs` per commit. Openings are observed commit by commit. | `t_claims` concatenated, per-commit `col_base` offset by `lambda_base`, `qcs` per commit, `stack_open` flattened. Kernels and the eq memo are shared between commits; they depend only on (u, r, λ) and the slice position. |
| WHIR | μ powers over the concatenated stacking openings. Round 0: per tree `hash_coset(rows)` and `merkle_verify(commit_t, index, ·)` (or a multiproof per tree), with `codeword_vals[j] += μ^(offset_t + c)·row_t[j][c]`. | One Horner chain per coset row runs from the last column of the last tree down to column 0 of tree 0, which gives Σ μ^(offset_t + c)·row_t[c] with no extra rows. Leaf jobs and a Merkle path per tree are checked against `roots[t]` (main: loaded; preprocessed: constant; cached: loaded). The query index bits are shared. |

**Trust chain for the constant.** The preprocessed root is a constant of the NV program (Const and
ConstX rows), as are the vk pre-hash and the child's constraint DAG. The program itself is pinned by
BIND at the fixed-point levels and by V_d for the final layer, so the chain is: V_d pins the program,
the program pins (pre_hash, preprocessed root, DAG), and the root pins the table. A child that opens
any other table fails the round-0 Merkle root check. A program built for a different table differs in
its words, and binding rejects it.

## 2. Which NV roles and ops change

**None.** NvAir, the SHA AIR, TableAir, ByteAir, the GLUE/HASH/SAMP/BIND roles and the ISA are
untouched. The new program sites use only ops the audit already covers:
* Const/ConstX/Mul/Add (`ce`) and UnitW/UnitWT/Anchor (`observe_commit_cells`) for the constant root;
* Load/Unit12 for openings and stacking openings;
* Job/Horn/Horn2 for round-0 leaves of the extra trees;
* NodeJob/DigWS*/SibWS*/Dig/Sub/Zero for their Merkle paths and root checks.

### Change list for the auditor (lane/pq-nv-circuit-soundness; FAITHFUL.md style)

All changes are in `nv/verifier.rs` (`openvm-recursion-prep.patch`):

| id | site | change | mirrors (native) | audit note |
|---|---|---|---|---|
| P1 | `build_verifier` requirements | The `preprocessed_data.is_none() && cached_mains.is_empty()` assert is removed. A static height check `hypercube_dim + l_skip == log_height` is added. The `layouts.len() == 1` assert is removed. | `verifier/mod.rs` PreprocessedTraceHeightMismatch; `proof_shape.rs` layouts and the O-2 multi-commit rule | The O-2 rule is enforced by the native `verify_proof_shape` (`expect`), test `nv_prep_o2_round0`. |
| P2 | preamble | preprocessed: `const_commit(pd.commit)` replaces `obs1(log_height)`; cached: `load_commit(c)` after the tight height. Both are stored in `extra_commits[a]`. | `verifier/mod.rs` preamble loop | The order (pvs last) is checked by transcript end-state equality with native in every test. |
| P3 | column openings | `all_masks` per part; after the common-main loop, `part_cells[t]` = per trace its parts 1.. (load_obs, rot or 0 by mask). | `batch_constraints.rs` observation order | Nothing is sampled between the two loops (native observes parts 1.. inside its per-trace loop before evaluating). |
| P4 | DAG variables | `Entry::Preprocessed{offset}` reads `part_cells[t][0]`. `Entry::Main{part_index}` reads common main when `part_index == n_cached`, else `part_cells[t][has_prep + part_index]`. | `evaluator.rs` `eval_var` | Every other entry still panics. |
| P5 | stacking claims and q-coefficients | `t_claims` = common main, then parts 1..; per-commit `cmasks`, `col_base` offset `lambda_base`, `qcs[commit]`. `kern` and `em_memo` are shared between commits. `assert_eq!(lambda_base, t_claims.len())`. | `stacked_reduction.rs` `lambda_indices_per_layout`, `q_coeffs` | Kernel sharing is sound: the key fixes `(n, need_rot, src_row, col_log_height)` and the memo fixes `(bit, row_idx >> bit)`; neither depends on the commit. |
| P6 | stacking openings | Load/obs of every commit's openings in commit order; the final sum is over the flattened `qcs × stack_open`. | `stacked_reduction.rs` final sum | — |
| P7 | WHIR round 0 | `roots` = [main, extra commits in sorted-trace order]. Per query: leaf jobs per tree. A Horner chain per coset row runs over the trees from last to first (Horn2 pairs, odd remainder Horn, inside one tree), then `pending[tree]`, then `merkle_path(…, &roots[tree])` per tree (multiproof decompressed per tree). | `whir.rs` initial round (izip over commitments, mu_pow_iter) | Claim E (FAITHFUL §2(e)) holds per tree: the same cells are hashed (units of tree t's leaf job) and folded. The index bits are shared, as natively. |
| P8 | WHIR μ batching | `total_width` = Σ widths; `assert_eq!(widths.sum, total_width)`. | `whir.rs` `mu_pows` | — |

Program identity for single-commitment children (P1–P8 degenerate to the old code) is checked
byte for byte (§5).

## 3. Multi-commitment rule (O-2 round 0)

* A child with more than one commitment must run WHIR round 0 on the Johnson fallback; the
  first-order list is squared by the commitment batching. The native proof shape enforces this, and
  NV inherits it because the generator calls `verify_proof_shape`. `nv_prep_o2_round0` checks both
  directions: a preprocessed child with Johnson round 0 verifies, and with first-order round 0 the
  program generator refuses it.
* **Scenario A keeps every NV and FINAL proof single-commitment.** Only the base proof has extra
  commitments, and the base is in the Johnson (list-decoding m = 16 / 8) regime already
  (`bound-base.out`), so its queries do not change. The MCA batching term sees a few more stacked
  columns, which is negligible.
* **Scenario B1** (§8) gives every inner NV proof a second commitment. Their round 0 then goes to
  Johnson: penultimate q0 41 → 44 [model]. FINAL keeps one commitment, so the final proof's O-2
  round 0 is unchanged.

## 4. Cost

### 4.1 Per child commitment [measured law]

From the generator (NV_QCOST lines, `logs/`):

| quantity | rows |
|---|---|
| fixed: preprocessed root constant (2 × `ce` ≤ 2 × 23 rows) + observe (3) | ≤ 49 |
| fixed: cached root (2 Load + 3) | 5 |
| per opened column (load, obs, rot or zero obs) | 3 |
| per stacked column (eq chain over the high bits, kernel shared, λ² term, qc add; opening load+obs) | ≈ 6 |
| **per round-0 query** (coset-leaf lever): 1 leaf job + 2^k1·⌈w/2⌉ Horn2 + 5 per Merkle level + 2 Dig + 4 root check | **7 + 2^k1⌈w/2⌉ + 5·depth** |
| per round-0 query, without coset leaves: 2^k leaf jobs, 2^k − 1 node jobs (7 rows), 2^k Dig pairs | 2^k + 7(2^k − 1) + 2^(k+1) + 2^k⌈w/2⌉ + 5·depth + 6 |
| SHA compressions per round-0 query | depth + ⌈(2^k1·w·4 + 58)/128⌉ |

Measured checks:
* Small child (l_skip 2, n_stack 8, k = 3, no coset leaf, depth 8, 10 queries): 288 → 415 rows per
  round-0 query for one extra width-1 tree (+127 = 8 + 49 + 16 + 8 + 40 + 6), and 542 for two extra
  trees (preprocessed + 1 cached). The program goes from 8,138 rows (Fib) to 9,509 (preprocessed Fib).
* With all levers (k1 = 1, ×15, coset leaf, 42 B), see `logs/qcost-levers.log`.

The per-query term is a full Merkle path for every query, since NV verifies one path per query (the
multiproof lever only shrinks proof bytes). So **every extra commitment costs about one more WHIR
round-0 tree, whatever the size of its table**. A 2^16-row table and a 2^4-row table cost the same
once stacked to the full height. Hence:

* merge every fixed table into **one** preprocessed AIR (one commitment);
* do not preprocess tables only to save base cells (§6).

### 4.2 At L1 over the base (scenario A) [model on measured laws]

`prep_model.py`, pinned base shapes from the e2e slice (DESIGN-BASE §3; ×15 domain, k1 = 1, coset
leaves), per extra base commitment:

| base shape | q0 | depth | + L1 program rows | + compressions | + NvAir rows | + SHA rows |
|---|---:|---:|---:|---:|---:|---:|
| pinned b = 1, m = 16 (L1 = 623,802 rows) | 536 | 28 | **79,976 (+12.8 %)** | 15,544 (+64 %) | 244,316 | 1,989,632 |
| alternative b = 2, m = 8 (L1 = 400,280 rows) | 268 | 29 | **41,384 (+10.3 %)** | 8,040 (+50 %) | 126,396 | 1,029,120 |

* The b = 1 L1 with one extra commitment is ≈ 704k program rows. That still fits the 2^20 program
  region (ADDR_BITS = 20), but adds to G2's memory problem.
* Against code-as-public-values (pq-wasm-base today, about 95 NV rows per record, §6), one
  commitment breaks even at about **840 records (b = 1) and 435 (b = 2)**. Real contracts are 10^4 to
  10^5 instructions.

### 4.3 Effect on the final layer [model]

The baseline reproduces the recursion lane's corrected figure: 287,557 B, L = 24, NvAir 257,926 rows
(2^17.98). The measured stream-lane FINAL is 252,636 rows (3.6 % under 2^18) with 287,477 B
provisional.

| scenario | final | L | penultimate q0 | NvAir rows (vs 2^18) | SHA rows |
|---|---:|---:|---:|---:|---:|
| baseline (1 commitment, toy app table) | **287,557** | 24 | 41 | 257,926 (−1.6 %) | 780,288 |
| A: base / L1 only | **287,557** (no change) | 24 | 41 | unchanged | unchanged |
| B1: program commitment, app table kept | 296,493 | 25 | 44 (Johnson) | 285,501 (+8.9 %) | 975,872 |
| B1: program commitment, app table removed | 295,741 | 25 | 44 | 263,261 (+0.4 %) | 975,872 |
| B1, app table removed, 1k program rows cut | 293,197 | 24 | 44 | 261,761 (−0.1 %) | 975,872 |
| app-table binding, real L1 400k rows | 315,677 | 26 | 41 | 1,046,200 | 822,272 |
| app-table binding, real L1 624k rows | 321,445 | 26 | 41 | 1,499,694 | 843,264 |

In B1, the extra cost is about 2/3 cells and 1/3 GKR:
* The extra round-0 tree of the penultimate child adds q0 × (depth + 1) ≈ 1.3k compressions, which
  is +196k SHA rows.
* The three Johnson queries add their share.
* NvAir rises above 2^18, so GKR goes from L = 24 to L = 25 (+2.5 KB) until about 1k program rows
  are cut.

## 5. Tests [measured]

Files: `nv/prep_tests.rs` and `nv/prep_demo.rs`. Every test runs the program generator against the
native verifier. Every rejection also runs the full NV trace through the debug prover (all AIRs, all
buses), which must panic. Logs are in `logs/`.

| test | what | result |
|---|---|---|
| `nv_prep_honest` | Preprocessed Fib child (2 commitments): native verify, no program failure, transcript end state = native, the same program for two witnesses, full NV constraint check. | pass |
| `nv_prep_tampered_commitment` | (a) The vk's preprocessed commit is flipped with the pre-hash kept: Merkle root and transcript failures, and the circuit rejects. (b) An opened preprocessed row is tampered with: Merkle root, circuit rejects. (c) A preprocessed column opening is tampered with: constraint and stacking failures, circuit rejects. | pass |
| `nv_prep_wrong_vk_constant` | The program is built from a vk with a different pre-hash: rejected (program and circuit). | pass |
| `nv_prep_other_table` | A proof for table B under table A's program and the reverse, with the same AIR and heights and a different selector column, are rejected. A vk claiming B's commitment with A's pre-hash, on A's proof, is rejected by the Merkle root (program and circuit). | pass |
| `nv_prep_cached` | Cached children: CachedFixture11 (3 commitments), preprocessed + 1 and + 3 cached parts (3 and 5 commitments). Honest children pass the full constraint check. A tampered cached commitment in the proof is rejected. | pass |
| `nv_prep_o2_round0` | A preprocessed child with Johnson round 0 verifies; with first-order round 0 the generator refuses it. | pass |
| `nv_prep_every_proof_element` | Program ≡ native on every single-element mutation (EF/F + 1, digest bit flips, cached commitments included), for 3 fixtures (preprocessed Fib, preprocessed + 2 cached, toy base with 2 preprocessed AIRs) × 3 lever sets. | see `logs/elements.log` |
| `nv_prep_demo_toy_base` | §6. | pass |
| `nv_prep_demo_wrong_program` | An execution of another program (one record changed) is rejected under this program's NV (program and circuit). A tampered code-table opening is rejected. | pass |
| program identity | Single-commitment Fib and Interactions programs are byte-identical before and after (instrs, vals, jobs, transcript), in the default and all-lever + 42 B modes. | identical |
| fast NV suite | `nv:: config:: final_layer_domain o2_agreement dkt_cert`, 48 B and 42 B + coset leaf: everything passes except `nv_statement_passthrough`. That test fails identically on the unmodified head 07822685a: "child ALU height must equal ours", from the WIP `bind = bind \|\| child_nv` default; owner is the recursion lane. | 65/66 + 1 pre-existing |
| levers | `nv_prep*` with every child lever (k1 = 1, ×15, keep-domain, multiproof, Gruen GKR/ZC, derived claims, next mask, WHIR-Y, tight, wide PoW), 48 B and 42 B + coset leaf. | pass |

## 6. Demo: toy base with a preprocessed CODE table [measured]

`nv/prep_demo.rs`, `ToyBase`:
* EXEC fetches `[pc, op, h, fee, x0..x3]` from CODE (FETCH bus, the pq-wasm-base record layout) and
  range-checks a witness byte in RANGE (256 rows).
* The machine computes `acc' = acc + x0 + byte` with `pc' = pc + 1`, and outputs the final acc as a
  public value.

There are three variants:
* **Split**: CODE (preprocessed `[rec, valid]`, main `mult`, constraint `mult·(1 − valid) = 0`) and
  RANGE (preprocessed `v`) are separate AIRs: 3 commitments.
* **Fixed**: one FIXED AIR holds both tables as 10 preprocessed columns: 2 commitments.
* **Public**: the pq-wasm-base design today. Code records are public values with one boundary
  interaction per record, and RANGE is committed and derived: 1 commitment.

NV program rows, small child params (default levers):

| variant | n = 16 | 32 | 64 | interactions | commitments |
|---|---:|---:|---:|---:|---:|
| Public | 11,632 | 13,323 | 16,026 | 3 + n | 1 |
| Split | 13,067 | 13,069 | 13,066 | 4 | 3 |
| Fixed | 12,053 | 12,053 | 12,053 | 4 | 2 |

All levers + 42 B (`logs/demo-levers.log`): Public 9,600 / 11,607 / 14,308; Split 9,372–9,480;
Fixed 9,590–9,611. With tight heights the code table's committed height is a shape constant, so the
rows move with n.

* The preprocessed variants do not grow with the code. The Public variant grows by 84–106 rows per
  record. The ±3 rows in Split come from deduplicating the constant root limbs against the other
  program constants.
* At these toy parameters (10 round-0 queries, depth 8) one commitment costs about 1.3k rows. At L1
  over the real base it costs about 80k (§4.2).

**Recommendation for the WASM base (pq-wasm-base §3.3, §7.1).**
1. **CODE should be a *cached* table bound through the statement, not a preprocessed one.**
   * A preprocessed CODE makes the base vk, and so the L1 program, per contract. The L1 program
     contains the base pre-hash and the CODE root as constants. With one L1 program per contract, G2
     binding (§8, C_L1) needs one constant per contract.
   * With CODE cached, the root is a proof value that L1 observes. L1 exposes it in the statement
     digest, and V_d or the chain checks it against the contract's code commitment, a deterministic
     function of the code that can be precomputed per contract.
   * This removes the per-record boundary interactions, makes the base vk contract-independent (per
     code-size class, G6), and shrinks G5's 25 felts per instruction in the statement to one digest.
   * Cost: one extra round-0 tree at L1, about 80k rows (b = 1).
2. **Do not preprocess BYTE/RANGE16 for cost.** They save 1.44 M base cells, but cost one extra tree
   at L1 (+15.5k compressions, about 2.0 M SHA rows, about 165 M L1 cells at b = 1).
   * Preprocess a fixed table only if it buys more, for example a 2^24 RANGE-T that removes one
     lookup per consumed value (pq-wasm-base §7.3).
   * If several fixed tables are preprocessed, put them in **one** FIXED AIR.

## 7. Native side

* `stark-backend` v2 (pinned d667af5 + unified levers) supports preprocessed traces (keygen
  `PrepKeygenData` → `stacked_commit_odd` with `k_first`, the ×15 domain and coset leaves) and cached
  traces (`CommittedTraceData`, device `commit`) in the prover. The verifier handles them too
  (preamble, proof shape, batch constraints, stacking, WHIR multi-tree including the multiproof),
  and the transcript extractor has roundtrip tests for both.
* Found and fixed: `test_utils` (`commit_cached_trace`, `CachedFixture11`, `DummyInteractionChip`)
  committed cached traces with `params.k_whir()`, so round-0 leaves had 2^k rows instead of 2^k1.
  Under the k1 lever the prover failed (`MerkleTreeOpenedRowsOutOfBounds`). Fix:
  `params.whir.k_first()` (`stark-backend-prep.patch`). Keygen and the device `commit` already used
  `k_first`.
* Not changed, flagged: the device `commit` passes `tight_heights` for every committed matrix, but
  the proof shape builds cached layouts with `StackedLayout::new` (never tight). A cached trace
  committed through the device with the tight lever on would mismatch. The test utilities commit
  cached traces non-tight. Risk R5.

## 8. Binding design note: program binding at levels ≥ 2 by commitment (G2) [design, not built]

This refines the recursion lane's G2 note (`pq-recursion-nv/README.md`, "Gap G2") with this lane's
mechanism and costs. **No binding code is changed here**; the recursion lane owns binding and is
fixing G1.

**Problem.**
* Today L2 checks that its child L1's program columns P0..P3, opened at the child's batch point r,
  equal the fixed L1 program P_L1. It does this by evaluating Σ_x eq(r, x)·pw(P_L1[x]) over a data
  copy of P_L1 (the app table).
* Every level carries this table, because the program is uniform. That costs O(|P_L1|) = 400–624k
  rows over a real base.

**Why the commitment is cached and not preprocessed.**
* A preprocessed program commitment lives in the vk. The NV vk would then contain the commitment of
  its own program.
* But the program contains the child vk's pre-hash, which at the fixed point is its own pre-hash.
* That is circular. A cached commitment is a proof value, so the vk stays uniform and acyclic.

**Design B1.**
1. **NvAir program columns become a cached part.** P0..P3 (4 columns at the NvAir height) move to a
   cached main part (`PartitionedBaseAir::cached_main_widths = [4]`). The BIND role reads them via
   `Entry::Main{part_index: 0}`, and common main becomes the last part.
   * The prover commits the program trace as `CommittedTraceData`. It is the same for every proof of
     a level, so it is committed once and cached.
   * Every NV-family proof (L1, L2, …, penultimate) has two commitments: common main and C_P.
2. **The parent check is selected by the child's level flag** (the existing `flag = [child level ≠ 1]`):
   * **child level 1:** `(C_P − C_L1)·(1 − flag) = 0` on the two digest cells, about 6 rows.
     * C_L1 is a 42/48-byte constant of the NV program: the commitment of P_L1 at the NV parameters,
       computed at setup by the same `stacked_commit_odd` as a preprocessed keygen. It is
       deterministic and anyone can recompute it.
     * The child's program openings at r are then WHIR-bound to MLE(P_L1)(r), so no table is needed.
   * **child level ≥ 2:** BIND as today, gated by flag. The opening of the child's (witness) program
     tree at r must equal Σ_x eq(r, x)·pw(own P[x]), the ACC row.
   * The C_P cells already exist in this lane's generator (`extra_commits[a]`, a loaded root), so the
     check is one gated `assert_eq` per cell.
3. **FINAL keeps one commitment.** Its program stays in common main, and V_d checks it natively (G8).
   * FINAL verifies a two-commitment penultimate. It binds that child with
     `C_P(penultimate) = C_NV`, where C_NV is the constant commitment of the uniform NV program. This
     is not circular, because FINAL's program differs from NV's.
   * This closes the open "FINAL does not bind its child program" gap (README Q3) at about 6 rows,
     instead of option (a), uniform FINAL params, or option (b) with a 6k-row data table.
4. **The app table and the APPB role are removed.**
5. **Chain of constants:** V_d pins FINAL's program → FINAL pins the penultimate by C_NV → each NV
   level pins its child by BIND (child = own) → L2 pins L1 by C_L1 → L1's program pins the base vk
   (pre-hash, preprocessed roots, DAG) → the base pins CODE through the statement (cached root, §6).

**Size estimate [model, §4.3].**
* Final 295,741 B (L = 25), or 293,197 B with about 1k program rows cut to return to L = 24. This is
  independent of |P_L1|.
* Against app-table binding: 287,557 B with a toy L1, and 315,677–321,445 B with the real 400–624k
  row L1. B1 saves 20–28 KB at real scale and costs +5.6–8.2 KB against the toy figure.
* Per level:
  * +q0 × (7 + 2·1 + 5·29) ≈ 6.8k program rows, plus about 110 fixed rows;
  * +1.3k compressions (+170k SHA rows), plus three Johnson queries in round 0;
  * −10,988 app-table program rows and their data/BIND rows.

**Alternatives considered.**
* *Preprocessed program with the vk hash as a public value:* the pre-hash becomes a witness, passed
  through and checked by V_d. This avoids cached commitments, but the preamble's first observation
  becomes a witness, and that needs its own soundness argument.
* *In-circuit WHIR opening of C_L1 at r:* 60–80k rows per level.
* *Keeping the app table:* O(|P_L1|).

**For the recursion lane to decide:**
* whether the Johnson round-0 cost on inner levels (q0 +3) is acceptable;
* C_L1's exact parameters: it must be recomputed whenever the NV params, the digest mode, or the L1
  program change;
* whether NvAir's cached part interacts with the tight-heights lever (R5).

## 9. Open risks

* **R1 L1 size.** One extra base commitment adds about 80k L1 program rows and 15.5k compressions at
  b = 1. L1 is already at the ISA ceiling and above this machine's memory (G2/F3). The b = 2 base
  halves the cost. A CODE design that avoids a second tree, for example CODE rows inside the main
  commitment bound by a PREP side proof (DESIGN-BASE §2.2), would avoid it completely.
* **R2 Per-contract vk.** A preprocessed CODE table makes L1 per contract (§6). The recommended
  cached-CODE design moves the code binding into the statement. V_d or the chain must then check the
  CODE root against the contract's code commitment, which is a new native obligation, not yet
  specified.
* **R3 Scenario B1 cost.** It is +5.6–8.2 KB on the final and needs NvAir cuts to stay at L = 24.
  Inner levels go to a Johnson round 0. This is a model, not measured.
* **R4 Audit.** P1–P8 are generator changes with no new constraints. The constant-root mechanism is
  the one already used for the pre-hash, and the per-tree Merkle checks are the existing
  `merkle_path`. The auditor should still re-check Claim E per tree and the stacking λ-index offsets
  (P5).
* **R5 Tight heights and cached traces** (§7): the device-commit/proof-shape mismatch is native and
  not exercised by the NV tests.
* **R6 The pre-existing `nv_statement_passthrough` failure** on the recursion head (WIP bind
  default). It is not related to this lane.

## 10. Reproduction

```
research/near-compression/native/recursion/setup_prep_deps.sh        # trees under /data/illia/nearproof-deps/pq-nv-prep
cd $DEPS/openvm-sha384 && cargo test --release -p openvm-recursion-circuit --lib -- nv_prep
# all levers: CHILD_K1=1 CHILD_X15=15 CHILD_KEEP_DOMAIN=1 CHILD_MULTIPROOF=1 CHILD_GRUEN_GKR=1 CHILD_GKR_DERIVE=1 \
#   CHILD_GRUEN_ZC=1 CHILD_NEXT_MASK=1 CHILD_WHIR_Y=1 CHILD_TIGHT=1 CHILD_WIDE_POW=1 [NEARPROOF_DIGEST_BYTES=42 NEARPROOF_COSET_LEAF=1]
python3 research/near-compression/results/pq-nv-preprocessed/prep_model.py   # §4.2, §4.3
```
