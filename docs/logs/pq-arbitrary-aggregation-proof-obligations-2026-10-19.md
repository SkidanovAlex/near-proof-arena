# Proof obligations for the "final PQ proof under 300 KB, arbitrary aggregation" paper

Status: 2026-10-19. Planning document. Companion to `docs/logs/pq-paper-audit-2026-10-19.md`
(paper draft held until the join lands) and `docs/logs/pq-gap-analysis-2026-10-19.md` (end-to-end
gap).

Purpose: fix exactly what must be **proved** (and separately what must be **measured**) before a
paper can claim, without qualification:

> A single ≤ 300 KB post-quantum proof certifies a NEAR chunk, for **any** segmentation of the
> chunk into `S` segments and **any** aggregation tree shape, using only proven bounds (no
> proximity conjecture, no capacity-regime assumption, no random-words heuristic).

This is a proof backlog, not a status report. Each item has an owner lane, an estimated size, and
whether it is a Lean obligation, a pen-and-paper obligation, or a measurement.

---

## 0. What "arbitrary aggregation" must mean

The claim has four independent quantifiers. Each needs its own theorem; "arbitrary" is only
credible if all four are covered.

| quantifier | range | why it is not free |
|---|---|---|
| **S** (number of segments) | any `1 ≤ S ≤ S_max` | soundness union, statement indices, and the digest preimage all mention `S` |
| **arity `k`** | `N1` any `k`, `N2` `k = 2`, or `k`-ary with preprocessed program | in-circuit program binding is quadratic in `k` above level 1 |
| **depth `d`** | any, up to the query budget | per-proof union bounds fail; only the single-database theorem scales |
| **tree shape** | balanced, ragged, repeated children, single-child nodes | continuity/index checks and the root digest must reject ragged or dropped children |

The current evidence covers a **linear** chain (`d ≤ 7`, one proof per level) and a **2-to-1 and
8-to-1 prototype** at level 1. There is no theorem for the general tree yet: §9.1 of `DESIGN-BASE.md`
is a sketch, and it explicitly notes that the per-proof union bound **fails** at ~295 proofs
(`2^-126.5`), so the tree claim depends on the single-database theorem.

### 0.1 Two scopes to keep separate

| scope | gas | segments | status |
|---|---|---|---|
| **A. signed challenge (`G_α`)** | `3.451e12` | ~13 | within reach of the join |
| **B. 1 Pgas** | `1e15` (289.8× A) | ~1,880–3,760 | theory covers it; **no measurement above `G_α`**, and the challenge excludes it |

A paper claiming "arbitrary aggregation" must say which scope it quantifies over. Proving the
theorem for arbitrary `S` is possible; **measuring** it at 1 Pgas is a separate, unstarted project
(`pq-gap-analysis` §3).

---

## 1. The paper's theorem skeleton (what the proof must instantiate)

Notation follows `PROOF.md`. `R_vk` is the SWIRL trace relation; `V_d` the native final verifier;
`P_i` the NV program at level `i`.

```
Theorem (target).
Let C be a chunk claim. Let S ≥ 1 and let T be any aggregation tree over segments j = 0..S−1
with arity k_v and depth d. Assume:
  (H1) T* transcript (counter-mode squeeze, PoW bound to the query block);
  (H2) NV-faithful(i) for every node i;
  (H3) Base-faithful for the segment vk: R_vk_seg(x) ⇒ segRel(seg_j);
  (H4) Join-faithful: the two side proofs over HOSTQ/HOSTR/HOSTB compose to RelD3a;
  (H5) A-IC(τ);
  (H6) proximity inputs as in §4 (DKT26 O-1/O-2, any evaluation set);
Then for every quantum adversary with ≤ 2^64 oracle queries,
  Pr[V_d accepts π_d ∧ C is false] ≤ 2^−128,
and |π_d| ≤ 300 KB whenever the final-layer shape is one of the measured/modeled shapes.
```

The theorem is **not** currently provable end to end. The obligations below are grouped by which
hypothesis they discharge.

---

## 2. Obligation ledger

Status codes: **done** (proved and in tree), **hand** (complete prose proof, unreviewed),
**sketch** (argument only), **open**, **measure**.

### 2.1 (H1) Transcript — `T*`

| id | obligation | status | where | notes |
|---|---|---|---|---|
| T1 | Counter mode ≡ one long-output oracle call (`t → 2t`) | **hand** | `PROOF.md` Lemma 6.3 | elementary; needs review |
| T2 | Grinding credit inside one call: `2^-z (1−δ)^t` | **hand** | `PROOF.md` Lemma 5.1 | holds only under `T*`; review |
| T3 | Multi-call squeezing covered by CDHZ long-output model | **hand** | `PROOF.md` §6.2, GAPS G-1 | cites CDHZ; check the `t → 2t` factor in the final bound |
| T4 | `T*` implementation matches the model (native, prover, NV) | **done** (tests) | `pq-recursion-nv` README, `nv_tstar_tamper` | 30 squeeze / 12 PoW / 16 PoW-run blocks; 3 negatives. The paper needs a **refinement statement**, not just tests: program ≡ spec transcript |
| T5 | Refinement lemma: NV transcript circuit computes exactly the `T*` transcript | **open** | — | this is part of NV-faithful (H2); currently argued by difftests |

**Paper consequence:** T1–T3 are prose-provable in days. T5 must be folded into the NV-faithful
lemma, not left as "tests pass".

### 2.2 (H2) NV-faithful and recursion composition

| id | obligation | status | where | notes |
|---|---|---|---|---|
| N1 | `Theorem 6.4`: QROM straight-line KS for a *family* of layers, one database, truncated commitments | **hand** | `PROOF.md` Thm 6.4 | highest-value item to review/Lean |
| N2 | `Theorem 7.4`: linear-chain composition, error independent of `d` | **hand** | `PROOF.md` Thm 7.4, given A-IC | |
| N3 | **`Theorem 7.4-tree`**: composition over an arbitrary arity/depth tree, `(F3-tree)` | **sketch** | `DESIGN-BASE.md` §9.1 | **the central new theorem for "arbitrary aggregation"** |
| N4 | Error independent of node count for arbitrary `S` | **sketch** | same | follows from N1's single database; must be stated and proved, not asserted |
| N5 | A per-node union is *not* needed (or, if used, raise every target by ~8 bits) | **open** | `DESIGN-BASE.md` §9.1 caveat 2 | the current cross-check fails at 295 proofs; decide which route |
| N6 | NV-faithful(i): the NV circuit arithmetises `V_{i−1}` exactly (`F1–F6`) | **open** (in progress) | `pq-nv-circuit-soundness` | `FAITHFUL.md`; needs the `T*` refinement (T5) folded in |
| N7 | Program pinning: `V_d` checks the final program openings against the pinned program | **done** (measured) | `pq-e2e-slice`, G2 gate | 776-row forgery accepted without, rejected with |
| N8 | Program convergence / anchors: `BIND` at the fixed point, program independent of child heights | **done** (measured) | `pq-recursion-sha384` @ 9159123be | G2 chain L5 binds; needs the refinement statement |
| N9 | Preprocessed children in NV (FETCH code table, k-ary program commitment) | **done** (measured) | `pq-nv-preprocessed` | program ≡ native on 19,365 elements; enables R3 below |

**Paper consequence:** N3+N4 are the theorems that make the word "arbitrary" true. They are the
main piece of new theory the paper would contribute beyond the existing linear-chain result.

### 2.3 (H3) Base-faithful (segment relation)

| id | obligation | status | where | notes |
|---|---|---|---|---|
| B1 | `wasm_base_sound` for families 1–4 (const/add, div/rem, memory, globals, calls) | **done** (Lean) | `pq-wasm-base` §11–13 | i32/i64 subset |
| B2 | `wasm_base_sound_host`: host calls with an abstract response oracle | **open** | `JOIN-INTERFACE.md` §4.2 | blocked by the **gas invariant** (`RelW.gas` cannot be re-established after a host call) |
| B3 | Gas invariant fix: budget after a host call is `g_after`, not `R·S + g0` | **open** | `JOIN-INTERFACE.md` §4.2a, commit 206857297 | **the real blocker**, not the chip |
| B4 | `Base-faithful` for a real segment AIR set `seg-v1` (AIR ⇒ `segRel`) | **open** | `DESIGN-BASE.md` §10 BF1 | only a 4-opcode PQ slice exists |
| B5 | SWIRL relation ⇒ Lean AIR semantics (`R_vk` ⇒ `HoldsP`) | **done** | `Bridge.lean: holdsP_of_swirl` | no `sorry` |
| B6 | vk ⇔ Lean AIR equality (Rust symbolic DAG vs Lean `Air`) | **open** | BF2(a) | codegen or certificate |
| B7 | Zero-row inertness under tight heights (F5 analogue) | **open** | BF2(b) | |
| B8 | `multBoundP < p` for the joined/segment table set | **open** (one `decide`) | D3-join P9 | kernel-checkable day job |
| B9 | Receipt-level fold lemma across calls | **open** | BF4 | `run_foldSegments` exists within calls |
| B10 | `prepChunk` / ctx digest; `init C` / `final C` from `ClaimV3` | **open** | BF4 | |
| B11 | Segment split correctness for arbitrary `S` (any cut at receipt boundaries) | **open** | `Segment.lean` + BF4 | needed for "arbitrary S" completeness |
| B12 | Base-faithful difftest at segment granularity on D3 fixtures | **open** (measure) | BF5 | |

### 2.4 (H4) The Wasm ↔ state join

| id | obligation | status | where | notes |
|---|---|---|---|---|
| J1 | Bus partition: classical `< 128`, Wasm `0–6`, host `200–202` | **done** (kernel) | `Join.lean` | |
| J2 | `JoinStmt`, `HostAnswer`, `HostResp`, `WasmRunStmt`, `join_additive` | **stated** | `JoinFold.lean`, D3-join §1 | statement fixed, theorem not proved |
| J3 | `Joint → RelD3` composition (`Compose`) | **open** | D3-join P2 | needs J4, J5 |
| J4 | `WasmHalf`: `wasm_base_sound_host` | **open** | D3-join P3 | = B2, B3 |
| J5 | `StateHalf`: ContractData walk consumes `HOSTB`; `upsV3` applies the write log | **open** | D3-join P4 | prefix/path already kernel-checked |
| J6 | `CodeBound`: receipt → `code_hash` across the two proofs | **open** | D3-join P5 | assumed today |
| J7 | `HOSTB` byte binding (Wasm memory range ↔ state bytes) | **open** | D3-join P6 | needs the MEMIO mover |
| J8 | `HOSTR` gas binding (`g_after`) | **open** | D3-join P7 | gas half of the interface |
| J9 | HOST chip + import-call `check` + spec `callHost` | **open** | `pq-host-chip` | 10–15 days; design only |
| J10 | Ed25519 / SHA-512 in-circuit (`sigV3` chip) | **open** | — | nothing on the PQ stack verifies a signature |
| J11 | ContractData prefix/path/`cdWalkV3` facts | **done** (kernel) | `NearV3/D3/ContractData.lean` | |
| J12 | Joint table set soundness under SWIRL | **open** | D3-join P10 | not formalised for any PQ AIR |

### 2.5 (H5) A-IC

| id | obligation | status | where | notes |
|---|---|---|---|---|
| A1 | `Theorem O`: query-only oracle models cannot prove hash-only recursion | **hand** | `aic-research/LEMMA.md` | makes A-IC necessary, not lazy |
| A2 | A-IC(τ) stated exactly, with the time bound | **done** (adopted) | U-11/U-12 | |
| A3 | Any replacement (time bound / AROM / native recheck) analysed | **sketch** | `LEMMA.md` Cor O.2 | paper must state this is the one non-standard assumption |

**Paper consequence:** A-IC is a *limitation* the paper must foreground. It is not a conjecture the
authors chose; A1 shows there is no alternative in this model.

### 2.6 (H6) Proximity inputs — no new conjecture

| id | obligation | status | where | notes |
|---|---|---|---|---|
| P1 | WHIR Thm 5.2 (corrected, `Puš26` Thm 5.3) applies to our protocol | **cited external** | `PROOF.md` §4 | refereed + thesis |
| P2 | BCGM Thm 9.2 / BCHKS25 Thm 1.5 hold for arbitrary evaluation sets | **cited external** | x15 `SOUNDNESS.md` | |
| P3 | `c·2^K` domain lemma (smoothness edit) | **hand** | x15 `SOUNDNESS.md` Lemma 3.1 | four properties; review |
| P4 | **DKT26 → WHIR lift** (RS-level MCA/list ⇒ WHIR rbr) | **open (paper-level)** | GAPS S-28 | the main missing proximity step |
| P5 | DKT26 Thm 5.12 + Cor 7.7/7.8 (O-1), Lean | **done** (Lean) | ArkLib pin, `DKTGlue.lean` | |
| P6 | DKT26 first-order certificates (O-2), 129/129 deployed | **done** (Lean) | `DKTCertsO2_*` | six shapes |
| P7 | 9/44 penultimate certificates kernel-blocked at 24 GB | **open** (resource) | `DKTCertsO2_big.keys` | needs 32–48 GB, or document the exclusion |
| P8 | Round-0 multi-commitment Johnson fallback | **done** (measured) | `nv_prep_o2_round0`, G2 chain | penultimate r3 on J64 |
| P9 | Certificate table bound into the vk; per-round regime enforced | **done** (measured) | `AgreementTable` | |
| P10 | No capacity-regime / random-words assumption anywhere | **done** (audit) | `PRIOR-ART.md` §10, NF-10 | statement, not proof |

**Paper consequence:** P4 is the only open *proximity* proof. Everything else is either Lean or a
cited theorem. The paper's "no proximity conjecture" claim is defensible once P4 is written
(it is a composition, not a new bound).

### 2.7 Final-layer size (the `< 300 KB` half)

| id | obligation | status | where | notes |
|---|---|---|---|---|
| Z1 | Size law: final size = f(W, L, opened columns, queries) | **hand + measured** | `pq-recursion-nv` README | matches within 0.2 % at the optimal shape (b=2 chain) |
| Z2 | `V_d` accepts at the measured shape | **done** (measured) | G2 gate | 293,077 B, pinned program |
| Z3 | Forgery control | **done** (measured) | G2 gate | |
| Z4 | **Size independent of aggregation tree** (S, k, d) | **sketch** | `DESIGN-BASE.md` §5.4 | must be proved: final verifies an inner fixed-point proof; no node shape enters its bytes |
| Z5 | The fixed point exists for every aggregation tree | **sketch** | `DESIGN-BASE.md` §5.3/5.4 | T1/T2 shapes independent of S |
| Z6 | Bound number with `bind = true` on the O-2 chain | **open** (measure) | 287,477 was `bind=false` | re-run; expect ≈293 KB |
| Z7 | NvAir 2^18 headroom under program growth | **open** (measure) | gap analysis | a paired run already exceeded 2^18 |
| Z8 | Final-layer verification time | **open** (measure) | — | no V_d wall-clock recorded in these lanes |

**Paper consequence:** Z4 and Z5 are the two theorems behind "the proof stays under 300 KB *no
matter how you aggregate*". They are short but must be stated; today they are sentences in a design
doc.

---

## 3. What is already proven and can be cited as-is

Lean-proved or kernel-checked in this repo:

- `holdsP_of_swirl` (SWIRL ⇒ `HoldsP`), `pq_d0a_rel`, `pq_d1_rel`.
- `nearAirV3` / `nearAirV3D1` bus bounds and `join_partition`.
- `wasm_base_sound` for const/add/drop, div/rem, memory, globals, calls.
- ContractData prefix/path/`cdWalkV3` facts; path-split lemma.
- DKT26 O-1 (Thm 5.12 + Cor 7.7/7.8) and O-2 certificates, 129/129 deployed, with the
  `johnsonE0` constant; the ArkLib checker re-verifies the stored integers exactly.
- `multBoundP < p` for D0a/D1.

Measured (not proofs, but evidence a paper can cite):

- G2 gate: 293,077 B, `V_d` accept, forgery reject, 46 min, 17 GB.
- Streamed commitments: byte-identical proofs; 853 GB virtual codeword at 14.9 GB peak.
- `T*`, WHIR-Y, program pinning, preprocessed children: differential + tamper tests.
- 55/55 x15 adversarial cases; 5,921/5,921 and 6,321/6,321 SHA AIR mutations.

---

## 4. The "no new conjecture" ledger (paper §assumptions)

Must be written as a table with exactly these rows; anything else is a red flag to a reviewer.

| assumption | used for | status |
|---|---|---|
| SHA-384 is a (quantum) random oracle | all hashing | standard idealisation |
| A-IC(τ) | in-circuit hash = oracle | **necessary** (A1); the one non-standard row |
| DKT26 (O-1/O-2) | proximity | Lean-proved; **paper unrefereed** — say so |
| BCGM / BCHKS25 | MCA/CA any `D` | external, refereed |
| WHIR Thm 5.2 (Puš26) | PCS rbr | external |
| NV-faithful / Base-faithful / Join-faithful | circuit + AIR refinement | engineering obligations (§2) |

Explicitly **absent** and must be stated as absent: proximity conjecture, capacity-regime MCA,
ethSTARK random-words, PoW hardness, sub-collision-resistant digests (42 B default), trusted
setup, groups/lattices.

---

## 5. Lean vs pen-and-paper: what to prove *here*

The user's rule is that a preprint we depend on should be proved here. Feasible split:

**(a) Minimum consistent with the rule — weeks**

1. `Theorem 7.4-tree` + `(F3-tree)` (N3) and node-count independence (N4), in Lean.
2. `c·2^K` domain lemma + exact sampler (P3) in Lean (small: four properties + a bijection).
3. `T*` counter-mode refinement (T5) and the grinding lemma (T2) in Lean.
4. The 9 blocked DKT certificates at ≥32 GB (P7).
5. `Size-independent-of-tree` (Z4) and fixed-point existence (Z5) as Lean statements.

**(b) Full version — months**

6. DKT26 → WHIR lift (P4) formalised in ArkLib (sets `n, ρ`; the hard part is Pul's corrected
   Thm 5.2 hypotheses).
7. Weak-binding Theorem 4 + Theorem R formalised.
8. `wasm_base_sound_host` (B2/B3) — genuinely hard because of the gas invariant.
9. `Join → RelD3` (J3) on top of B2/B3, J5–J8.

Items 1–5 are the paper-grade minimum for the *aggregation* theorem. Items 6–9 are needed for the
*chunk-validation* theorem and therefore for scope A.

---

## 6. Dependency order and what unblocks what

```
B3 (gas invariant) ──► B2 ──► J4 ──┐
J9 (HOST chip) ─────► J7, J8 ──────┼──► J3 (join compose) ──► H4
J5 (state half) ───────────────────┘
J10 (sig chip) ────────────────────┘  (only if transactions are signed)

N3, N4 (tree theorems) ────────────► H2 (arbitrary aggregation)
Z4, Z5 (tree-independent size) ────► <300 KB for arbitrary S

P4 (DKT26→WHIR) ───────────────────► H6 (proximity without conjecture)
P7 (9 certs) ──────────────────────► penultimate O-2 without J64 fallback
B4/B11 (seg-v1, splits) ───────────► H3 (base-faithful for any S)
```

Critical path for the paper: **B3 → B2 → J4 → J3** (chunk claim) and **N3 → N4** (arbitrary
aggregation). P4 is on a parallel path and is the only proximity item.

---

## 7. Measurement obligations (for the <300 KB claim)

| id | measurement | why it blocks the claim |
|---|---|---|
| M1 | Bound O-2 chain with `bind = true` | 287,477 B is unbound/provisional; the honest number may be ≈293 KB |
| M2 | Final-layer `V_d` wall-clock | "verifiable" needs a number |
| M3 | One real segment (seg-v1) base proof size and cells | the base is not the final layer; "proof under 300 KB" is the final, but the paper should state the base cost |
| M4 | Aggregation at, say, S = 8 and S = 64 (tree and G) | "arbitrary" needs at least two shapes measured, plus the theorem |
| M5 | NvAir height under the real app table | headroom is 3.6 %; growth can cost L 24 → 25 |
| M6 | 1 Pgas extrapolation honesty | state clearly it is modelled, not measured |

---

## 8. Risks to the paper's central claim

1. **"Arbitrary" may be too strong for cost.** Tree soundness scales, but *cost* does not: k-ary
   at levels ≥ 2 is quadratic with `BIND` (R3), so arbitrary arity needs a preprocessed program
   commitment that exists only for children, not for the parent program. The paper should quantify
   over **arbitrary S and depth** and over **`k = 2` / `N1` any `k`**, and say so.
2. **The tree theorem's union caveat.** If N3 is proved with the single-database theorem, fine.
   If a reviewer insists on a per-node union, every layer must gain ~8 bits, which costs bytes.
3. **Base-faithful is the weakest link.** Even with a perfect recursion layer, the paper's claim
   about a *chunk* rests on B4/B11, which are open for any real segment AIR set.
4. **A-IC may be judged as a conjecture.** It is not, given A1, but the paper must argue that
   carefully or a reviewer will treat it as `random-oracle-in-circuit` hand-waving.
5. **Scope A vs B.** Do not let "arbitrary aggregation" silently include 1 Pgas; the challenge
   excludes it and nothing above `G_α` has been run.

---

## 9. Paper section → obligation map

| planned paper section | obligations it must discharge |
|---|---|
| §3 domains (`c·2^K`) | P1, P2, P3 |
| §4 transcript (`T*`) | T1–T5 |
| §5 weak binding / WHIR-Y | (Thm 4, Thm R) — currently not in the draft's scope; include or cite |
| §6 agreement tables | P5–P9 |
| §7 recursion KS | N1, N2 |
| **§8 arbitrary aggregation** | **N3, N4, N5, Z4, Z5** |
| §9 systems | Z1–Z3, M1–M5 |
| §10 join / chunk relation | B1–B12, J1–J12 |
| §11 assumption ledger | §4 above, A1–A3 |
| §12 limitations | §8 above |

---

## 10. Immediate next actions (ordered)

1. **Write N3/N4** (`Theorem 7.4-tree`) as a Lean statement plus proof, in
   `lane/pq-final-soundness`. This is the paper's core new theorem and does not depend on the join.
2. **Write Z4/Z5** (tree-independent final size + fixed point existence); short, unblocks the
   "under 300 KB for any aggregation" phrasing.
3. **Fix the gas invariant (B3)**; it is the true blocker for the join, ahead of the HOST chip.
4. **Re-run the bound chain with `bind = true` (M1)**.
5. **Write P4** (DKT26 → WHIR) or explicitly mark it as the one cited composition in the paper.
6. Kernel-check the 9 blocked certificates at ≥32 GB, or record the J64 fallback as permanent.
