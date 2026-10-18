# D3a feasibility study: a formally admitted succinct proof for WASM chunks, toward 1 Pgas in ≤ 300 KB

Status: **study, 2026-10-14**, lane `lane/v3-d3a-study` (from main `584d55ff`). Commissioned by the user on
2026-10-14. The **north star** was revised the same day:

* validate chunks of up to **1 Pgas** (10¹⁵ gas, the mainnet chunk gas limit, ≈ 290 × today's
  `G_α` = 2²² · 822,756 ≈ 3.45 Tgas);
* with a **complete proof of ≤ 300 KB**;
* under `validity-classical-128`, transparent setup, random-oracle model;
* with the prover allowed to use **a few H200 machines**.

Nothing in this lane changes `nearAirV3`, the D0a certificate, any spec relation, any challenge, `oracle/v3`,
pinned files or prover code paths. Every relation, spec, challenge, security-profile or hardware change below is
a **PROPOSAL** that needs a user decision.

Labels used throughout:
* **measured** — run in this lane, on CPUs 8–9/24–25;
* **measured-repo** — measured earlier in this repo, with the source cited;
* **published** — vendor or paper claims, not reproduced here;
* **estimated** — arithmetic from a stated model;
* **ASSUMPTION** — an input that must be measured before it is relied on.

Inputs read:
* `docs/HANDOVER.md`, `STATUS-V3-D3.md`, `docs/requirements/D3_WASM_REQUIREMENTS.md` (v0.3: R5),
  `RECURSION_REQUIREMENTS.md`;
* `docs/zk-formal/V3-D0-DESIGN.md`, `V3-D1-DESIGN.md` (origin/lane/v3-d1a-spec, decisions P-D1-1…7);
* `docs/research/near-wasm-strategy.md`, `recursion-{summary,r1-cost,r2-theorem}.md`, `wasm-formal-survey.md`,
  `formal-ecosystem.md`, `checker-recommendations.md`;
* `spec/near-chunk-validation-d3.md`, `spec/lean/v3/NearSpecV3/{Wasm,D3,Logged}/*`;
* the challenge draft `challenges/drafts/near-chunk-v3.draft.json`;
* the zkVM dependencies under `/data/illia/nearproof-deps/` (§4.2);
* the untracked research note `docs/research/recursive-compression.md` in the main checkout. Another agent is
  working on it: it targets < 300 KB with hash-based recursion. I read it and did not modify it.

---

## D. User decisions (2026-10-14, binding) and what they change

| id | decision | consequence for this study |
|---|---|---|
| **U-1** | **Recursion ALLOWED, SHA-256 only.** The concrete SHA-256 evaluated inside circuits is treated as the random oracle. No Poseidon2 and no algebraic hash anywhere. | Option R-a is adopted as an assumption, to be named e.g. `sha256-random-oracle-in-circuit`. The challenge profile text still has to be drafted (PROPOSAL wording in §10.6). R-a' (Poseidon2) is **rejected**. Recursion nodes pay the full in-AIR SHA cost: 17 rows × W_eq 704 ≈ 12 k W-eq cells per compression (L5-SHA.md). R5 is superseded for D3-scale work. |
| **U-2** | **Proven soundness bounds only**, even if the proof ends up > 300 KB. No conjectured FRI regime. | 300 KB is now a *goal*, reachable only under a proven bound that can also be proved in Lean. The best proven size and its dependencies are in §10.4. |
| **U-3** | **Judge: parallel elaboration.** Measure judge wall time with parallel module elaboration on N cores under a 4 h wall limit. | PROPOSAL in §10.6: N = 16, plus the recheck implications. The S7 spike measures it. |
| **U-5** | **The long-term compressed-proof track (≤ 300 KB, 1 Pgas) targets 128-bit POST-QUANTUM security.** Today's classical challenges stay unchanged: D0a (signed), and `near-chunk-v3` with its D0a/D1a tiers under `validity-classical-128`. Phase 1 (the single-proof D3a tier on the classical stack) also stays. | §11 redoes the proof size, recursion and security analysis under PQ-128, and updates the latency envelope. **§11 supersedes §2.2, §10.2–§10.4 and U-1's SHA-256 choice for the PQ track** (U-1 re-check: §11.3). |
| **U-6** | **PQ security contract: failure ≤ 2⁻¹²⁸ against an adversary making ≤ 2⁶⁴ quantum hash queries** (not "128-bit quantum attack cost" with 2¹²⁸ queries). | The §11 size model's assumption stands. |
| **U-7** | **PQ track hash: SHA-384 throughout** (Merkle commitments, Fiat–Shamir, recursion circuits). Classical challenges keep SHA-256. | Amends U-1 for the PQ track (§11.3). D1's SHA-512 table should be a general SHA-384/512-family table. |
| **U-8** | **The real-time proof itself is post-quantum end to end** (no classical real-time layer with a later PQ wrap). | Real-time envelope = the PQ one (§11): about 12 Tgas worst-case pure WASM, 50–150 Tgas typical mix on 32 H200; every PQ proof obligation in §11 is on the real-time critical path. New prover/protocol code must be parameterised by hash, digest width and extension degree from the start. |
| **U-9** | **PQ proof-size target 0.5–1 MB under proven bounds; 300 KB is a stretch goal** (pursued via WHIR/STIR after the joint pinned-parameter milestone). | Joint milestone with `research/hash-recursion` decides whether to invest in WHIR/STIR proofs. |
| **U-10** | **PQ final-layer parameters (user decision 2026-10-17):** Merkle digests = SHA-384 truncated to **42 bytes (336 bits)**, domain-separated from full-width trees; **grinding z = 32 bits** per WHIR query phase (2-element PoW witness); **WHIR-Y** transcript order (each round's shift-query answers y_{i,·} are observed before sampling γ_i, including the final round). | Amends U-7 (truncation) for the PQ track. Proven basis: quantum collision bound t³/2³³⁶ ≤ 2⁻¹⁴⁴ at t = 2⁶⁴ (CMS19-style, ≈ 12 bits margin); grinding is Grover-tight (z bits per round). WHIR-Y costs 0 proof bytes and closes the block-equivocation attack of `lane/pq-weak-binding` HROB.md Prop. 2.1. Narrower (26–27 B) weak-binding digests remain a separate, undecided amendment. |
| **U-11** | **In-circuit random oracle for recursion, A-IC (user decision 2026-10-18):** for the recursive PQ track, SHA-384 evaluated inside the verifier circuit is treated as the random oracle (Assumption 7.3 of `lane/pq-final-soundness` PROOF.md). Under it, and with transcript fix T\* (counter-mode challenges; PoW on block B₁), the end-to-end bound is ≈ 2⁻¹³⁵ (2⁻¹³²·⁴ with a union over 7 layers) at ≤ 2⁶⁴ quantum queries. Funded: a research lane seeking a proven bound for our specific structure. | U-2 is **not met** on this one point for recursive proofs; recorded explicitly. No published result removes it for hash-only recursion; Barbara–Chiesa–Guan (TCC 2025) rule out the general relativized version in the ROM. Also amends U-10's grinding basis: the "Grover-tight" credit holds only with T\*-2. |
| **U-12** | **Time-bounded recursive claim (user decision 2026-10-18):** for recursive PQ proofs, U-6 reads: soundness error ≤ 2⁻¹²⁸ against adversaries making ≤ 2⁶⁴ quantum SHA-384 queries **and running in time ≤ τ = 2¹²⁸ operations**, under A-IC(τ) (U-11 restated with the time bound). The final recursive layer uses its own hash domain prefix, distinct from inner layers (0 bytes). | Forced by Thm O of `lane/pq-aic-research` LEMMA.md: in any oracle model that bounds only queries, depth ≥ 1 hash-only recursion is insecure (an unbounded-time adversary hard-codes a false proof accepted by the in-circuit-SHA-384 verifier and wraps it honestly). A-IC research closed as resolved-negative. Non-recursive proofs keep the query-only U-6. |
| **U-4** | **Near-real-time is required**, not minutes-async. NEAR blocks are ≈ 1 s. Hardware budget: "up to a few H200 machines" (2–4 × 8 H200). | §3.3's minutes-scale plan is **superseded by §10**. Verdict: worst-case 1 Pgas in ≈ 1–2 s is **not feasible** on 16–32 H200. §10.3 gives the achievable envelope and the hardware the worst case would need. |

Where §§0–8 conflict with this section or §10, **D and §10 govern**:
* §0 items 2, 4 and 6;
* §3.3 latency;
* §4.1's 1 Pgas column;
* §7 phases and spikes;
* §8 decisions 1–4 and 8.

The workload measurement (§1), the zkVM verdict (§4.2), reuse (§5) and exclusions (§6) are unchanged.

---

## 0. Answers in one page (original study; see D and §10 for updates)

1. **Workload (measured, §1).** On all 19,179 accepted D3 cases (172 public `near-chunk-v3` D3 fixtures plus the
   19,007 honest cases of corpora d3c7–d3c10):
   * at most **2.04 M WASM instructions** per chunk (49 % of the 4.19 M operators `G_α` allows), median 354, p99 0.81 M;
   * ≤ 94 host calls, ≤ 12 function calls, ≤ 1,280 memory pages (all contracts start at 1,024 pages = 64 MiB);
   * code ≤ 5.6 KB per contract;
   * **only 3.4–4.6 % of function-call gas is WASM-operator gas**; the rest is host and action fees
     (`storage_write`, `promise_*`, account creation).

   The corpora contain only synthetic contracts, so the instruction mix is not mainnet's: loads and stores are
   0.5 % of instructions here, while mainnet Rust contracts typically run 15–30 % (**ASSUMPTION**). Our own
   `G_α` dimensioning, which assumes pure WASM, is the worst case and is about 25× above anything in the corpora.

2. **1 Pgas (§3).** The adversarial worst case is pure WASM: 10¹⁵ / 822,756 ≈ **1.22·10⁹ WASM operators per
   chunk**. At the measured synthetic mix it is ≈ 3.7–5.2·10⁷ instructions per Pgas.
   * A custom WASM AIR costs ≈ 494–995 committed W-eq cells per operator (`recursion-r1-cost.md` presets,
     **ASSUMPTION** until spike S2). That is **0.6–1.2·10¹² cells per 1 Pgas chunk**.
   * At D0a's measured throughput (≈ 75 s per 10⁹ W-eq cells on 8 vCPU) this is **12–25 h on the draft's 8-vCPU
     profile and 2–7 TB of prover memory**. 1 Pgas is impossible on the current hardware profile with any
     architecture.
   * On **2–4 machines × 8 H200**, with segment proving, an aggregation tree and a GPU port of our STARK prover:
     **≈ 1–5 min for a worst-case 1 Pgas chunk, and ≈ 15–60 s for a typical chunk** (estimated; §3.3).

3. **300 KB (§2).** Today's D0a proof is 5.3–5.7 MB of STARK plus up to 1.3 MB of hints. That is ≈ 20× over.
   * **No single-layer STARK in the arena's proven regime reaches 300 KB.** The arena's ROM accounting charges
     2⁶⁴ hash queries, so the query phase must give ≈ 192 bits. In the unique-decoding regime (UDR), which is
     the only one proved in Lean today, that means ≥ 160 queries and ≈ 0.7–0.9 MB even for a tiny final trace.
   * Reaching ≤ 300 KB needs **all three** of:
     1. **recursion/compression** (or a polylogarithmic multilinear IOP), to make the last proof small and
        constant-size;
     2. **the Johnson (list-decoding) regime proved in Lean without Mathlib**, which gives ≈ 2–4 bits per query at
        blowup 2⁴–2⁸, plus 30–32 bits of grinding. With these, the estimated final layer is ≈ 230–350 KB on FRI and
        lower with STIR/WHIR-style rate decay;
     3. **every hint moved into the proof**. Hints are witness-derived (refund body, scheduler state, queue
        values, and D1's transactions); claim-only checks can stay native.

   The conjectured capacity regime would give ≈ 125–240 KB. It is not admissible, because `CryptoSound` needs a
   proven bound.
4. **Recursion is the formal crux (§2.3).** An outer AIR that verifies an inner proof must evaluate the
   *concrete* hash. The arena's `CryptoSound` ROM branch cannot express that, so recursion is not provable under
   today's profile (V3-D0-DESIGN §5.5, confirmed here). Two admissible ways out:
   * **(R-a) PROPOSAL:** a new allowed assumption that instantiates the inner protocol's ROM bound with the
     concrete hash (the standard heuristic), with the arithmetisation step *proved* in Lean against
     `npVerifierP`.
   * **(R-b)** a **single-shot polylogarithmic IOP** (sumcheck/GKR + WHIR-style hash PCS) that stays inside the
     ROM. It is formally cleanest, but it is a new protocol layer in Lean and needs a monolithic distributed prover.

   Both also revisit the user's **R5 decision**, which is a user decision.
5. **zkVMs (option B, §4.2) are not admissible and cannot become admissible on any useful timescale.**
   * No artifact proves "accepting proof ⇒ RISC-V execution" through the IOP/FS layer.
   * All use Poseidon2 or BLAKE3 Fiat–Shamir at 96–100 bits.
   * All Lean artifacts need Mathlib.
   * There is no verified WASM→RISC-V compiler or verified interpreter.
   * Measured in this repo: wasmi in SP1 runs at ≈ 29 cycles per WASM instruction.

   They remain useful as a cost baseline and as GPU-prover references.
6. **Recommendation (§7).** Build **A: a NEAR-WASM machine AIR** whose Lean soundness is
   **protocol-independent** (`Holds ⇒ Rel`).
   * First prove it in the current stack at `G_α` (a D3a tier proof).
   * Then reuse the same tables as the *segment AIR* of the north-star architecture **A+R**: segments with
     continuations, an aggregation tree, and a recursive compression to ≤ 300 KB, on a GPU prover.
   * In parallel, run the formal spikes that decide (R-a) vs (R-b): the Johnson-regime proof in Lean, and the
     size calculator.
   * **D1/D2 should change now** (§5): no new witness-derived hints. **P-D1-2 (native Ed25519 on hinted
     transactions) is incompatible with 300 KB and should be marked interim**; plan D1-S faithful.

---

## 1. Workload: what D3a chunks execute (measured)

**Method.** The independent Python D3 checker (`oracle/tools/spec_check_v3_d3.py` with the clean-room VM
`oracle/wasm-d3/cleanroom/nearwasm.py`) runs unchanged on every case. A wrapper,
`tools/d3a-study/instr.py`, loads an in-memory copy of `nearwasm.py` with two added lines (a per-instruction
counter, plus a map from flat-IR index to the original opcode) and wraps `host_dispatch`, `mem_read/write` and
`run_vm`. No repo code is modified.
* Every case reproduces the checker's verdict (`accept`): 19,179 out of 19,179.
* Raw JSONL (4 × 2.6 MB plus public) is in `/data/illia/nearproof-deps/validation/v3-d3a-study-20261014/`.
* Hashes are in `docs/e2e-results/v3-d3a-study/raw-sha256.txt`, and the aggregates in the two `workload-*.txt`
  files there.
* Run time: ≈ 15 min on 4 cores.

Per accepted chunk:

| quantity | public D3 (172) p50 / p99 / max | corpora d3c7–10 (19,007) p50 / p99 / max |
|---|---|---|
| WASM instructions executed (flat IR, excluding block/loop/end) | 1,081 / 1.32 M / **1.38 M** | 354 / 0.81 M / **2.04 M** |
| finite-wasm charge points executed | 295 / 0.19 M / 0.20 M | 102 / 0.12 M / 0.29 M |
| host calls | 14 / 58 / 60 | 8 / 49 / **94** |
| function calls (VM runs) | 2 / 6 / 6 | 1 / 6 / **12** |
| linear-memory size (pages of 64 KiB) | 1,024 / 1,279 / 1,279 | 1,024 / 1,279 / 1,280 |
| largest contract executed (bytes) | 5,603 | 5,603 (sizes seen: 34 B – 5.6 KB) |
| function-call gas burnt (Σ `burnt`) | 0.39 / 3.39 / **3.44 Tgas** | 0.23 / 3.25 / **3.45 Tgas** (= `G_α`) |
| of which WASM-operator gas | 1.1 G / 1.16 T / 1.21 T | 0.38 G / 0.71 T / 1.80 T |
| host↔memory bytes | 141 / 6.4 K / 6.5 K | 60 / 5.4 K / 14.4 K |
| promises / receipts (meta, public) | 2 / 9 / 13 promises; 6 / 588 / 590 receipts | — |

Distribution against the cap (corpora plus public, by FC gas): 10,549 cases are below 0.1 `G_α`. 345 are in
0.9–1.0 `G_α`, and the largest of those executes 2.04 M instructions. **No in-domain case gets close to the
4.19 M-operator worst case.** Gas is dominated by host fees:
* aggregate WASM-operator share of FC gas: **3.4 %** (corpora) and 4.6 % (public);
* aggregate instruction density: **37–52 k instructions per Tgas**, against **1,215 k/Tgas** for pure WASM.

**Instruction mix** (corpora; shares of executed flat IR including charge pseudo-ops):

| family | share | family | share |
|---|---|---|---|
| local get/set/tee | 30.7 % | compare/eqz | 6.3 % |
| const | 18.0 % | mul | 5.5 % |
| gas charge points | 13.3 % | convert/extend | 0.8 % |
| control (br/br_if/if/return) | 12.4 % | **store / load** | **0.41 % / 0.05 %** |
| add/sub | 12.0 % | global, call/call_indirect | 0.34 %, 0.23 % |
| shift/bitwise/div/clz | < 0.05 % each | bulk memory/table | ≈ 0 |

**Host-call mix** (corpora, 219,427 calls, 56 distinct functions). By count: `register_len`, `read_register`,
`storage_write`, `input`, `promise_create`, `log_utf8`, `promise_batch_create`. By gas:
* `promise_create` 2.89 Pgas;
* `storage_write` 2.87 Pgas;
* `promise_then` 1.39 Pgas;
* `promise_batch_action_create_account` 1.22 Pgas;
* `promise_batch_create` 0.68 Pgas;
* `promise_batch_action_transfer` 0.58 Pgas.

These total 12.3 of the 12.85 Pgas burnt across all cases.

**Caveats (important).**
1. The contracts are synthetic (`ttn2`, `d3rich`, `d3hostx`, `d3tiny`, `d2program`, `d3ed`). Mainnet contracts are
   0.1–1.5 MB (limit 4 MiB), use memory heavily (near-sdk serde, allocators), and call far fewer promise fees per
   instruction.
2. **The real mainnet mix is unmeasured.** HANDOVER §8 already lists a mainnet replay. Spike S1 makes it a
   prerequisite: it must measure the operator-gas share, distinct contracts and code bytes per chunk, memory-op
   share, and touched memory.
3. Proving cost must be dimensioned for the **adversarial** chunk, which is pure WASM. The measured mix sets
   *typical* latency, not the bound.

**Raising `G_α` to 1 Pgas (× 290).** Per chunk:

| scenario | WASM operators | contracts / code | host work |
|---|---|---|---|
| D3a today (`G_α`), worst | 4.19 M | ≤ 5.6 KB in corpora; up to 4 MiB allowed | small |
| 10 × `G_α` (34.5 Tgas) | 41.9 M | | |
| 100 × `G_α` (345 Tgas) | 419 M | | |
| **1 Pgas, worst (pure WASM)** | **1.22·10⁹** | | |
| 1 Pgas at the measured synthetic mix | 3.7–5.2·10⁷ | | ≈ 10 k `storage_write`, ≈ 3 k promises ⇒ ≈ 10⁶ SHA blocks of trie work (est.) |
| 1 Pgas of `sha256`/`keccak256` host calls | small | | ≈ 40–46 MB hashed (≈ 0.6–0.7 M SHA blocks or 0.34 M keccak-f): **fewer cells than pure WASM** |

Pure WASM operators have the highest **cells per gas** of anything in D3α: ≈ 6·10⁻⁴ cells/gas, against ≈ 10⁻⁵ for
hashing host calls. Pure WASM is therefore the design point for capacity. A second capacity problem appears at
mainnet scale: **contract preparation**. Each distinct contract executed in a chunk must be hash-bound (SHA over
its code) and decoded and validated in-AIR (PREP: ≥ 1 row per code byte). A chunk touching 20 distinct 400 KB
contracts carries 8 MB of code, i.e. ≈ 125 k SHA blocks plus ≥ 8 M PREP rows. Code also does not travel in
nearcore's state witness (it is distributed separately), so the claim/witness format question in §6 must be
answered.

---

## 2. Proof size: from 5.3–6.2 MB to ≤ 300 KB

### 2.1 Where D0a's bytes go, and the arena's query accounting

* D0a proof: **5.26–5.67 MB** STARK, formal bound `v3MaxInner` 6.44 MB at g = 2. Parameters: rate 1/16, LDE ≤ 2²⁶,
  216 queries, arity-8 FRI, SHA-256 Merkle, BabyBear with an Fp8 extension.
* Hints: honest ≤ 1.30 MB; the formal maximum is 1.95 MB (`v3MaxHintBytes`).
* Size is ≈ `216 × (4·W_eq + paths)` with `W_eq ≈ 2,600–3,000`, so the **opened rows dominate**.
* **Why 216 queries.** The kernel-checked bound (`ZkFormal.Params.udr2_ok`, DESIGN.md:305) charges the query phase
  `(2⁶⁴ + 2⁴⁰·k + k) · ((n−e)/n)^216 ≤ 2⁻¹³²`. Under the profile's `max_hash_queries_log2 = 64`, a
  128-bit target needs ≈ **192 bits per Fiat–Shamir attempt**. That count, not the 128 itself, sets the number of
  queries.
* **Grinding** (proof of work before query sampling) is a ROM-sound lever this stack does not use yet.
  * z bits of grinding cost the honest prover 2^z hashes and cut the required query bits to `192 − z`. At z = 32
    that is ≈ 4·10⁹ SHA-256 compressions, about 1 s on a GPU.
  * PROPOSAL-free: it is a protocol change inside the existing ROM game, but it needs an L2/L3 lemma.

### 2.2 Proven vs conjectured FRI regimes at 128 bits (estimated)

Model: a final ("outer") layer AIR with W_eq ≈ 300, three Merkle trees, 32-byte digests, arity-8 FRI down to
degree 2⁶, z = 32 bits of grinding, shared top Merkle levels, and OOD values and roots included. Per-query bits:
* UDR: `−log₂((1+ρ)/2)`;
* Johnson: ≈ `½·log₂(1/ρ)`;
* capacity (conjectured): `log₂(1/ρ)`.

The script is reproducible from this table; its formula is in §9.

| blowup | regime | queries | outer trace 2¹⁶ | 2¹⁸ | 2²⁰ |
|---|---|---:|---:|---:|---:|
| 16 | UDR (**proved in Lean today**) | 176 | 690 KB | 817 KB | 896 KB |
| 16 | Johnson (proven in the literature, **not** in Lean) | 85 | 362 KB | 426 KB | 464 KB |
| 64 | UDR | 164 | 711 KB | 840 KB | 914 KB |
| 64 | **Johnson** | 56 | **274 KB** | **321 KB** | 346 KB |
| 256 | **Johnson** | 42 | **230 KB** | **269 KB** | (LDE > 2²⁷) |
| 64 | capacity (**conjectured; inadmissible**) | 27 | 149 KB | 172 KB | 184 KB |
| 256 | capacity | 20 | 125 KB | 144 KB | — |

Notes:
* The 2-adicity of BabyBear is 27, so LDE ≤ 2²⁷. That forces a small final trace (≤ 2¹⁸–2¹⁹) at high blowup,
  which means **a multi-step compression chain**: segments → aggregation at a low blowup → one or two wrap layers
  of shrinking trace → the final layer at blowup 2⁶–2⁸.
* **STIR/WHIR-style rate-decaying low-degree tests** reduce queries further per round. Published WHIR figures (63 KiB at
  100 bits, conjectured) suggest a ≈ 120–200 KB final layer in the proven Johnson regime at our 192-bit query
  target (estimated, uncertain ±50 %). Their proven soundness is again a Johnson-regime proximity-gap statement.
* **The formal bottleneck for 300 KB is a Mathlib-free Lean proof of Johnson-regime proximity gaps**
  (BCIKS20-style correlated agreement up to `1 − √ρ`). ArkLib has only the unique-decoding regime proved, its
  FRI/FS relations are still `sorry`, and it depends on Mathlib (§4.2). V3-D0-DESIGN P6 already flagged this as
  "research". It is spike S4 and go/no-go G1.
* Digests stay 32 bytes. With 2⁶⁴ hash queries, Merkle binding needs ≥ 256-bit outputs (birthday bound), so
  shorter digests are not a lever.

### 2.3 Recursion and its formal admission

**The obstruction.**
* `CryptoSound`'s ROM branch (`formal-core/ArenaCore/Admission.lean`) runs the deployed verifier against a *random*
  oracle.
* An outer AIR can only arithmetise the *concrete* hash.
* So the outer statement "∃ inner proof accepted by `V^{SHA-256}`" implies `Rel` only under an assumption about
  the concrete hash that the ROM game does not provide (V3-D0-DESIGN §5.5; `recursive-compression.md` reaches the
  same conclusion).
* R2 (native accumulation, `recursion-r2-theorem.md`) is ROM-provable but **does not shrink the proof**, because
  every segment is still opened natively.

The **deterministic half is provable**: `HoldsP outerAIR pub tr → ∃ π, npVerifierP innerAIR pub π = true`, where
`npVerifierP` is the existing executable Lean verifier model with the hash read from SHA rows. That is a refinement
proof of the same kind as L5 (SHA table ⇒ SHA spec) and L6 (tables ⇒ trie spec). Its pieces:

| piece | content | reuse | Lean est. (lines) |
|---|---|---|---|
| hash rows | SHA-256 compression | **L5 as is** (proved) | 0–5 k (wiring) |
| Merkle/MMCS openings | path recomputation vs root | L6 `mrk` pattern | 8–15 k |
| transcript | FS absorption order equal to `npVerifierP`'s | L2 definitions | 10–20 k |
| field/extension arithmetic | Fp8 mul/inv rows | new | 8–15 k |
| FRI fold/roll-in checks, final polynomial | per query, per layer | L3 statements | 15–30 k |
| ALI/OOD: evaluate the inner AIR's constraint DAG at the OOD point | **a universal "expression-eval" table driven by a committed DAG of the inner AIR** (generic over AIRs; proved once against `Expr.eval`) | L4 `Expr` | 20–40 k |
| bus/grand-product finals, public segments | | L3/L4 `HoldsP` | 5–10 k |
| composition, heights, completeness | | pattern of `ExtractV3`/`CompleteV3` | 15–30 k |
| **total** | | | **≈ 80–165 k lines** (the D0 design's 30–50 k × the measured 2–3× over-run) |

**Cryptographic half: options.**
* **(R-a) PROPOSAL: an allowed assumption `fs-instantiation-sha256` (or `…-poseidon2`).** Its statement: "for the
  pinned verifier V (np-udr-stark-v2 parameters), the Lean-proved ROM bound holds when the oracle is the concrete
  hash, against adversaries within the profile's query and size budgets." Combined with the proved arithmetisation,
  this gives outer soundness. The assumption is the standard random-oracle-instantiation heuristic that every
  deployed recursive STARK relies on. It is **stronger than** today's `random-oracle-fiat-shamir-sha256`, because
  that one is used only black-box.
* **(R-a') Poseidon2 inside the recursion layers (REJECTED by U-1).** In-circuit SHA-256 costs ≈ 17 rows × 544 columns per block,
  and verifying a D0a-sized proof costs ≈ 236 k blocks ≈ 2 G cells per recursion node. Poseidon2 over BabyBear
  would be ≈ 20–50× cheaper per node, but it needs a further allowed assumption (Poseidon2 as a random oracle /
  collision resistance). PROPOSAL; optional.
* **(R-b) Single-shot polylogarithmic IOP, no recursion.** A sumcheck/zerocheck over the AIR, GKR-LogUp for the
  buses, and a WHIR/STIR-style hash PCS over the stacked trace.
  * It stays entirely in the ROM game: the *existing* assumption list suffices.
  * Its proof is polylogarithmic, and the Johnson-regime estimate is ≈ 150–300 KB at 10¹² cells.
  * Costs: a **new protocol layer in Lean** (sumcheck RBR soundness, GKR, a multilinear PCS, the BCS/FS transfer),
    ≈ 60–120 k lines Mathlib-free. Some of it can be ported, not imported, from ArkLib's proved sumcheck.
  * It needs a **monolithic distributed prover**: one commitment over ≈ 10¹² cells, 2–8 TB at rate 1/2–1/4.
    That exceeds the 4.5 TB of HBM on 32 H200s, so it must stream from host RAM.
  * This is research-grade, but it is the only path to 300 KB that needs no new trust assumption.
* **(R-c) The `max_aggregation_depth = 8` in the current profile** suggests aggregation was anticipated, but no
  admission branch implements it. Any recursion adds the aggregation statement:
  * segment boundary states are chained on a global bus (`Wasm/Segment.lean` already proves
    `run (Σks + n) s = foldSegments ks s >>= run n`);
  * an arity-4 tree over ≈ 290 segments has depth 5, which is ≤ 8.

**Elaboration budget.** A recursive certificate contains, at minimum: the segment AIR's soundness (NEAR plumbing ≈
D0a's 3,964 modules plus WASM), the recursion AIR's proof, and the assembly. Projected: D0a ≈ 7,000 s; D1a
10,000–12,500 s (V3-D1-DESIGN §6.3); WASM AIR +7,000–15,000 s; recursion +3,000–6,000 s. That totals
**≈ 17,000–34,000 s serial, against 14,400 s**, so the certificate does **not fit the 4 h judge budget**. PROPOSAL:
raise the elaboration budget (8–12 h) or allow judge-side parallel elaboration with a CPU-seconds budget. The
elaboration-budget lane's D0a cuts (`codec_int`, est. −1,500–2,500 s) help but do not close the gap.

### 2.4 Hints must move inside the proof

The verifier keeps claim-only (class **C**) checks native at no proof-size cost: the claim is a verifier input,
not proof bytes. These are the header chain, `chunk_headers_root`, the ChaCha *shuffle* of source lists (seeded
from the claim), binary64 congestion, and RS parameters. **Witness-derived hints (class H) must become committed
witness plus in-AIR checks**:

| D0a/D1 hint | size (worst) | native check today | in-AIR replacement | cost (est.) |
|---|---|---|---|---|
| refund/outgoing body `B` | ≤ 0.91 MB | RS encode + `encoded_merkle_root`, outgoing root, `tryForward` | RS over GF(2⁸): ≈ 67·|B| ≈ 61 M multiply-adds by lookup, plus SHA Merkle | ≈ 61 M rows ≈ 3–6 G cells at the worst body (≈ 1 % of a 1 Pgas chunk; already sized by V3-D0-DESIGN §2.5) |
| scheduler state `s₀` (`0x0f`) | ≤ 98 KB | `Scheduler.run` (BTreeMap buckets, ChaCha, stable sorts) | a scheduler AIR | 20–40 k Lean lines (D0 design est. ×1.5); rows small |
| queue values | ≤ 128 KiB | queue decode | decoders in-AIR | small |
| `n`, okbits | bytes | | already AIR-bound | — |
| **D1 (P-D1-2): `txs`, `newTxs`** | ≤ 1.21 + 1.21 MB | `Ed25519.verify`, `pTxD1`, dedup, `merklize` vs claim `tx_root` | tx bytes as witness; SHA-Merkle vs the public `tx_root`; **in-AIR Ed25519 (D1-S faithful: ≈ 7.5 k field muls per signature)** | ≈ 3.6 M W-eq cells per signature ⇒ 4,096 tx ≈ 15 G cells; Lean +40–70 k lines |

**Verdict on P-D1-2.** Native Ed25519 over hinted transactions puts up to ≈ 2.4 MB of hint into every
maximum-size proof, which is incompatible with 300 KB.
* Recommendation: keep D1-N as the **interim D1a candidate** (it is decided, cheap, and reuses D0a).
* **Mark P-D1-2 as interim** and adopt **D1-S faithful** as the north-star D1 design. Ed25519 then becomes a shared
  chip that D3γ (`ed25519_verify`) reuses.
* Design the D1-N tables now so that only the source of the `valid` bit changes later (§5).
* This is a user decision (it revises P-D1-2's scope, not D1a's relation).

---

## 3. Cost model at `G_α`, 10×, 100× and 1 Pgas

### 3.1 Calibration

* **D0a measured-repo** (`docs/logs/v3-prover-perf-2026-10.md`): 263–312 s and ≤ 12.6 GiB for ≈ 3.5–4 G W-eq cells
  at 2²², on 8 vCPU of a Ryzen 9 9950X3D (AVX2). That is **≈ 75 s per 10⁹ W-eq cells** (±30 %), or ≈ 13 M cells/s.
* **WASM AIR cells per operator (ASSUMPTION).**
  * d3-lean: 494 (EXEC 150 columns plus three sorted-RAM tables);
  * d3-rich: 872;
  * NEAR-density: 995 (`recursion-r1-cost.md` §4.1).

  The measured mix (31 % locals, 18 % const, 12 % control) is the shape d3-lean assumes. Mainnet's heavier
  load/store share pushes towards d3-rich. Spike S2 replaces these presets with a measured value.
* **zkVM measured-repo** (`docs/research/checker-recommendations.md` §5): wasmi in SP1 runs at ≈ 29 RISC-V cycles
  per WASM instruction (RISC Zero ≈ 25). The SP1 6.8.1 CPU core prover reaches ≈ 226 k cycles/s on 32 threads with
  99 GB. The arena judge measured the SP1 compressed floor at ≈ 75 s with ≥ 18 GiB.

### 3.2 On the draft's CPU profile (8 vCPU, 16 GiB, 600 s): estimated

| WASM gas | operators | **A** (custom AIR) cells | A prove (8 vCPU) | A RAM (non-streaming) | **B** (wasmi-in-zkVM) cycles | B prove (SP1 CPU) |
|---|---|---|---|---|---|---|
| `G_α` 3.45 Tgas | 4.19 M | 2.1–4.2 G (+ D0a plumbing 3.5–4 G) | **420–630 s** in total: at or over 600 s | ≈ 20–25 GiB: **over 16 GiB** | ≈ 120 M (+ plumbing) | ≥ 530 s at 99 GB: over |
| 10 × (34.5 Tgas) | 41.9 M | 21–42 G | 0.5–0.9 h | 75–150 GiB | 1.2 G | ≈ 1.5 h |
| 100 × (345 Tgas) | 419 M | 207–417 G | 4.3–8.7 h | 0.75–1.5 TB | 12 G | ≈ 15 h |
| **1 Pgas** | **1.22 G** | **0.6–1.2 T** | **12.5–25 h** | 2–4 TB | 35 G | ≈ 43 h |

* Even D3a at `G_α` with pure-WASM chunks does **not fit** today's caps without prover work:
  * honest heights instead of fixed 2²² padding (also needed by D1-S);
  * a streaming (two-pass) memory schedule;
  * or a `G_α` of ≈ 2–2.5 Tgas.
* The measured corpora sit at ≤ 2.04 M operators. In practice they would fit at ≈ 2²¹ EXEC rows.

### 3.3 On 2–4 × 8-H200 machines (PROPOSAL hardware; estimated)

**Assumed machine:** 8 × H200 SXM (141 GB HBM3e each, 1.13 TB per node), NVLink/NVSwitch inside the node, 2 × 64–96-core
x86 hosts, 2 TB DDR5, and 4 × 400 Gb/s InfiniBand/RoCE between nodes.

**Planning throughput for our STARK on one H200: 0.5–2·10⁹ W-eq cells/s (ASSUMPTION).**
* That is ≈ 40–150 × our 8-vCPU host.
* It is consistent with published GPU STARK provers: SP1 Hypercube's real-time Ethereum proving on 16 GPUs, ZKsync
  Airbender's ≈ 20 M RISC-V cycles/s on one H100, RISC Zero and OpenVM CUDA backends, and ZisK. These are
  **published** figures, not reproduced here.
* SHA-256 Merkle hashing on GPU runs at tens of GB/s and is not the bottleneck.

**Architecture: A+R.**
* The chunk is executed once natively, recording segment boundary snapshots: ≈ 1.2·10⁹ operators in a
  trace-recording interpreter, ≈ 10–30 s serial; this can be pipelined.
* Trace generation then runs per segment on host cores.
* Segments are proved in parallel on GPUs at low blowup (rate 1/2–1/4). Inner proofs may be large; only the root
  is transmitted.
* An arity-4 aggregation tree follows, then 1–2 shrinking wrap layers and the final layer at blowup 2⁶–2⁸
  (Johnson) for ≤ 300 KB.

**Memory per segment vs HBM.**
* A 2²² × 494 segment is 8.3 GB of trace, 17–33 GB of LDE at blowup 2–4, plus Merkle and quotient: **2–4 segments
  per H200**.
* Taller 2²⁴ segments at blowup 2 need ≈ 66 GB and fit.
* Host RAM (2 TB per node) holds the traces of ≈ 100 segments.

**Latency (estimated):**

| chunk | cells (A) | segments (2²² ops) | 16 × H200 | 32 × H200 |
|---|---|---|---|---|
| typical (measured synthetic mix, ≤ 300 Tgas, plus plumbing) | 30–80 G | 5–15 | 20–60 s | 15–40 s |
| 100 × `G_α` worst | 0.21–0.42 T | 100 | 1–2 min | 0.6–1.2 min |
| **1 Pgas worst** | **0.6–1.2 T** | **290** | **2–5 min** | **1–3 min** |

Each figure includes the base proving `cells / (n_GPU · 0.5–2 G/s)`, recursion overhead of +30–100 % (SHA-based
nodes; ≈ 2 G cells per node), the final wrap of 10–30 s, and witness generation.

**Target I would consider realistic:** ≤ 5 min for an adversarial 1 Pgas chunk and ≤ 30–60 s for a typical chunk,
on 4 × 8 H200, with a stretch of ≤ 1 min worst case using Poseidon2 inner layers (R-a') and 2²⁴ segments. **This
is not real-time.** NEAR's block time is ≈ 0.6–1 s, so a proof trails validation by minutes. That suits the
cross-shard "one proof for all shards" use (HANDOVER §0), not a synchronous drop-in for
`validate_chunk_state_witness`. The user should be told this plainly.

**Porting our prover to GPU.** The prover is outside the TCB: only the verifier model is formal. So **a GPU port
has no Lean cost**. The work is:
* NTT/LDE over BabyBear (ICICLE or the Plonky3/SP1 CUDA kernels as references);
* SHA-256 Merkle trees;
* quotient evaluation (constraints generated to CUDA from the Lean-exported layout, `np-lean-export-v3 --layout`);
* DEEP/FRI and grand products;
* multi-GPU segment scheduling.

Estimate: 10–20 k lines of CUDA/Rust, **8–16 lane-weeks**, with conformance kept by the existing `run-v2.sh`
(proofs byte-identical to the CPU prover).

**zkVM CUDA backends (published).** SP1 (CUDA prover; Hypercube cluster), RISC Zero (CUDA/Metal), OpenVM (CUDA in
2.x), ZisK and Airbender are GPU-native. Jolt has GPU work in progress. Upstream Plonky3 is CPU-only. These help as
references and kernels; §4.2 explains why they cannot be the admitted path.

**PROPOSAL (judge/challenge): hardware profile for the north-star tier.**
* `hardware_profile`: `gpu = 8 × H200 141 GB` per node, `nodes ≤ 4`, host 2 TB.
* `max_vram_bytes` ≈ 1.1 TB per node.
* `max_prove_ms` 300,000 (1 Pgas class) / 60,000 (typical class).
* `max_proof_bytes` 307,200.
* `max_verify_ms` on CPU ≤ 1,000.

The live judge needs a GPU worker class: currently `max_vram_bytes = 0`, 8 vCPU, 16 GiB (draft 32 GiB RAM), no GPU.
Cost-board pricing (`pm-near-mainnet-2026q4`) needs a GPU-hour price. The current D0a/D1a/D3a tiers keep the CPU
profile.

---

## 4. Architecture options

### 4.1 Comparison (both constraints: 1 Pgas and ≤ 300 KB)

| option | rows/cells per WASM op | at `G_α` (CPU) | at 1 Pgas (32 × H200) | proof size path | admission path | Lean effort (est.) | engineering (≤ 4 lanes) | main risk |
|---|---|---|---|---|---|---|---|---|
| **A** custom NEAR-WASM machine AIR in the current stack (single proof) | 1 EXEC + 2–3 RAM rows, ≈ 494–995 cells | 420–630 s, 20–25 GiB (needs prover work) | n/a (single proof ≤ `G_α`) | 5.5–7 MB | existing `AdmissionStatement`, ROM, unchanged protocol | **150–300 k lines, ≈ 1,500–3,500 modules** (strategy doc 60–120 k × 2–3) | 4–8 months | volume (89 host functions, gas points), elaboration budget |
| **A+R** (recommended north star) A's tables as the segment AIR + continuations + aggregation + recursive compression + GPU prover | same | same as A | **1–3 min** (worst) | **≈ 230–350 KB FRI-Johnson; ≈ 120–200 KB STIR/WHIR-Johnson** | **needs PROPOSAL R-a** (+ optional R-a'), proved arithmetisation vs `npVerifierP`, Johnson regime in Lean, bigger judge budget | A + 80–165 k (recursion AIR) + 20–40 k (Johnson regime) + 10–20 k (grinding, aggregation) | A + 6–10 months (parallel tracks) | Johnson-regime proof without Mathlib; assumption approval; judge budget |
| **B** existing zkVM running a RISC-V-compiled NEAR runtime/interpreter | ≈ 25–29 RISC-V cycles (measured-repo) × zkVM cells per cycle | ≥ 530 s, ≥ 99 GB (SP1 CPU) | ≈ 1–4 min on GPUs (published rates) | SP1 compressed 1.27 MB; ≈ 220 KB succinct RISC Zero (96 bits conjectured); smaller only with Groth16/PLONK (trusted setup: **forbidden**) | **none**: no IOP/FS proof, non-SHA FS, 96–100 bits, Mathlib, no verified compiler or interpreter (§4.2) | would need a RISC-V ISA spec + whole-zkVM soundness + protocol soundness + a compiled interpreter proof: **≫ 500 k lines, years** | 1–2 months for an *unadmitted* prototype | inadmissible |
| **C1** hybrid: nearAirV3 plumbing + WASM sub-AIR on shared buses | = A (it is A's structure) | = A | with R: = A+R | = A / A+R | = A / A+R | = A | = A | = A |
| **C2** hybrid: nearAirV3 + a zkVM sub-proof bound by a shared commitment | B's | B's | B's | composition | B's problems **plus** composition (R5) | B + composition | — | inadmissible |
| **D1/E** single-shot multilinear IOP (zerocheck + GKR-LogUp + WHIR-style PCS) over A's AIR | ≈ A's columns, no quotient blowup | similar to A | 2–6 min (distributed, streaming commitment; research) | **≈ 150–300 KB** with no recursion | **stays in the ROM game with today's assumptions**; new L2/L3-level protocol proofs | A + 60–120 k (sumcheck, GKR, PCS, FS) | A + 6–12 months; distributed prover is research | prover engineering at 10¹² cells; Johnson proof again |
| D2 folding/IVC | — | — | — | Nova/HyperNova: curve assumptions (**not allowed**); hash-based accumulation (Arc/WARP-style) = R2: ROM-provable, no size gain without an in-circuit decider (back to R-a) | — | — | — | — |
| D3 per-contract specialisation | — | — | — | — | AIR fixed per challenge; impossible. Use generic *chips* instead (memcpy, u128 arithmetic, sha/keccak) | — | — | — |
| D4 lookup-heavy (Jolt-like) WASM machine | fewer columns, large tables | — | — | — | large tables proved by kernel `decide` are expensive in elaboration (2¹⁶ entries per table); prefer byte tables plus arithmetic | — | — | judge budget |

### 4.2 Why B (zkVMs) cannot be admitted: what the Lean artifacts actually prove

This section summarises the survey of `/data/illia/nearproof-deps/`.
* **sp1-lean.** Lean 4.28, Mathlib, 78 k lines. It proves 25 SP1 RV64IM chips against Sail-generated LeanRV64D.
  `sp1_machine_soundness` has 1 `sorry`, plus 25 `native_decide` and 8 `bv_decide`. About 76 Sail platform
  axioms sit in the target theorem. The lookup argument is assumed, and recursion and the PCS/FS layer are out of
  scope.
* **openvm-fv.** Lean 4.26, Mathlib, 407 k lines. It proves 45 RV32IM opcodes plus SHA/Keccak per *row* against
  Sail RV32, with 0 `sorry`. It assumes the bus/lookup argument and "the proof system". There is no whole-trace
  theorem. The certified verifier is generated from a private repository.
* **risc0-lean4** has 43 `sorry`s (`relation := sorry`). **zkLean** and the **jolt zklean-extractor** contain no
  soundness theorems. **ArkLib** (Lean 4.34, Mathlib, 314 k lines) has 180 `sorry`s, FRI relations `:= sorry`,
  and FS soundness as a TODO. It does prove sumcheck and the UDR proximity gap.
* **Final proofs:**
  * SP1 6.8.1: 100-bit target, Poseidon2 FS;
  * RISC Zero: 96–99 bits conjectured;
  * OpenVM: 100 bits;
  * Jolt: Dory (pairings) or lattice assumptions.

  None meets 128 bits with SHA-256 FS. Their small proofs come from Groth16/PLONK/Halo2 wraps, which need a
  trusted setup or curve assumptions.
* The repo's own SP1 pipeline was **REJECTED** by the formal judge (`ARTIFACT_BINDING_FAILED`, `MANIFEST_INVALID`,
  `CERTIFICATE_MISSING`, `OBLIGATION_UNDISCHARGED`; `docs/e2e-results/sp1-pipeline.md`). `D3_WASM_REQUIREMENTS`
  §2.3.1 rules out compile-to-RISC-V unless the compiler is proved, and no verified WASM→RISC-V compiler or verified
  wasmi exists.
* An admission statement would have to cover all four of:
  1. RISC-V ISA semantics, Mathlib-free on v4.34.1;
  2. whole-zkVM constraint soundness: memory, lookups, multi-shard, syscalls, precompiles;
  3. IOP/PCS/FS soundness re-parameterised to SHA-256 at 128 bits;
  4. a refinement proof that the *compiled binary* of an interpreter implements `NearSpecV3`'s WASM and host
     semantics, including gas points.

  Item (4) alone exceeds option A, which proves the WASM machine directly against the same semantics.

**Use B only as** an unranked EXPERIMENTAL cost baseline and as a source of GPU kernels.

---

## 5. Reuse, and what D1/D2 should do now

**What carries over to A / A+R:**

| asset | carries over | how |
|---|---|---|
| L1–L4 (field, BCS/FS, UDR IOP, AIR DSL, `HoldsP` + public segments) | A fully. A+R: inner layers yes; the final layer needs the Johnson-regime L3 variant plus grinding | protocol unchanged for segment proofs |
| L5 SHA-256 tables (two instances) | yes: code hashing, trie, receipts, and the **recursion AIR's hash rows** | unchanged |
| trie tables (`node/head/val/walk/uniq/ups/sizeA7`), `srcp`, `bnd`, `mrk`, `sort`, `acct`, `akey`, `qv` | yes: contract storage is trie reads/writes on the same buses | per-table views verbatim (23 of 25 tables, as D1) |
| `rcptV3` | partly: D3 adds promise/data/yield receipts and action receipts with FunctionCall. Expect a `rcptV3D3` variant (D2 needs one too) | first-row/offset edits as D1, plus new action kinds |
| scheduler/ChaCha tables | yes (claim/hint-side today; in-AIR for 300 KB) | — |
| D1 `txV3` MEM/AKMEM timestamped memory chain | **pattern** for WASM RAM (timestamped accesses, sorted continuity) | generalise to address spaces |
| `romSound_hint`, `stream_eq_of_count`, `bindPrepared` | yes, while hints remain (A); `stream_eq_of_count` also binds segment boundary streams | — |
| Lean WASM semantics (`NearSpecV3.Wasm.*`, logged `WasmStepE`, `WasmRun` with `Nat.strongRecOn`, `Segment.lean`) | **the target semantics of O2–O6** (EXEC step ⇒ `Wasm.Exec.step`); segment fold ⇒ continuations | read-only reuse |
| `npudr` Rust prover (generators, bus checker, `--check-only`, conformance) | yes; GPU port behind the same interfaces | — |
| judge tooling (`ClosureDeps.lean`, `judge-time.py`, `TypeHashes`) | yes; mandatory from day one | — |

**Recommendations to D1/D2 (concrete, now):**
1. **No new witness-derived hints.** Anything the verifier recomputes natively from *witness* data (not claim
   data) costs 300 KB later.
   * D1-N's tx hint is acceptable only as an interim measure.
   * Shape `txV3` so that `valid_i` is a column read from a bus. Today the native result arrives as a public
     segment; later a `sigV3` chip sends it. With that shape, D1-S is an additive table, not a `txV3` rewrite.
   * Bring the transactions in as committed witness bytes with an in-AIR SHA-Merkle check against the public
     `slotB2.txRoot`, instead of re-merklising them natively. This costs ≈ 40 SHA blocks per transaction and makes
     the hint removable.
2. **Make every table's height honest, not fixed at 2²²**, and keep `maxLog` a parameter. D1-S, D3 and segmenting
   all need it, and the D1 design already lists it as a prerequisite.
3. **Design `rcptV3` variants for extension.** D2 adds Delegate, Stake/AddKey/DeleteKey and DeployContract; D3
   adds FunctionCall, Data and yield receipts. Introduce **one action-dispatch bus** (action kind, receipt index,
   action index) with per-kind chips, rather than more columns in `rcptV3`. D2 should create it; D3's FunctionCall
   chip then plugs in.
4. **Contract-code path.** D2's `DeployContract` should already put code bytes through the SHA bus, keyed by code
   hash (`CODE` bus). D3's PREP AIR consumes that bus. D2 should also adopt code-size accounting compatible with
   segmenting PREP.
5. **Gas and compute as bus-carried values.** D2's action fees and D3's host and WASM gas should share a
   per-receipt gas accumulator, with exact `burnt`/`used`/compute and the promise-lowered limits. Put it in a
   single `gasV3` chip from D2 onward.
6. **Small modules and import hygiene** (V3-D1-DESIGN §6.3) are now essential: every D3 module counts against a
   budget that is already exceeded (§2.3).
7. **Protocol-independent statements.** State every new table's soundness as `TableLocal → View` and keep
   `Holds ⇒ Rel` free of FRI parameters. That way the tables survive a protocol change (Johnson-regime FRI,
   grinding, or the single-shot IOP of option E).

---

## 6. D3a exclusions: who can lift them, at what cost, and the spec PROPOSALS for "any mainnet chunk"

| exclusion (where) | A / A+R | B | cost (est.) | PROPOSAL needed |
|---|---|---|---|---|
| **`e.g_alpha`** (`D3/FunctionCall.lean:389`) | A: no (single proof). **A+R / E: yes** | yes (no admission) | §3; segmentation plus recursion | replace `G_α` with the chunk `gas_limit` (A1 already caps it at 10¹⁵); retire `e.g_alpha`; new tier `D3∞` (or `D3a'`). **Revisits R5** |
| floats (D3β, `prepare … = .outOfDomain`) | yes: FLOAT chip, soft-float with canonical NaN, proved vs the `F64` model | yes | Lean 30–60 k; rows ≈ 20–60 per float op | lift the float condition; spec W3 floats (f32 instance) + H3 |
| curve host functions (`ecrecover`, `ed25519_verify`, `p256_verify`, `alt_bn128_*`, `bls12381_*`) | yes, as non-native field chips (shared with D1-S Ed25519). Cost per Pgas is bounded by their gas: e.g. ≈ 300 ecrecovers/Pgas × ≈ 3 M cells ≈ 1 G cells; pairings ≈ 200/Pgas × 50–100 M cells ≈ 10–20 G | yes | Lean: ed25519 40–70 k (D1-S); secp256k1/p256 +20–40 k each; bn254/BLS12-381 pairings incl. map-to-curve 60–120 k each | spec the curves (FIPS/RFC/EIP) in `NearSpecV3`; D3γ/D3δ tiers |
| global contracts, deterministic state init, gas-key host families (`realOodHosts`), ETH-implicit `Local` (P5) | yes: mostly spec plus trie plumbing (different key namespaces, a code-resolution step) | yes | spec 5–15 k; AIR small (walks on existing tables) | spec E15 (global-contract code resolution), state-init semantics, legacy-wallet hashes |
| ML-DSA keys created by contracts (P4, `w.shape`) | key *storage* only: cheap (decode lengths) | yes | small | lift P4 in the action decoder |
| ML-DSA / secp256k1 *transaction* signatures (D1 scope) | yes: ML-DSA-65 is NTT over q = 8,380,417 < p_BabyBear, which is AIR-friendly; secp256k1 shares the ecrecover chip | yes | ML-DSA 30–60 k Lean; rows ≈ 10–30 M per signature | D1 tx-shape lift |
| **`e.code_cache`** (cache-dependent verdicts) | **no prover can lift it.** nearcore's verdict depends on the validator's compiled-contract cache, so the relation is ill-defined | no | — | upstream nearcore fix (deterministic cold-cache semantics), or a canonical-verdict decision (PROPOSAL; recommend keeping it out) |
| 4 MiB contracts vs PREP rows | A+R: segment PREP | yes | PREP AIR 20–40 k Lean | drop any `InD3α` code-size cap |
| D0a/D1a capacity bounds: A7 `B0 = 2.0 MB` (trie bytes), A9 `W0` ChaCha words, A10 `Dp0 = 32`, NT0 = 4,096, `w.size` 8 MiB (nearcore: 64 MiB) | A+R: segment trie and SHA tables too (global buses) | yes | rows: SHA ≈ 1.25 rows/B | raise `B0` to the mainnet witness maximum, `w.size` to 64 MiB, `NT0` to the protocol maximum; requires the mainnet replay (S1) for liveness numbers |
| resharding (D∞, `noResharding`) | yes in principle (claim plus trie split) | yes | spec + AIR (trie split proofs) 20–40 k | define the resharding relation (D∞) |
| per-receipt storage-proof limit, compute usage | already in spec; AIR must track `recorded_storage` per receipt | — | — | — |

"Any mainnet chunk" therefore needs these PROPOSALS: retire `e.g_alpha`, D3β, D3γ, D3δ, global contracts/state
init/gas keys, the P4/P5 lifts, raised capacity bounds (B0, `w.size`, NT0, A9/A10), resharding, and a decision on
`e.code_cache`. All of them assume the A+R or E prover.

---

## 7. Recommendation, phased plan, go/no-go checkpoints

**Recommendation.** Build option **A** as **protocol-independent** table proofs. Ship it first as a D3a tier
proof in today's stack (single proof, `G_α`, CPU), and plan from day one for **A+R**:
* segments on global buses;
* an aggregation tree;
* recursion to a Johnson-regime final layer ≤ 300 KB;
* a GPU prover on 2–4 × 8 H200.

Run **E** (single-shot multilinear IOP) as a funded research alternative until G1/G3. Do **not** pursue B except as a
benchmark.

**Phase 0: spikes that retire the biggest risks first (2–4 weeks, ≤ 4 lanes).**

| spike | question | output | lanes |
|---|---|---|---|
| **S1 mainnet replay** | real op-gas share, distinct contracts and code bytes per chunk, load/store share, touched memory, receipts, witness size; 1,000+ recent mainnet chunks through the pinned nearcore plus the clean-room VM counter in this lane | the mix table of §1 on real data; `B0`/`w.size` liveness | 1 (needs mainnet data access: PROPOSAL) |
| **S2 EXEC/RAM prototype** | cells per operator for the real layout (EXEC, RAM spaces, ALU lookups, gas points, CODE lookups) | Lean table values plus kernel `wf`/`W_eq`; Rust trace from the clean-room trace; `--check-only` on the 19 k corpus | 1 |
| **S3 size calculator** | exact bytes of a final layer under UDR / Johnson / STIR-WHIR, with grinding, at 192 query bits | extend `tools/recursion/r1_model.py`; reconcile with §2.2 | ½ |
| **S4 Johnson regime in Lean** | can BCIKS20-style correlated agreement up to `1−√ρ` (or the specific FRI/STIR lemma) be proved Mathlib-free on 4.34.1? | a written proof plan plus a kernel-checked core lemma (Guruswami–Sudan step) | 1 (research-heavy) |
| **S5 GPU prover** | our `npudr` LDE plus SHA-256 Merkle plus quotient on one H200 | measured cells/s vs 75 s per G on CPU | 1 (needs an H200) |
| **S6 recursion-node cost** | rows to verify one D0a-sized proof in-AIR (SHA vs Poseidon2) | count from `r1calib` breakdown; projection per node | ½ |
| **S7 judge budget** | projected elaboration for a D3a and an A+R certificate | `judge-time.py` model; budget PROPOSAL | ½ |

**Go/no-go.**
* **G1, after S3 + S4 (≈ 4 weeks).** Does the Johnson regime prove out, with ≤ 300 KB under S3?
  * If yes, A+R (or E) is viable.
  * If no, 300 KB is unreachable under a proven bound. The user then chooses: accept ≈ 0.7–0.9 MB (UDR + grinding
    + recursion), or the conjectured regime (an assumption, PROPOSAL).
* **G2, after S2.** If cells per operator ≤ ≈ 700, A at `G_α` fits ≤ 600 s after the prover work. Otherwise lower
  `G_α` (PROPOSAL) or move D3a to GPU.
* **G3: user decisions.**
  * R-a assumption: yes ⇒ A+R; no ⇒ E only.
  * Revisit R5.
  * Hardware profile.
  * Judge budget.
* **G4, after S1.** Re-dimension segments and the typical latency target from mainnet data.

**Phase 1: D3a tier on the current stack (≈ 4–8 months, 4 lanes; overlaps Phase 2).**
1. Spec freeze of `RelD3a` with D0a-style bounds (PROPOSAL `RelD3a := RelD3 ∧ A1… ∧ InD3α ∧ G_α`, as D1a did).
2. PREP AIR (decode/validate/finite-wasm points ⇒ CODE bus).
3. EXEC + RAM + ALU + gas.
4. CALL / stack budget.
5. Host chips: registers, context, storage on trie buses, promises/receipts on the action bus, logs, sha256/keccak/ripemd.
6. Link / `FactorD3` / completeness.
7. Rust prover with honest heights.
8. Certificate, under the judge-budget PROPOSAL.

Milestones: M1 PREP + EXEC on a toy contract (soundness and completeness of O2/O3); M2 all integer ops;
M3 host functions; M4 `ExtractD3aStmt`; M5 admitted locally.

**Phase 2: north-star infrastructure (parallel, ≈ 6–10 months).**
* GPU prover;
* segmented proving with global buses;
* the recursion AIR proved against `npVerifierP`;
* the Johnson-regime L3 plus grinding;
* aggregation;
* hints moved in-AIR (RS, scheduler, D1-S Ed25519);
* the final ≤ 300 KB layer;
* a GPU judge worker.

**Phase 3: lifts toward any mainnet chunk.** D3β, γ, δ, global contracts, raised bounds, resharding: §6.

---

## 8. Decisions needed from the user (all PROPOSALS)

1. **Security profile for recursion**: add an assumption that instantiates the ROM with the concrete hash (R-a),
   optionally plus Poseidon2 for inner layers (R-a'); or keep the profile and fund the single-shot IOP (E) only.
   This **revisits R5** (no composition).
2. **Proof-size regime**: confirm that 300 KB must hold under a *proven* bound (Johnson regime, research risk G1).
   The alternative is to accept the conjectured capacity regime as an assumption.
3. **Hardware profile** for a north-star tier: 2–4 nodes × 8 H200, `max_vram_bytes` > 0, `max_prove_ms`
   60–300 s, `max_proof_bytes` 307,200; a GPU judge worker; a GPU-hour price in the cost model.
4. **Judge elaboration budget**: 4 h → 8–12 h, or parallel elaboration with a CPU-seconds budget, for D3a and A+R
   certificates.
5. **P-D1-2**: mark native Ed25519 as interim; plan D1-S faithful plus in-AIR tx Merkle. D1a's relation is unchanged.
6. **Mainnet replay data access** for S1, and a GPU for S5.
7. **Spec roadmap** of §6: retire `e.g_alpha` in a new tier, raise the capacity bounds, and decide `e.code_cache`
   (recommend keeping it excluded and filing upstream).
8. **Latency expectation**: minutes for 1 Pgas, not block time. Confirm that the cross-shard asynchronous use is
   the target.

---

## 9. Evidence and reproduction

* Workload: `tools/d3a-study/instr.py OUT.jsonl CASE_DIR...` (needs `claim.bin`; public fixtures need a
  `claim.bin → request.bin` link), then `tools/d3a-study/agg.py OUT.jsonl...`, and
  `tools/d3a-study/metascan.py DIR` for the meta-only scan.
  * Results: `docs/e2e-results/v3-d3a-study/workload-{public-chunk-v3,corpora-d3c7-10}.txt`.
  * Raw data: `/data/illia/nearproof-deps/validation/v3-d3a-study-20261014/`, hashes in `raw-sha256.txt`.
  * Run with `taskset -c 8,9,24,25`, 4 shards, ≈ 15 min.
* §2.2 size model: queries = ⌈(192 − z)/b⌉. Per query:
  `4·W_eq + 3·32·(L − log₂q) + Σ_FRI-layers (8·32 + 32·(dᵢ − log₂q))`, with `L = log₂ LDE`. The fixed part is the
  roots, the final polynomial (2⁶ ext) and OOD (2·W_eq ext). W_eq = 300, z = 32, arity 8. This is an *estimate*;
  S3 replaces it with the exact FORMATS-based model.
* Throughput anchors: `docs/logs/v3-prover-perf-2026-10.md` (D0a), `docs/research/recursion-r1-cost.md` (R1
  presets and S-curves), `docs/research/checker-recommendations.md` §5 (SP1/RISC Zero/wasmi),
  `docs/e2e-results/sp1-pipeline.md` (SP1 judge run).

---

## 10. Re-plan under U-1…U-4: near-real-time, SHA-256-only recursion, proven bounds

### 10.1 Target assumed

| class | gas | latency target (end of chunk execution → proof available) |
|---|---|---|
| typical mainnet chunk | ≤ ≈ 50–300 Tgas (**ASSUMPTION** until S1; the mainnet chunk gas limit is 1 Pgas, but typical use is well below it) | **≤ 1–2 s** |
| worst case | 1 Pgas, adversarial pure WASM (1.22·10⁹ operators) | ideally ≤ 2 s; the question is whether that is feasible |

There is one floor that no hardware removes. NEAR prices 1 Pgas at ≈ 1 s of *native* execution on validator
hardware (gas ≈ ps: 1 Tgas ≈ 1 ms). The prover must at least execute the chunk, so worst-case latency is
≥ ≈ 1 s plus proving. Proof work can overlap that execution only if segments start proving while later segments
are still executing (§10.5, lever L1).

### 10.2 Cost model under U-1 and U-2 (estimated)

* **Base (segment) work.** 494–995 W-eq cells per WASM operator (ASSUMPTION, S2). D0a-type plumbing, trie and
  SHA for the witness: ≈ 1.25 SHA rows per witness byte × 704 ≈ 0.9 k cells/B. A 5 MB witness is ≈ 4.4 G cells.
* **Segment proof (inner) parameters under U-2.**
  * Proven UDR at rate 1/2–1/4 with 32-bit grinding. The inner proof is never transmitted; it only feeds
    recursion.
  * A low blowup keeps the LDE cheap, but UDR gives < 1 bit per query at rate 1/2. That needs ≈ 300+ queries,
    which makes the recursion verifier expensive.
  * The best trade-off is ≈ blowup 4 (UDR ≈ 0.68 bits/query → ≈ 235 queries at z = 32) or blowup 16
    (176 queries). S3 settles it.
* **Recursion node under U-1 (SHA-256 in-AIR).**
  * Verifying one inner proof of W_eq ≈ 500 at 176–235 queries costs ≈ 300 SHA compressions per query (leaf
    rows ≈ 32 blocks, 3 Merkle paths ≈ 66, FRI ≈ 200). That is ≈ 53–70 k compressions × 12 k ≈ **0.65–0.85 G
    cells**, plus Fp8 arithmetic and the inner-AIR DAG evaluation (≈ +30 %): ≈ **0.85–1.1 G cells per child
    proof**.
  * D0a's real proof needs ≈ 236 k compressions ≈ 2.8 G cells (V3-D0-DESIGN §5.5).
  * So **a 2²²-operator segment (2–4 G base cells) carries ≈ 25–50 % recursion overhead per tree level it
    feeds**, at arity 4.
  * Summing over a tree of depth d ≈ log₄(S) with similar-sized node proofs gives **total recursion work
    ≈ 0.4–0.7 × base**. Total ≈ **1.4–1.7 × base**.
* **Correction to §2.3.** R-a' (Poseidon2) is no longer available. The ≈ 20–50× cheaper hash nodes are gone, and
  the figures above already use SHA-256.
* **Final layer.** Johnson regime (if S4 succeeds) at blowup 2⁶–2⁸, with a shrinking trace 2¹⁶–2¹⁸. Its prove
  time is dominated by the LDE of a 2¹⁸ × ≈ 300 trace at blowup 2⁸ (≈ 2·10¹⁰ cell evaluations plus SHA Merkle):
  **≈ 0.2–0.5 s on one H200** (estimated).
* **GPU throughput (ASSUMPTION; S5/S8 measure it).** Our STARK on one H200 is planned at 0.5–2·10⁹ W-eq cells/s.
  For SHA-256 alone (Merkle commitments):
  * cited: hashcat mode 1400 (SHA2-256) is reported at ≈ 22 GH/s on an RTX 4090 (Chick3nman benchmark gist);
  * I found no published H200 figure;
  * **estimate for an H200: ≈ 10–20 G compressions/s** (integer-ALU bound, similar to or below a 4090).
  * Committing the LDE of 10¹² cells at blowup 2 hashes ≈ 8 TB ≈ 1.25·10¹¹ compressions ⇒ **≈ 0.2–0.4 s on 32
    H200s**. Native SHA is therefore *not* the binding cost at 1 Pgas. In-AIR SHA in recursion nodes is (above).

### 10.3 Feasibility verdict and real-time envelope (estimated)

**Plain answer: near-real-time (≈ 1–2 s) worst-case 1 Pgas is NOT feasible on 2–4 × 8 H200.**

**Worst case 1 Pgas:**
* total work ≈ (0.6–1.2 T base cells) × 1.4–1.7 ≈ **0.85–2.0 T cells**;
* on 16–32 H200s at 0.5–2 G cells/s each (8–64 G cells/s): **≈ 13–250 s**, central estimate ≈ 30–60 s on 32 GPUs;
* plus the ≥ 1 s execution floor and ≈ 5–8 tree levels × 0.1–0.3 s critical path.

**What IS achievable in ≈ 1–2 s on 32 H200** (≈ 1 s of proving after a pipelined ≈ 0.5 s of tree and final
layer):
* the budget is ≈ **10–40 G cells** of base work;
* pure-WASM adversarial gas: 10–40 G ÷ (494–995 × 1.5) ≈ **7–54 M operators ≈ 6–45 Tgas worst-case**. At the
  central estimate (1 G cells/s/GPU, d3-lean) that is **≈ 25 Tgas worst case, ≈ 7 × today's `G_α`**;
* **typical mix** (measured synthetic: 37–52 k WASM instructions per Tgas; a mainnet mix with heavier memory use
  is ASSUMED ≤ 2× that):
  * a 300 Tgas chunk is ≈ 11–31 M instructions ≈ 8–46 G cells, plus witness plumbing ≈ 4–10 G;
  * **≈ 100–300 Tgas typical-mix chunks fit in ≈ 1–2 s on 32 H200** at the central-to-optimistic throughput;
  * on 16 H200 the envelope halves.
* So **real time is decided by the worst case, not the typical case**. A real-time tier needs a *worst-case*
  admission bound: an `InD3` cells/gas budget that bounds pure-WASM gas, e.g. a per-chunk WASM-operator cap
  ≈ 25–50 Tgas-equivalent, while host-heavy gas up to 1 Pgas stays allowed. This is a PROPOSAL (P-RT-1, below):
  it replaces `G_α`'s "total FC gas" with a **weighted gas budget** (each gas category weighted by its proving
  cells).

**Hardware for worst-case 1 Pgas in ≈ 2 s:**
* ≈ 1 s of proving for 0.85–2.0 T cells needs 0.85–2.0 T cells/s, i.e. **≈ 450–4,000 H200s (≈ 60–500 8-GPU
  nodes)** at 0.5–2 G cells/s each;
* central estimate ≈ **1,000 H200s**;
* plus a cluster interconnect able to move ≈ 10–30 TB of trace/LDE within the second (trace generation must be
  local to the GPUs: each node re-executes its segments from snapshots).

That is two orders of magnitude above the stated budget. Even then latency ≥ execution (≈ 1 s) + one segment +
tree depth, so ≈ 2–3 s is the realistic floor.

**State of the art (cited, not reproduced):**
* the Ethereum Foundation defines real-time proving as ≥ 99 % of L1 blocks within 10 s;
* SP1 Hypercube: 99.7 % of 954 mainnet blocks in < 12 s on 16 RTX 5090s (earlier: 93 % of 10,000 blocks,
  average 10.3 s, on ≈ 200 RTX 4090s);
* ZisK: 7.4 s on 24 GPUs;
* ZKsync Airbender: strong single-GPU throughput, scaling linearly across GPUs.

Ethereum blocks are ≈ 30–60 Mgas EVM. These systems target ≈ 100-bit, partly conjectured security with
Poseidon2/BLAKE-style hashes over KoalaBear/BabyBear or multilinear PCS. **Our constraints are strictly costlier:**
* 128-bit *proven* bounds with 2⁶⁴ hash queries (≈ 192 query bits; UDR inner proofs need ≈ 2–4 × their query
  counts);
* SHA-256 everywhere (in-AIR SHA ≈ 10–50 × an algebraic hash per compression);
* a **10 × tighter latency target** (1 s vs 10 s).

As a rough calibration (estimate): what SP1 does in 10 s on 16 GPUs we would do in ≈ 30–100 s on 16 GPUs. That is
consistent with §10.3's figures.

### 10.4 Best proven proof size (U-2)

| layer regime (Lean status) | final proof (estimated, §2.2 model) | depends on |
|---|---|---|
| UDR + 32-bit grinding (UDR proved in Lean; grinding needs an L2/L3 lemma) | **≈ 0.70–0.90 MB** | recursion (U-1) + grinding lemma; hints in-AIR |
| Johnson regime FRI, blowup 2⁶–2⁸, z = 32 (proven in literature; **Lean proof is S4, research**) | **≈ 230–350 KB** (≈ 230–270 KB at blowup 2⁸, trace 2¹⁶–2¹⁸) | S4 succeeding Mathlib-free; BabyBear 2-adicity 27 forces final trace ≤ 2¹⁸ ⇒ an extra shrink layer |
| Johnson-regime STIR/WHIR-style low-degree test (proven; Lean: S4 plus a new LDT proof) | ≈ 120–200 KB (±50 %) | S4 plus a new protocol layer, ≈ 20–40 k lines |

So **≤ 300 KB under a proven bound is reachable only if the Johnson-regime proximity gap is proved in Lean** (G1).
Otherwise the best proven size is **≈ 0.7–0.9 MB**. Larger digests or a different field do not change this:
SHA-256 digests are fixed at 32 B, and an extension field ≥ 2²⁴⁸ already makes the field error terms negligible.

**Latency vs size.** The Johnson-regime final layer adds ≈ 0.2–0.5 s (high blowup). The UDR final layer is cheaper
to prove but ≈ 3 × larger. At a 1 s budget this trade matters, and the size/latency switch is a tier parameter.

### 10.5 Design levers, ranked by impact on real-time capacity

| # | lever | effect (estimated) | cost |
|---|---|---|---|
| L1 | **Prove while executing.** The native executor emits segment snapshots; GPUs start segment k while k+1 executes | hides most of the ≈ 1 s execution floor; latency ≈ max(exec, prove) + tail | prover engineering; no Lean |
| L2 | **Wide, shallow aggregation** (arity 8–16, segments of 2²⁰–2²² operators) | depth 3–4 instead of 5–8, so ≈ 0.3–1 s off the critical path; per-node SHA cost grows with arity but runs in parallel | recursion AIR parametric in arity |
| L3 | **Per-receipt / per-call parallel segments.** Receipts execute sequentially in nearcore, but each call's WASM run is a separate segment family; the state overlay is bound on trie buses | more parallelism for many-call chunks; no help for one giant call | the relation's segment fold (`Segment.lean`) generalised to receipts |
| L4 | **Fewer cells per operator**: lookup-heavy ALU (byte tables), fusing locals into EXEC rows (locals plus const are 49 % of instructions; register-like local caching), fused superinstructions (`local.get; i32.const; i32.add`) | cells/op 494 → ≈ 250–350 (target); the real-time envelope scales inversely | S2; larger tables must stay cheap in elaboration |
| L5 | **Inner-proof parameters**: blowup 4–16 vs query count; grinding z = 32–40 bits | ≈ 1.5–2 × on recursion cost | L3 parameter proofs |
| L6 | **GPU SHA-256 throughput** (Merkle, and the in-AIR SHA trace generation) | ≈ 0.2–0.4 s at 1 Pgas on 32 GPUs; must be overlapped | S8 measures it |
| L7 | **Pipelining across blocks** | raises *throughput* (one proof per block sustained) but **not latency** | — |
| L8 | Hardware | linear in GPUs up to the tree/execution floor | budget |

### 10.6 PROPOSALS added by this re-plan

* **P-RT-1 (domain).** A real-time tier bounds *proving-weighted* gas: `Σ_cat w_cat · gas_cat ≤ Γ`, with weights
  from measured cells per gas (WASM operators ≫ host fees ≫ hashing per gas), instead of `G_α` on total FC gas.
  Sized so that the worst case fits ≈ 1–2 s on the stated hardware (≈ 25 Tgas pure-WASM-equivalent on 32 H200,
  central estimate). Host-heavy chunks up to 1 Pgas remain inside. Requires S1/S2/S5.
* **P-RT-2 (security profile, implements U-1).** Add the allowed assumption
  `sha256-random-oracle-in-circuit`: "the Lean-proved ROM soundness bound of the pinned inner verifier holds with
  the oracle instantiated by SHA-256 as arithmetised by the pinned L5 table". Set `max_aggregation_depth` per tier
  (≤ 8). The admission theorem's ROM branch gains a recursion clause. The arithmetisation-matches-`npVerifierP`
  part stays **proved**.
* **P-RT-3 (judge, implements U-3).**
  * Elaboration runs as `lake build -j N` with **N = 16** cores under a **4 h wall** limit. The per-module 1 h
    limit stays. Total CPU-seconds is reported and capped at N × 4 h.
  * Determinism: oleans must be byte-identical between `-j 1` and `-j N` (spot-checked at registration).
  * **Recheckers:**
    * leanchecker and nanoda check environments module-by-module or in parallel. Allow N-core parallel runs,
      keeping 2 h wall per run and 4 h wall per rechecker.
    * lean4lean (3,223 s serial for D0a) would be ≈ 3–5 × that for an A+R certificate (≈ 3–4.5 h serial). It
      needs parallel replay over independent module subsets, or its 4 h limit becomes binding.
    * S7 measures the critical path of the module DAG: wall ≥ critical path regardless of N.
  * Estimate: D0a is 7,000 s CPU, so at N = 16 the wall is ≈ max(critical path, 440 s). An A+R certificate is
    17–34 ks CPU, so at N = 16 the wall is ≈ max(critical path, 1.1–2.1 ks). That fits 4 h unless a single chain
    of modules exceeds it, which needs the small-module discipline of §5.
* **P-RT-4 (hardware/challenge).** Real-time tier hardware profile `2–4 × 8 H200`, `max_vram_bytes` ≈ 1.1 TB per
  node, `max_prove_ms` ≈ 2,000 (typical-class) with a worst-case class at the P-RT-1 bound, and a GPU judge worker.
  *Separate* "capacity" classes up to 1 Pgas with `max_prove_ms` 60,000–300,000 measure throughput and cost
  without claiming real time.

### 10.7 Updated recommendation and plan

**Recommendation (unchanged core, re-targeted).**
* Build **A+R with SHA-256 recursion** (U-1).
* Table soundness stays protocol-independent.
* The first admitted artifact is the **D3a single-proof tier on CPU** (Phase 1), as before.
* The north star becomes a **real-time tier under P-RT-1** (weighted gas bound, ≈ 1–2 s on 32 H200), plus
  non-real-time 1 Pgas capacity classes.
* **Worst-case real-time 1 Pgas is not a goal on this budget.** It would need ≈ 500–4,000 H200s; I recommend not
  pursuing it.
* Option E (single-shot multilinear IOP) is deprioritised. It avoids the SHA-in-circuit cost, but its monolithic
  distributed commitment is latency-hostile and it is research-grade. Keep only S4, which both A+R and E need.

**Spikes (Phase 0, ≈ 3–5 weeks, ≤ 4 lanes; S5/S8/S9 need one H200).**

| spike | question | go/no-go |
|---|---|---|
| S1 mainnet replay | real typical gas, mix, contracts and witness per chunk | sets the typical-class target (G4) |
| S2 EXEC/RAM prototype + L4 levers | measured cells/operator; target ≤ 350 | G2: ≤ 700 keeps the D3a CPU tier viable; ≤ 350 doubles the real-time envelope |
| S3 size calculator | exact proven sizes: UDR+grinding vs Johnson; inner-proof parameter sweep (L5) | input to G1 |
| **S4 Johnson regime in Lean** (Mathlib-free) | the only route to ≤ 300 KB under U-2 | **G1**: fail ⇒ accept ≈ 0.7–0.9 MB proven |
| S5 GPU STARK kernel | our LDE + quotient + Merkle on one H200: cells/s | **G5**: < 0.5 G cells/s ⇒ real-time envelope < 10 Tgas worst case; rethink |
| S6 recursion-node cost | rows to verify a segment proof with in-AIR SHA (U-1), arity 4–16 | confirms the 1.4–1.7 × total |
| S7 judge parallel elaboration | `-j 16` wall time, critical path, recheck times for D0a (and a projected A+R closure) | supports P-RT-3 |
| **S8 GPU SHA-256 throughput** (new) | compressions/s on an H200 for Merkle-tree layouts (leaf rows of 1–12 KB, arity-2 inner nodes), and in-AIR SHA trace generation rate | input to L6 |
| **S9 latency-budget prototype** (new) | an end-to-end critical-path model with real timings: native execution with snapshots (nearcore or the clean-room VM), segment trace generation, simulated segment and node proofs on GPU, tree depth vs arity, final layer | **G6**: does a 25 Tgas pure-WASM chunk fit in 2 s on the available GPUs? Sets P-RT-1's Γ |

**Phases.**
* **Phase 1 (4–8 months):** D3a CPU tier, as in §7. D1-N proceeds with P-D1-2 **interim**; the D1/D2 shaping advice
  of §5 is unchanged and now essential: no witness-derived hints, honest heights, action-dispatch bus, CODE bus,
  `gasV3` chip.
* **Phase 2 (6–10 months, parallel):**
  * the GPU prover (S5 → production);
  * segmenting with prove-while-execute (L1);
  * the SHA-256 recursion AIR proved against `npVerifierP`;
  * grinding lemma; Johnson-regime L3 (if G1 passes);
  * hints in-AIR (RS, scheduler, D1-S Ed25519);
  * the P-RT-3 judge;
  * GPU judge worker.
* **Phase 3:** real-time tier under P-RT-1 (Γ from S9), then lifts (§6). Raise Γ as cells/operator (L4) and
  hardware improve.

### 10.8 Decisions still open (all PROPOSALS)

1. **P-RT-1**: replace `G_α` with a proving-weighted gas bound for the real-time tier. This accepts that
   worst-case 1 Pgas is *not* real time on 2–4 × 8 H200. Alternatively, fund ≈ 500–4,000 H200s, or relax the
   latency target for worst-case chunks.
2. **P-RT-2**: the exact wording of the SHA-256-in-circuit assumption and the recursion clause in `CryptoSound`.
3. **P-RT-3**: N = 16 parallel elaboration / 4 h wall, and parallel rechecking (especially lean4lean).
4. **P-RT-4**: the real-time and capacity hardware profiles and the GPU judge worker.
5. **If G1 fails**: accept ≈ 0.7–0.9 MB proven proofs, as U-2 already implies, or keep 300 KB as a stretch only.
6. Access to mainnet data (S1) and an H200 (S5/S8/S9).

Sources cited in §10 (published, not reproduced here):
* SP1 Hypercube real-time claims: <https://www.theblock.co/post/355013/succinct-introduces-zkvm-sp1-hypercube-claims-real-time-ethereum-proving>
* the 16 × RTX 5090 / 99.7 % figure, ZisK 24 GPUs / 7.4 s, Airbender, and the EF definition of real-time proving:
  <https://blockeden.xyz/blog/2026/01/30/zksync-airbender-fastest-risc-v-zkvm-ethereum-proving/>
* hashcat SHA2-256 GPU benchmarks: <https://gist.github.com/Chick3nman/e4fcee00cb6d82874dace72106d73fef>,
  <https://hashcat.net/forum/printthread.php?tid=11787>

---

## 11. Post-quantum 128 (U-5): size, recursion, security and latency

Inputs:
* research branch `research/hash-recursion` @ `26e538be`, read-only: `research/hash-recursion/README.md`, the
  `Wire`/`Budget` modules, `docs/research/recursive-compression.md`;
* the size model `tools/d3a-study/pqsize.py`, new in this lane;
* the literature cited below.

**Which theorems hold with which constants is my reading of the papers. Pinning them is the research branch's
milestone M3, and nothing here is proved.**

### 11.1 The security contract this section assumes (needs a user decision)

The research README distinguishes two contracts: "128-bit quantum attack cost" and "failure ≤ 2⁻¹²⁸ for a bounded
adversary". I use the **second**, carried over from today's profile:
* failure ≤ 2⁻¹²⁸;
* against an adversary making **t ≤ 2⁶⁴ quantum hash queries** (`max_hash_queries_log2 = 64`);
* with 2⁴⁰ prover queries.

A different t moves every number below. That is decision PQ-D1.

### 11.2 What PQ changes, term by term

| term | classical today | PQ-128 (t = 2⁶⁴) | source / reasoning |
|---|---|---|---|
| **Fiat–Shamir transform** | ROM; L2's potential argument charges each query, with no multi-round blow-up | Generic multi-round measure-and-reprogram loses `(2t+1)^{2r}` for r rounds (Don–Fehr–Majenz, eprint 2020/282). With r ≈ 10–25 FRI/STARK rounds that is **useless**. The usable route is **round-by-round soundness ⇒ QROM soundness of BCS** with a loss ≈ `O(t²)·ε_rbr + O(t³/2^λ)` (Chiesa–Manohar–Spooner, TCC 2019, eprint 2019/834; rbr notions and QROM transfers in Block–Garreta–Tiwari–Zając, eprint 2023/1256). | the per-round error needed is ε_rbr ≲ 2⁻¹²⁸⁻¹²⁸⁻ᶜ, so **≈ 260 bits per round** (c ≈ 4 for the hidden constants; to be pinned in M3) instead of ≈ 192 |
| **query phase** | 192 − z bits from queries | ≈ 260 − z/2 bits | Grover gives a quadratic speed-up on grinding, so z classical bits of work buy only z/2 PQ bits |
| **algebraic challenges** (bus α/γ, ALI, DEEP, FRI folding) | Fp8 of BabyBear (2²⁴⁸) suffices for 2⁻¹³² | each round needs ≲ 2⁻²⁶⁰ with degree/size factors up to 2²⁷, so **\|K\| ≳ 2²⁹⁰ ⇒ a degree-10 or degree-12 extension** (2³¹⁰ / 2³⁷²) | **Fp8 is insufficient for PQ**: +25–50 % on every extension (aux, quotient, OOD) column |
| **Merkle binding / digest width** | SHA-256, 2¹²⁸ birthday bound | quantum collision search on an n-bit random function: success ≈ `O(t³/2ⁿ)` (BHT; tight per Zhandry, arXiv 1312.1027). With n = 256 and t = 2⁶⁴ that is **2⁻⁶⁴: SHA-256 is insufficient**. n = 384 gives 2⁻¹⁹²; n = 512 gives 2⁻³²⁰ | the research branch's `Budget` checks the same template arithmetic |
| **hash choice** | SHA-256 | **SHA-384** (SHA-512 compression, 384-bit output) or **SHA-512**. Not 2 × SHA-256 concatenation: concatenating iterated hashes is not stronger than its parts (Joux multicollisions), and the README already warns that wider or concatenated digests are not ideal wide QROs. SHA-384/512 as a QRO is itself an *assumption*, the same kind as today's SHA-256 ROM assumption | PROPOSAL PQ-D2 |
| **recursion composition** | concrete SHA-256 as the RO in-circuit (U-1) plus soundness | needs **quantum knowledge extraction** (research branch M4). The rbr route gives knowledge soundness only under rbr *knowledge* soundness. Extraction against quantum adversaries is the deepest open item (compressed-oracle recording, Zhandry eprint 2018/276) | — |

### 11.3 Re-checking U-1 (SHA-256-only recursion) under PQ

**U-1 cannot hold for the PQ track.** SHA-256 Merkle commitments give only ≈ 2⁻⁶⁴ binding against 2⁶⁴ quantum
queries. **PROPOSAL PQ-D2:** for the PQ track, change U-1 to "SHA-2 only, SHA-384 (or SHA-512) everywhere in the
proof system, inside and outside circuits". SHA-256 stays for the classical tiers.

In-circuit cost:
* L5 SHA-256: 17 rows × W_eq 704 ≈ **12 k cells per compression**. A Merkle node (64 B + padding) needs 2
  compressions, so ≈ 24 k cells per node.
* A SHA-512-family table: 64-bit words as 2 × 32-bit limbs, 80 rounds. V3-D1-DESIGN §4.2 estimates W_eq ≈ 1,100
  and ≈ 25–40 k cells per 128-B block.
* **SHA-384 node** (2 × 48 B = 96 B + padding ≤ 128 B) = **1 compression ≈ 25–40 k cells**, i.e. ≈ 1.0–1.7 × a
  SHA-256 node.
* SHA-512 node (128 B + padding) = 2 compressions ≈ 50–80 k cells (2–3.3 ×).

**SHA-384 is the sweet spot** if t = 2⁶⁴. SHA-512 is needed only under a stronger contract (t = 2¹²⁸).

Native GPU cost:
* SHA-512 uses 64-bit additions, which GPUs emulate. My **recollection** of hashcat is ≈ 7 GH/s for SHA-512 against
  ≈ 22 GH/s for SHA-256 on an RTX 4090. That is **not verified here**; S8 measures it.
* Per byte, SHA-512 is then ≈ 1.5 × slower.
* At 1 Pgas, commitment hashing goes from ≈ 0.2–0.4 s to **≈ 0.3–0.6 s** on 32 H200s.

### 11.4 PQ proof size: best justifiable proven figure

**Correction to §2.2/§10.4.** The earlier model assumed a final trace of 2¹⁴–2¹⁶ rows. In a recursive chain, the
last layer's trace must contain the verifier of the previous layer, so its height is a *fixed point*. For the PQ
Johnson case at blowup 2⁶:
* the previous layer is opened at ≈ 85 queries;
* each query needs ≈ 220 SHA-384 compressions (3 Merkle paths of ≈ 20 levels, leaves of ≈ 10 blocks per tree,
  ≈ 7 FRI layers);
* that is ≈ 19 k compressions × 30 k cells ≈ 0.56 G cells, so **≈ 2²¹ rows at W_eq 300**.

The same argument puts the classical final layer at ≈ 2¹⁹–2²⁰ rows. Its realistic size is therefore **≈ 320–400 KB**,
not 230–270 KB.

With BabyBear (2-adicity 27), a 2²¹ trace allows blowup ≤ 2⁶.

Final-layer size (`pqsize.py`: 260 − z/2 query bits, z = 32; 48/64-B digests; 40-B extension elements; top
log₂(q) Merkle levels shared; W_eq 200–600):

| final-layer regime (Lean status) | queries | SHA-384 | SHA-512 |
|---|---:|---:|---:|
| UDR, blowup 2⁶, trace 2²¹ (UDR algebra proved in Lean; PQ FS not) | 250 | **1.9–2.3 MB** | 2.3–2.8 MB |
| FRI Johnson, blowup 2⁶, trace 2²¹ | 85 | **0.71–0.88 MB** | 0.87–1.04 MB |
| FRI Johnson, blowup 2⁸, trace 2¹⁹ (needs W_eq ≈ 1,000 to fit the verifier) | 63 | ≈ 0.6–0.75 MB | ≈ 0.7–0.85 MB |
| STIR/WHIR-class LDT, Johnson regime (rate decays per round; fewer, cheaper later queries) | — | **≈ 0.3–0.5 MB** (est., ±50 %) | ≈ 0.35–0.6 MB |

Levers not in the model:
* **Merkle multiproof dedup** (siblings shared between query paths beyond the top log₂(q) levels, and between
  FRI-layer cosets): ≈ −10–20 %.
* **Caps** (publishing the top c levels once): already captured by the log₂(q) sharing; at most a few KB more.
* **A field with larger 2-adicity** (Goldilocks: 2³², with a degree-5/6 extension for 2²⁹⁰+) would allow blowup 2⁸
  at trace 2²¹, about −15–25 %. That is a protocol-wide change.

**Verdict.** Under PQ-128 with *proven* bounds (U-2), the best I can justify is:
* **≈ 0.6–0.9 MB with FRI in the Johnson regime;**
* **≈ 0.3–0.5 MB with a STIR/WHIR-class test** (uncertain);
* ≈ 2 MB with what Lean can prove today (UDR).

**< 300 KB is not reachable with FRI.** It is *conceivable* only with:
* a WHIR-class test in the Johnson regime;
* multiproof dedup;
* favourable pinned QROM constants;
* possibly a larger-2-adicity field.

It is marginal even then. My recommendation is to plan for **≈ 0.5–1 MB** and treat 300 KB as a stretch goal.

**New Lean proofs required** (none exist; all Mathlib-free on 4.34.1):
1. **Johnson-regime proximity gaps / correlated agreement** (BCIKS20-type) — S4, formerly classical-only.
2. **rbr (knowledge) soundness** of the chosen IOP: FRI or STIR/WHIR, plus the AIR/bus/DEEP rounds, at ≈ 260 bits
   per round. L3 today proves the potential-style ROM bound, not rbr knowledge.
3. **A QROM model** (research M1): complex amplitudes, unitary adversaries, a uniformly random function, Born-rule
   probabilities.
4. **QROM BCS / Fiat–Shamir** with explicit constants (M3), including Merkle binding (`O(t³/2ⁿ)`).
5. **Quantum extraction / composition for recursion** (M4).
6. **A parameter set plus serializer bridge to the Wire model** (M5). This study's `pqsize.py` is a draft input.
7. The classical-side **arithmetisation proofs**, now against a PQ-parameterised verifier model: SHA-384 table,
   degree-10/12 extension, new query counts.
8. A **SHA-512-family compression table** with an L5-style proof. It is shared with D1-S Ed25519 (SHA-512), see
   §11.6.

### 11.5 Updated real-time envelope and hardware (estimated)

Cost factors, PQ against the §10 classical figures:
* inner-proof queries ×(244/160) ≈ 1.5;
* recursion-node hashing per compression 1.0–1.7 × (SHA-384);
* extension columns ×1.25–1.5.

Results:
* recursion overhead 0.4–0.7 × base becomes **≈ 0.8–2.2 × base**;
* base cells +10–20 %;
* total ≈ **2.0–3.8 × base**, against 1.4–1.7 classically.

| quantity (32 × H200, ≈ 1–2 s) | classical (§10.3) | **PQ-128** |
|---|---|---|
| worst-case pure-WASM gas per chunk | 6–45 Tgas (central ≈ 25) | **≈ 3–25 Tgas (central ≈ 12)** |
| typical-mix chunks | ≈ 100–300 Tgas | **≈ 50–150 Tgas** |
| H200s for worst-case 1 Pgas in ≈ 2 s | 450–4,000 (central ≈ 1,000) | **≈ 600–9,000 (central ≈ 2,000)** |
| final layer (Johnson, 1 GPU) | 0.2–0.5 s | 0.3–0.8 s |
| native commitment hashing at 1 Pgas | 0.2–0.4 s | 0.3–0.6 s |

**Plain answer: near-real-time worst-case 1 Pgas is further out of reach under PQ.** The real-time tier's weighted
gas bound (P-RT-1) would be about half the classical one.

The PQ final layer could run as an **asynchronous "PQ wrap"** over a classical real-time proof. That is not a
real-time PQ guarantee, since its soundness is only as good as the classical layers inside it. It makes sense only
if the user accepts PQ-at-rest (archival and light-client use) rather than PQ-at-validation. That is decision PQ-D3.

### 11.6 Does PQ change Phase 1, D1 or D2 now?

The classical relations, tiers and the signed D0a are unchanged. Five cheap alignments are worth doing now:
1. **Build one SHA-2 compression family, not just SHA-256.** D1-S (Ed25519) already needs `sha512V3`. Design it
   as a generic SHA-512-family table with a parametric IV and truncated output (SHA-384, SHA-512), proved in L5
   style. It then serves Ed25519, D3's host `sha512`-free paths, and **the PQ commitment and recursion hash**.
   This adds no work to D1-N (interim P-D1-2 stands).
2. **Parameterise new protocol code.** Any new prover, verifier-model or format code (GPU prover, recursion AIR,
   `pqsize`/S3 calculators) takes **digest width, hash and extension degree as parameters**, not 32 B / SHA-256 /
   Fp8 constants. The deployed `np-udr-stark-v2` is untouched.
3. **Keep table soundness generic in the extension field.** New D1/D2/D3 table proofs should not specialise
   lemmas to Fp8. Then a degree-10/12 extension needs only re-instantiation (check during S2).
4. **No new witness-derived hints** (§5). This matters even more under PQ, because every PQ byte is costlier.
5. **Unchanged:** the NEAR relation's own SHA-256 (trie, receipts, block hashes) and Ed25519. They are the
   *statement*, not proof-system assumptions. The D0a design never relies on SHA-256 collision resistance for
   `Holds ⇒ Rel`. Making NEAR itself PQ is out of scope, as the research README also notes.

### 11.7 Merging this lane with `research/hash-recursion`

Proposed split. The research branch is the **formal home of the PQ track**; this lane covers AIR, cost and latency.

| research M# (README) | owner | this lane's input / what to avoid duplicating |
|---|---|---|
| M1 finite quantum experiment | research | — |
| M2 interactive protocol + soundness | **shared**. This lane's **S4** (Johnson-regime proximity gaps) becomes the FRI/STIR/WHIR part of M2, in their Std-only package; no separate S4 lane | S3 sweeps choose FRI vs STIR vs WHIR |
| M3 quantum FS with constants | research | §11.2's ≈ 260-bit-per-round target is the requirement M3 must confirm or correct |
| M4 extraction / composition | research | the recursion AIR's arithmetisation (classical-side, §2.3 table) stays here |
| M5 parameters + serializer → Wire | **joint**. `tools/d3a-study/pqsize.py` (this lane) plus the fixed-point recursion-height model feed their `Wire` module; one calculator, kept in `tools/recursion/` | S3 and S6 deliver here |
| RISC Zero harness | frozen as a baseline (non-PQ, 96–97 bits conjectured; tiny-proof prove > 600 s) | none |

First joint milestone (≈ 3–4 weeks, light CPU): **a pinned PQ parameter set and exact wire size.**
* Hash: SHA-384.
* Extension degree.
* LDT: FRI vs WHIR.
* Queries per round from the M3 target.
* The fixed-point recursion height.

It goes/no-goes 300 KB before any large Lean investment (G1 now includes PQ).

### 11.8 Updated spikes and plan deltas

* **S3** becomes a joint calculator with the research branch, PQ and classical. It adds the fixed-point
  final-layer height and multiproof dedup.
* **S4** moves into research M2. It now targets PQ rbr knowledge soundness, not only the proximity gap.
* **S6** (recursion-node cost) runs for SHA-256, SHA-384 and SHA-512, using a prototype SHA-512-family table
  (D1-S shared).
* **S8** (GPU SHA throughput) measures SHA-256 **and** SHA-512/384 on an H200.
* **S9** (latency budget) gets a PQ variant.
* Phase 1 is unchanged. Phase 2 is re-targeted:
  * the classical real-time track (P-RT-1…4);
  * the PQ compression track, with the formal work led by the research branch and parameters from S3.
  * The two share the segment AIR, the GPU prover and the SHA-2 family tables.

### 11.9 Decisions for the user (PROPOSALS)

* **PQ-D1, security contract.** Failure ≤ 2⁻¹²⁸ against t = 2⁶⁴ quantum queries (assumed here), or "128-bit quantum
  attack cost" with t up to 2¹²⁸ (forces SHA-512 and ≈ 2× the query bits).
* **PQ-D2, hash.** Amend U-1 for the PQ track to **SHA-384** (or SHA-512) throughout the proof system, with
  "SHA-384 in circuits as a QRO" as the assumption. No 2 × SHA-256.
* **PQ-D3, PQ scope.** PQ for the real-time validation proof (latency ≈ 2× worse, envelope ≈ half), or a PQ wrap
  as an asynchronous archival layer over classical real-time proofs.
* **PQ-D4, size target.** Accept ≈ 0.5–1 MB as the PQ-proven target, with 300 KB as a stretch goal that depends
  on WHIR-class work.
* **PQ-D5, field.** Stay on BabyBear with a degree-10/12 extension, or evaluate a larger-2-adicity field
  (Goldilocks) for the PQ track. That is a protocol-wide change.
* Earlier open items stand: P-RT-1…4, P-D1-2 interim, and access to mainnet data and an H200.

Sources for §11:
* Measure-and-Reprogram 2.0, Don–Fehr–Majenz: <https://eprint.iacr.org/2020/282>
* On Soundness Notions for IOPs: <https://eprint.iacr.org/2023/1256>
* Chiesa–Manohar–Spooner, *Succinct arguments in the QROM*: <https://eprint.iacr.org/2019/834>
* Zhandry, quantum collision bounds: <https://arxiv.org/abs/1312.1027>
* How to Record Quantum Queries: <https://eprint.iacr.org/2018/276>
* Concrete Security of Non-interactive FRI: <https://eprint.iacr.org/2024/1161>
* WHIR: <https://eprint.iacr.org/2024/1586>
* hashcat benchmark gist: <https://gist.github.com/Chick3nman/e4fcee00cb6d82874dace72106d73fef>

The constants of the cited theorems were not re-derived here.
