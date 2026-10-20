# Gap analysis: an end-to-end 1 Pgas proof under 300 KB

Status: 2026-10-19, after the G2 gate passed and the D0a/D1 port experiments landed.
Companion artifacts: `tools/d1-pq-envelope/` (per-table envelope), `lane/pq-stream-commit`
`g2-gate/` (measured final), `lane/pq-state-port` (D0a port), `lane/pq-wasm-base` §14 (join
design), `lane/pq-d1-envelope` (D1 envelope).

## 0. Two different goals, usually conflated

Both are called "the target". They differ by 290× in workload and need different machinery.

| | **A. chunk at `G_α`** | **B. chunk at 1 Pgas** |
|---|---|---|
| gas | `2^22 · 822,756` = 3.451e12 (2^41.65) | 1e15 = **289.8×** A |
| status | the signed challenge's cap (`e.g_alpha`) | research definition only (`Scope.checkD3Peta`) |
| base cells [E] | 2.1–4.2 G (494–995/op × 4.19 M ops) | 0.6–1.2 **T** (D3A study §3) |
| segments at 2^28.25 cells | ~13 | **~1,880–3,760** |
| one proof? | no (W would be ~200) | no (W would be **35,000–71,000**; pin is 24) |
| needs | the join (G3) | the join **plus** segmentation/recursion beyond `G_α` |

The 300 KB proof size does **not** grow with workload — only the stacking height does. So B is not
"harder to keep small"; it is harder because it needs a 1,880–3,760-segment aggregation tree that has
never been built or measured, and because the sealed challenge excludes it (`e.g_alpha`).

**Recommendation:** finish A first. B is a second project, not a scale-up of A.

## 1. What is done and measured

| item | evidence |
|---|---|
| Recursion tail: 5-level G2 chain, FINAL **293,077 B**, V_d accept + forgery control | `pq-stream-commit/g2-gate/` (measured, 46 min, 17 GB) |
| Fast CPU prover: 147×, byte-identical; L1 over real base 152 s / 10 GB (was 190–230 GB est.) | `pq-cpu-prover` README §6 |
| D0a state tables on SWIRL: all 25, no stand-in, tamper 19/19, 1.02–1.60 MB | `pq-state-port` §1 |
| D1 envelope: 23/30 tables proven; per-table data cross-checked | `pq-d1-envelope`, `tools/d1-pq-envelope` |
| Direct-Wasm base: F1+div+locals+memory+globals+calls, Lean `wasm_base_sound` | `pq-wasm-base` §11–13 |
| Lean bridge ingredients for SWIRL⇒`HoldsP`, `multBoundP < p` kernel-checked | `pq-state-port` §2 |
| **Full** SWIRL⇒`HoldsP` (`holdsP_of_swirl`), D0a/D1 composition, vk⇔Lean difftest | `pq-state-port` §2.1 |
| D1 on PQ: all 30 tables, no stand-in, tamper 23/23 | `pq-state-port` §3 |
| TAPE canonical table + `tapeNet_canon`; TAPE root as a statement component | `pq-state-port` §2.2 |
| Wasm join: bus partition proved; interface + coverage statement fixed | `pq-state-port` §5 |

## 2. What is missing, ordered by what blocks A

### 2.1 HOST chip and buses (blocking)
Design only (`pq-wasm-base` §14.2). Needed: `check` support for import calls, the HOST chip,
`HOSTQ`/`HOSTR`/`HOSTB` buses, the register space, the `g_after` budget register, and the spec-side
`callHost` simulation given a response oracle. Without it the Wasm proof cannot represent a run that
makes any host call — and essentially every real contract does.

### 2.2 Ed25519 / SHA-512 in-circuit (blocking, weeks)
The classical D1 verifier runs `prepD1` natively (~3.6 ms/signature, ~15 s at 4,096 tx). For a
succinct final verifier this must be a `sigV3` chip (or a separate sig proof). Nothing on the PQ
stack verifies a signature today.

### 2.3 The join (blocking, 15–25 agent-days [E])
Wasm proof + state proof over shared buses (`HOSTQ`/`HOSTR`/`HOSTB`), plus `code_root`/`func_root`/
`data_root` = the state side's code hash. Requires the `runCall` fold over the D1 extraction and
`wasm_base_sound` (D3α-style). Neither side's theorem covers the joined system.

*Bus partition and the interface are now fixed* (`lane/pq-state-port`): classical buses `< 128`
(kernel-proved) vs Wasm `0–6`, so `+128` separates them and 200/201/202 are the new host buses
(`Join.lean`, `JOIN-INTERFACE.md`).  The coverage statement is `JoinFold.lean` (`HostAnswer`,
`HostResp`, `WasmRunStmt`, `JoinStmt`, `join_additive`).  Still missing: the HOST chip itself.

### 2.4 The remaining D1 tables on PQ — **done**
All 30 tables now, with **no `EXT` stand-in** (`lane/pq-state-port`, `4cb4a5f88`): the natural-height
re-cut handles the six fixed-2^22 renders, 4.47 M cells, 1,289,274 B, prove 20.3 s, tamper 23/23,
V_d statement check OK.  The `EXT` stand-in described here was the envelope demo's, not the port's.
The tamper suite also documents one honest case: `rid` is all-zero padding on the fixtures, so its
payload is legitimately unconstrained (multiplicity 0); the suite reports it as skipped rather than
claiming a vacuous rejection.

### 2.5 Statement plumbing (medium, enumerated)
* **TAPE**: the public-message table's cached commitment must be carried up through every NV level
  to V_d (M2). *Lean side done* (`lane/pq-state-port`: `tapeCanon`/`tapeNet_canon` —
  `HoldsP` from SWIRL is proved, and the canonical TAPE's net-multiplicity identity is proved, so
  `VdChecks.tape` is discharged under commitment binding). The **NV passthrough** of the cached
  root (Rust, across L1…FINAL) is the remaining part.
* **`max_interaction_count` 2^28 → 2^30**: D1's N = 2^29.59. Two LogUp bits. D0a needs it too (M8).
  *Done in the demo driver* (`1 << 30` in `pq-state-port`), not yet in the production shape.
* **Per-table height cap** (`log_height ≤ maxLog_t`) enforced in vk/NV/V_d (M4). *Check done in the
  demo driver*; the vk/NV/V_d enforcement is still open.
* ~~**`holdsP_of_swirl`**: the final list-sum aggregation of the Lean bridge.~~ **Done**
  (`lane/pq-state-port` `Bridge.lean`, `426b73deb`): `holdsP_of_swirl` is proved with no `sorry`,
  and `pq_d0a_good`/`pq_d0a_rel`/`pq_d1_rel` compose it with `extractV3`/`ExtractD1Stmt`. This
  entry was stale when written.

### 2.6 Coverage theorem (medium)
`wasm_base_sound` proves execution. There is no theorem from (Wasm proof ∧ state proof) to the chunk
relation, and `ChunkStmtAir` has no Lean refinement. G4 in `pq-e2e-slice`.

*Shape fixed*: `JoinFold.JoinStmt` states it — `RelD1a` is preserved when every `FunctionCall`
action is backed by a `WasmRunStmt` whose host answers are the state tables'.  `join_additive`
records that the join only *requires* the Wasm backing and does not change the state relation.
The proof needs the HOST chip and the `d3Hooks`/`runCall` correspondence.

## 3. What is missing for B (1 Pgas) beyond A

1. **Segmentation + recursion over segments.** ~1,880–3,760 segments at `2^28.25` cells each; the
   aggregation tree (`build_l1_linked` k-to-1, design G) has been designed and partly prototyped
   (N1 proofs, 2-proof node debug) but never at that many leaves.
2. **The per-segment statement.** Each segment needs its own boundary state commitment and a
   cross-segment bus balance; `Segment.lean` has the fold, but not on the PQ stack.
3. **A 290× cost measurement.** No AIR has been run above `G_α`. The 12–25 h / 2–7 TB figures are
   extrapolations from the D3A study; with the 147× prover they are still hours and tens of GB per
   segment, and the tree multiplies the sequential depth.
4. **A decision** to reopen the gas cap, which the signed challenge explicitly excludes.

## 4. The single most useful next experiment

Not another model. **Prove one real D1 state shard and one real Wasm call, then join them on one
bus.** Concretely:

1. Pick the `storage_write` host call as the only bridge. It is the highest-gas call with a
   *single-write* state side. **Correction (verified 2026-10-19):** the D1 tables do **not** cover
   contract storage. `RelD1` is transfer-only (`TxD1.lean:97` rejects any action that is not
   `Transfer`), and `RuntimeD1.txKeys` walks only `accountKeyPath` and `keyAccessKey` — never
   `TrieKey::ContractData`. No AIR table references `ContractData`. So the state half of a
   `storage_write` is **new work** (a `ContractData` key prefix in `walkV3`/`kibV3` plus the
   D3 `RealStore` overlay), not something the port inherits. That makes the join a
   **D3-join**, not a D1-join, and it should be priced accordingly.
2. Prove the Wasm side with one `call` of `storage_write` (needs 2.1), and the state side with the
   trie tables (D0a port already works).
3. Check the joint `HOSTQ`/`HOSTR`/`HOSTB` balance over the two proofs.
4. Only then measure size and time.

That one experiment decides whether the join is 15 agent-days or a rewrite, and it does not require
Ed25519 (no signature if the transaction is a system receipt or the witness is supplied).

## 5. Honest sizing

| milestone | work | confidence |
|---|---|---|
| D1's 7 tables on PQ + natural heights | 3–5 days | high |
| statement plumbing (TAPE, interaction cap, height caps) | 3–5 days | high |
| `holdsP_of_swirl` composition | 4–6 days | high |
| HOST chip + buses + spec simulation | 10–15 days | medium |
| Ed25519/SHA-512 AIR | weeks | medium |
| the join + coverage theorem | 15–25 days | low |
| **A: `G_α` chunk, <300 KB, end to end** | **~2–3 months** | medium |
| segmentation/recursion to 1 Pgas + a 290× measurement | unknown, research | low |

The 293,077 B number is real, but it is the **recursion tail only**. Stating "1 Pgas under 300 KB"
as achieved would be false by the join (2.1–2.3) and by 290× of unmeasured scale (B).
