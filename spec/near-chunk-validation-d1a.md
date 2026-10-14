# `near/pv86/chunk-validation/v0`, domain **D1a** — D1 with the D0a amendments and a transaction bound

Status: **unsigned draft**, 2026-10-14 (lane `v3-d1a-spec`). Additive successor of domain D1
(`spec/near-chunk-validation-d1.md`, `NearSpecV3.RelD1`), which is **not modified**, in the way
D0a (`spec/near-chunk-validation-v0a.md`, `NearSpecV3.RelD0a`) is the bounded successor of D0.
Design: `docs/zk-formal/V3-D1-DESIGN.md` §3. User decisions P-D1-1 … P-D1-7 of 2026-10-14
(recorded there, §0): a bounded tier `RelD1a` in new files plus `Tier.d1a` (P-D1-1); signatures
verified natively by a verifier (P-D1-2); `NT0 = 4,096` transactions (P-D1-3); A7 bound `B0 =
2,000,000` as D0a (P-D1-4); proof cap = near-chunk-v3's 64 MiB (P-D1-5); `prepD1` candidate-side
(P-D1-6); function-call and gas-key validity classes stay in scope (P-D1-7).

## 1. The relation

```
RelD1a(B, W, Dp, N)(cb, w) := RelD1(cb, w) ∧ A1(cb) ∧ A2ᴰ¹(cb, w) ∧ Canon0fᴰ¹(cb, w)
                              ∧ unfoldBytesᴰ¹(cb, w) ≤ B ∧ A8(cb) ∧ chachaWordsᴰ¹(cb, w) ≤ W
                              ∧ (∀ used source proof e, |e.path| ≤ Dp) ∧ A12(cb)
                              ∧ |w.transactions| ≤ N
```

Challenge instance: `B = B0 = 2,000,000`, `W = W0 = 770,000`, `Dp = Dp0 = 32` (the D0a values,
unchanged) and `N = NT0 = 4,096` (T1, §2.4).

Lean: `NearSpecV3.ChunkValidationD1a` (`RelD1a B cb w (W := W0) (Dp := Dp0) (N := NT0)`, `decodeWD1`,
`usedProofsD1`, `a2D1`, `reads0fD1`, `canon0fD1`, `appliedReceiptsD1`, `triesD1`, `unfoldBytesD1`,
`a7D1`, `schedInsD1`, `chachaWordsD1`, `a9D1`, `maxPathDepthD1`, `a10D1`, `txCountD1`, `t1`, `NT0`;
the claim-only `a1`, `a8`, `a12` and `B0`, `W0`, `Dp0`, `unfoldedBytesT`, `canonical0f`, `schedWords`
are the D0a definitions of `NearSpecV3.ChunkValidationV0a`, used unchanged). Executable verdict
`checkD1a B cb w`. **Proved** (no `sorry`, axioms `propext`, `Quot.sound` only):

* `relD1a_iff : RelD1a B cb w W Dp N ↔ checkD1a B cb w W Dp N = .ok ()`;
* `relD1a_relD1 : RelD1a B cb w W Dp N → RelD1 cb w` (for all bounds): **a pure restriction**,
  every D1a proof is a D1 proof of the same claim, and no soundness statement mentions the bounds;
* `relD1a_mono_all` (monotone in each of `B`, `W`, `Dp`, `N`), `relD1a_mono` (in `B`);
* `inD1a_iff`, `relD1a_iff_inD1a : RelD1a ↔ RelD1 ∧ InD1a`, `relD1a_iff_in` (challenge bounds).

`NearSpecV3.ChallengeD1a`: `challengeSpecD1a` (`Rel c w = RelD1a B0 c.encode w`, same claim type
and codec as D0/D1), `WfClaim.relD1a_rel`, `WfClaim.domainD1a_domain`, `challengeParamsD1a`
(`maxProofBytes = maxProofBytesV3` = 64 MiB, P-D1-5). The claim and witness formats are unchanged
(`spec/claim-v3.md`).

**Empty main pre-state.** As in D0a (v0a §1, user decision 2026-10-13): a claim whose B2
own-slot `prev_state_root` is `0^32` is **not** in `RelD1` (`checkD1` builds the same
`partialTrie w.main.values prev_state_root [BufferedReceiptIndices]`, where the zero root is an
unrevealed `.hash`, so the read fails: `invalid: MissingTrieValue (BufferedReceiptIndices)`),
hence not in `RelD1a`. Existing Lean semantics, no change. The D1a Python checker rejects it as
Lean does (the unmodified D1 checker treats the zero root as an empty trie); mutant family
`w.empty_pre_state` (§3).

## 2. Amendments (out-of-domain conditions added to D1's table)

The D0a predicates decode the witness with the D0 decoder `decodeStateWitness`, which fails on
every witness carrying a transaction (`nTransactions` must be 0), and A7 / A9 rebuild the **D0**
run. So each witness- or run-reading amendment is restated over `decodeStateWitnessD1` and the
**D1** run (`applyNewChunkD1`); the claim-only ones are reused verbatim.

| id | D1a condition (Lean) | restatement for D1 | why (prover completeness / size) | honest chains |
|---|---|---|---|---|
| `c.gas_limit` (A1) | `a1 cb` | identical (claim only) | bounds applied receipts (`n ≤ 4,481`) and the refund body; with the transactions' gas counted in `e.compute`, local + incoming receipts stay `≤ 4,481` whenever any receipt is applied, so `rcptV3`, `sortV3`, `srcpV3` and both SHA instances keep their D0a heights (design §3.2) | genesis value forever (v0a §2.1); mainnet 1000 Tgas: in |
| `w.proof_routing` (A2) | `a2D1 cb w` | `usedProofsD1` over the D1 witness's entries | no receipt is Merkle-hashed but filtered out (proof size) | nearcore invariant (v0a §2.2): transactions do not change how source proofs are built |
| `e.sched_canonical` (Canon0f) | `canon0fD1 cb w` | `reads0fD1`: `0x0f` of the D1 witness's main / implicit pre-states | the in-AIR scheduler decodes exactly `n²` ordered links | nearcore invariant (v0a §2.3): only `run_bandwidth_scheduler` writes `0x0f`; transactions never do |
| `w.unfolded` (A7) | `a7D1 B cb w` | `unfoldBytesD1` over `triesD1` (§2.1) | the AIR hashes every revealed node occurrence, incl. the transaction keys' paths and the transaction writes | measured headroom ≥ 150× (§3) |
| `c.bw_requests` (A8) | `a8 cb` | identical (claim only) | bounds the requests the in-AIR scheduler converts | nearcore invariant (v0a §2.3a) |
| `e.chacha_words` (A9) | `a9D1 W cb w` | `chachaWordsD1` over `schedInsD1` (the D1 run's pre tries) | bounds the in-AIR ChaCha lane (`< 2²²` rows) | `applyNewChunkD1` runs `schedStep` exactly as D0; measured max 0 on D1 corpora (§3) |
| `w.path_depth` (A10) | `a10D1 Dp cb w` | `usedProofsD1` | bounds `srcpV3` (`≤ 2²²` rows) | nearcore emits `⌈log₂ #shards⌉ ≤ 6` |
| `c.layout_wf` (A12) | `a12 cb` | identical (claim only) | bounded own-shard routing intervals | nearcore type invariant (v0a §2.9) |
| **`w.tx_count` (T1, new)** | `t1 N w` | — | bounds the verifier's native per-transaction work and the in-AIR transaction tables (§2.4) | honest producers stop at ≈ 2,241 transfers |

Order of the executable checks (`checkD1a`, reason strings as `checkD0a` plus T1): `checkD1`, then
A1, A2, Canon0f, A7, A8, A9, A10, A12, T1, each failing as `out of domain (<id>): …`.

### 2.1 A7ᴰ¹ `w.unfolded`: which tries

`unfoldBytesD1 cb w = Σ_τ unfoldedBytesT pre_τ + unfoldedBytesT post_τ` exactly as v0a §2.4, with
the transitions of the D1 run (`triesD1`, mirroring `checkD1` step for step):

* **main pre trie**: `partialTrie w.main.values prev_state_root (mainKeys receipts bshards ++
  txKeys w.txs)` — the very trie `checkD1` builds. `txKeys` lists the signer account
  (`[0] ‖ signer`) and the access key (`[2] ‖ signer ‖ [2] ‖ [0] ‖ pk`) of **every** transaction of
  the witness, whether or not the run reads it (a duplicate, an expired transaction or one with a
  bad signature is never read, but its keys are in the partial trie and revealed as far as the
  witness holds the nodes). This counts at least what an AIR that walks only the candidates'
  keys hashes, so the bound still bounds the tables; and it keeps A7 a function of the trie the
  relation itself builds (as in D0a).
* **main post trie**: the native trie `applyNewChunkD1` returns: the scheduler write, the
  transaction writes (signer amount, 9-byte full-access key with the new nonce), the local
  receipts' credits, then the incoming receipts.
* **implicit transitions**: as D0 (keys `DelayedReceiptIndices`, `0x0f`).

`B1 = B0 = 2,000,000` (P-D1-4): no new SHA rows. Liveness (design §5.4, estimated): on
mainnet-sized tries ≈ 11 KB per transaction, so ≈ 150–250 transfers per chunk fit — chunks
above it are **out of D1a, unprovable there, never wrongly accepted**. Raising B1 is a separate
cost lever (a third SHA instance).

### 2.2 A2ᴰ¹, Canon0fᴰ¹, A10ᴰ¹: same predicates, D1 witness

Identical to `a2`, `canon0f`, `a10` with `decodeW` replaced by `decodeWD1` (`decodeWitnessFile`
then `decodeStateWitnessD1`). The used proofs, the `0x0f` reads and the path lengths depend
only on the claim walk and on the witness's `entries`, `main`, `implicit`, which have the same
meaning in both formats. The nearcore source checks of v0a §2.2, §2.3 carry over unchanged:
transactions add neither source proofs nor writes of `0x0f`.

### 2.3 A9ᴰ¹ `e.chacha_words`

`chachaWordsD1 = Σ_τ schedWords (schedInsD1 …)`: the scheduler inputs of each applied transition,
read from `triesD1`'s pre tries and the walk's block contexts (`applyNewChunkD1` calls
`schedStep prims ctx t` before any transaction, on the same pre trie; the RNG seed is B2's
`prev_hash`). `Scheduler.run_eq_mid` (D0a, proved) shows the counted RNG is the run's own.

### 2.4 T1 `w.tx_count` (new): definition, `NT0`, why, liveness

**Definition** (`t1 N w`): `decodeWD1 w = ok sw → |sw.txs| ≤ N` (`false` when the witness does not
decode; irrelevant, `RelD1` is false there). `sw.txs` is the witness's `transactions` list as
decoded, **duplicates and expired transactions included**. `new_transactions` is not bounded
(T2 of the design is not part of D1a, §2.5).

**Why.** A failed transaction burns no gas and changes no state, so neither the chunk gas
limit, A1, nor `e.compute` bounds how many transactions a chunk carries; only the 8 MiB witness
does (≈ 49,000 minimal transfers). A succinct prover must be complete on its domain, and with
native signatures (P-D1-2) the verifier does per-transaction native work (decoding, the
duplicate check, `Ed25519.verify` ≈ 3.4 ms compiled, `txCost`, outcome leaves): `NT0 × 3.4 ms ≈
14 s` of the 60 s verify budget. In-AIR, NT0 bounds the transaction table (`16 × (NT + local
credits) ≤ 2¹⁷` rows), the outcome-Merkle leaves (`NT + 4,481`) and the hint.

**`NT0 = 4,096`** (P-D1-3). Honest-chain impact: none expected. nearcore's chunk producer stops
adding transactions at `max_tx_gas` = 500 Tgas of transaction gas (`runtime_configs/68.yaml:50`,
`chain/chain/src/runtime/mod.rs:1683-1700`): ≤ ≈ 2,241 transfers at ≈ 223.18 Ggas each
(V3-D1-DESIGN §0, P-D1-3). More than NT0 entries need a producer that includes transactions it
did not validate (the adversarial producer of the `d1-mixed` class does this for a few
transactions per chunk; measured max 13, §3).

**Liveness.** T1 never makes a false statement provable; a chunk with more than NT0
transactions is out of D1a (unprovable in D1a, still a D1 statement).

### 2.5 Not in D1a (exclusions)

* **T2** `|new_transactions| ≤ NT` — only needed for a proof cap below ≈ 16 MiB; P-D1-5 keeps
  the 64 MiB cap of near-chunk-v3, so D1a does not bound `new_transactions` (their size is bounded
  by the 8 MiB witness).
* **T3** (in-AIR signature count) — not applicable: signatures are verified natively (P-D1-2).
  The relation contains no in-AIR obligation: `Ed25519.verify` is reached only inside `RelD1`
  (`Tx.valid`), a spec function a verifier may evaluate natively.
* **T4** FullAccess-only keys — **not adopted** (P-D1-7): function-call keys (with / without
  allowance) and gas keys stay inside D1a with their failure outcomes; an access key that does
  not decode stays a rejection (as in D1).
* No gas-price cap (the u128 token-overflow drop stays inside D1a).
* `prepD1` (the native preparation of a D1a verifier) is **not** part of the pinned spec
  (P-D1-6): it is candidate-side (zk-formal), proved against `RelD1a`.
* D0a ⊂ D1a is **tested, not proved** (as D0 ⊂ D1): every D0a positive is a D1 positive with no
  transactions, where `txKeys [] = []`, `processTxs ctx st [] = ok st` and every D1a predicate
  reduces to its D0a one.

## 3. Reference checkers, oracle and tests

* **Lean** `nearspec-v3-check-d1a` (`zk-formal` package, root `ZkFormal.V3.Tools.CheckD1a`, plain
  spec code: compiled `checkD1a`); flags `--bound`, `--words-bound`, `--depth-bound`,
  `--tx-bound`; reports `unfold`, `chacha_words`, `max_path_depth`, `tx_count`.
* **Python** `oracle/tools/spec_check_v3_d1a.py`: the D1 checker (`spec_check_v3_d1.py`,
  unmodified) with the D0a checker's recording trie and counting ChaCha RNG installed
  (`spec_check_v3_d0a.py`, unmodified), plus the amendment checks on the D1 witness; A7 adds every
  transaction's two keys to the recorded read keys of the main trie.
* **Oracle** `oracle/v3-d1a` (`near-arena-oracle-v3-d1a measure-case`): nearcore borsh decoding
  of the witness (T1: `ChunkStateWitness::transactions().len()`), nearcore `TrieKey`s for the D1
  main keys (D0 read keys + every transaction's `Account` / `AccessKey`), A7 on nearcore's
  `RawTrieNodeWithSize` (offline, post blobs from `oracle/tools/dump_a7_store_v3_d1a.py`), A10 from
  the `MerklePath`s. Generation stays with `oracle/v3-d1` (unmodified: its tree is pinned by the
  near-chunk-v3 draft's D1 generator specs).
* **Mutants** `oracle/tools/d1a_mutants_v3.py` (byte surgery restoring every hash the relation
  checks): `w.tx_count_at_bound` (exactly NT0 transactions, padding by duplicates: accept),
  `w.tx_count_over` (NT0 + 1: out of domain `w.tx_count`), `w.path_depth_at_bound` /
  `w.path_depth_over` (32 / 33 path items on a D1 witness), `w.empty_pre_state` (reject).
  Boundary sweep `oracle/tools/d1a_boundary_v3.py`: each in-domain case at its own A7 / A9 / A10 /
  T1 value accepts and at value − 1 is out of domain for that family, in Lean and Python.
* **Difftest** `oracle/tools/difftest_v3_d1a.py` (Lean vs Python, optional oracle measures);
  results: `docs/logs/v3-d1a-spec-2026-10.md`, `docs/e2e-results/v3-d1a/`.

## 4. Challenge wiring

* **near-chunk-v3, tier `D1a`** (prepared, not frozen): `NearSpecV3.Tier.d1a`,
  `RelTier .d1a = RelD1a B0`, `rel_mono` through `relD1a_relD1` (no new disjunct of `RelChunkV3`),
  coverage tier `D1a` with the D0 and D1 classes (`d0-quiet`, `d0-transfers`, `d0-missing`,
  `d1-transfers`, `d1-mixed`, `d1-receipts`), rank between D0 and D1. This edits
  `ChallengeChunkV3.lean` (in the draft's pinned tree) and the draft; it requires a re-freeze
  (`docs/logs/v3-d1a-spec-2026-10.md`, "Draft patch").
* **params.bin**: a near-chunk-v3 D1a candidate uses the challenge's domain id `D3a` (like D0a
  there); no new domain id. A standalone D1a challenge (`challengeParamsD1a`) would need domain
  id `"D1a"` (the scope-name suffix) with the D1 runtime-config digest — not added
  (`spec/tools/params_bin_v3.py` unchanged).
