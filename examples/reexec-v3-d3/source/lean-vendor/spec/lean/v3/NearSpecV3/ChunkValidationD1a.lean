import NearSpecV3.ChunkValidationV0a
import NearSpecV3.ChunkValidationD1

/-!
# `NearSpecV3.ChunkValidationD1a` — `RelD1a`: D1 with the D0a amendments and a transaction bound

Additive successor of `NearSpecV3.ChunkValidationD1` (`RelD1`, not modified), as
`ChunkValidationV0a` is of `ChunkValidationV0` (spec/near-chunk-validation-d1a.md;
docs/zk-formal/V3-D1-DESIGN.md §3; user decisions P-D1-1 … P-D1-7 of 2026-10-14):

  `RelD1a B cb w W Dp N := RelD1 cb w ∧ A1 cb ∧ A2ᴰ¹ cb w ∧ Canon0fᴰ¹ cb w ∧ A7ᴰ¹ B cb w ∧ A8 cb ∧
    A9ᴰ¹ W cb w ∧ A10ᴰ¹ Dp cb w ∧ A12 cb ∧ T1 N w`
  (`W`, `Dp`, `N` default to `W0 = 770,000`, `Dp0 = 32`, `NT0 = 4,096`; the challenge instance
  of `B` is `B0 = 2,000,000`, P-D1-4).

A pure restriction of `RelD1` (`relD1a_relD1`). Each D0a amendment is restated over the D1
witness decoder (`decodeStateWitnessD1`; the D0a predicates decode with the D0 decoder, which
fails on every witness that carries a transaction) and, where it reads the run, over the D1 run
(`applyNewChunkD1`). The claim-only amendments A1, A8, A12 are the D0a functions themselves.

* **A1** (`c.gas_limit`), **A8** (`c.bw_requests`), **A12** (`c.layout_wf`): `a1`, `a8`, `a12`
  of `ChunkValidationV0a`, unchanged (claim only).
* **A2ᴰ¹** (`w.proof_routing`), **Canon0fᴰ¹** (`e.sched_canonical`), **A10ᴰ¹** (`w.path_depth`):
  the D0a predicates with the witness decoded as a D1 witness (`a2D1`, `canon0fD1`, `a10D1`).
* **A7ᴰ¹** (`w.unfolded`): `unfoldBytesD1` = Σ over the applied transitions of the unfolded pre
  trie plus the unfolded native post trie, where the main pre trie is exactly the one `checkD1`
  builds (keys `mainKeys receipts bshards ++ txKeys w.txs`: the signer account and access key
  of **every** transaction of the witness) and the main post trie is the one `applyNewChunkD1`
  returns (the transaction writes, local receipts, incoming receipts and scheduler write).
* **A9ᴰ¹** (`e.chacha_words`): `chachaWordsD1`, the ChaCha20 words of the scheduler runs of the
  D1 run (`applyNewChunkD1` runs `schedStep` exactly as the D0 run does; the inputs are the
  `0x0f` value of the D1 pre tries).
* **T1** (`w.tx_count`, P-D1-3): the witness's `transactions` list has at most `N` entries
  (`NT0 = 4,096`), duplicates and expired transactions included. Bounds the native per-transaction
  work of a verifier (decode, `Ed25519.verify`, outcome leaves; P-D1-2) and the in-AIR transaction
  tables; failed transactions burn no gas, so nothing else bounds the count (≈ 49,000 fit an
  8 MiB witness).

`checkD1a B` is the executable verdict (`.ok ()` ⇔ `RelD1a B`, by `relD1a_iff`). Nothing here
involves the signature check: `Ed25519.verify` is reached only inside `RelD1` (`Tx.valid`), so
the relation leaves the verifier free to evaluate it natively (P-D1-2).
-/

namespace NearSpecV3

open NearSpec

/-- The D1 witness of a witness file (`checkD1`'s decoder, without its size gates). -/
def decodeWD1 (w : Bytes) : Except String StateWitnessD1 := do
  let (sw, _) ← decodeWitnessFile w
  decodeStateWitnessD1 sw

/-- The used source proofs of a D1 witness, in walk order (as `usedProofs`). -/
def usedProofsD1 (k : WalkD0) (w : StateWitnessD1) : List ProofEntry :=
  k.sourceBlks.flatMap fun S => S.slots.filterMap fun (s, ci) =>
    if s.heightIncluded == S.hdr.height then lookupLast (chunkHash s.inner ci.encodedMerkleRoot) w.entries
    else none

/-- A2ᴰ¹ (`w.proof_routing`). -/
def a2D1 (cb w : Bytes) : Bool :=
  match walkD0 cb, decodeWD1 w with
  | .ok k, .ok sw => (usedProofsD1 k sw).all fun e => e.receipts.all fun r => k.L.shardOf r.receiverId == k.H.shardId
  | _, _ => false

/-- The `0x0f` values read by the D1 run: main pre-state, then each implicit pre-state. -/
def reads0fD1 (k : WalkD0) (w : StateWitnessD1) : List (Option Bytes) :=
  let find (vals : List Bytes) (root : Bytes) : Option Bytes :=
    ((partialTrie vals root [keyBwState]).find keyBwState).getD none
  let roots := w.main.postStateRoot :: w.implicit.map (·.postStateRoot)
  find w.main.values k.slotB2.prevStateRoot :: (w.implicit.zip roots).map fun (T, r) => find T.values r

/-- Canon0fᴰ¹ (`e.sched_canonical`). -/
def canon0fD1 (cb w : Bytes) : Bool :=
  match walkD0 cb, decodeWD1 w with
  | .ok k, .ok sw => (reads0fD1 k sw).all (canonical0f k.L)
  | _, _ => false

/-- Applied (incoming) receipts as `checkD1` builds them (lenient: missing proofs are skipped). -/
def appliedReceiptsD1 (k : WalkD0) (w : StateWitnessD1) : List Receipt := Id.run do
  let mut receipts : List Receipt := []
  for S in k.sourceBlks do
    let proofs := S.slots.filterMap fun (s, ci) =>
      if s.heightIncluded == S.hdr.height then lookupLast (chunkHash s.inner ci.encodedMerkleRoot) w.entries
      else none
    let shuffled := (shuffleWithSeed proofs S.hdr.prevHash).getD proofs
    receipts := receipts ++
      (shuffled.map fun e => e.receipts.filter fun r => k.L.shardOf r.receiverId == k.H.shardId).flatten
  return receipts

/-- `(pre_τ, post_τ)` for every applied transition, as `checkD1` builds and runs them: the main
pre trie over `mainKeys … ++ txKeys w.txs`, the main post trie returned by `applyNewChunkD1`
(with the claim's validity flags), then each implicit transition as in D0. -/
def triesD1 (cb wb : Bytes) : Except String (List (PTrie × PTrie)) := do
  let k ← walkD0 cb
  let w ← decodeWD1 wb
  let B2 ← match k.blks[k.b2i]? with | some b => pure b | none => throw "walk"
  let prevB2 ← match k.blks[k.b2i + 1]? with | some b => pure b | none => throw "walk"
  let receipts := appliedReceiptsD1 k w
  let ctxB2 := blockCtx k.L k.H.shardId k.slotB2.gasLimit B2 prevB2.hdr.nextGasPrice
  let t0 := partialTrie w.main.values k.slotB2.prevStateRoot [keyBufferedIdx]
  let bshards ← match t0.find keyBufferedIdx with
    | some v => bufferedShards v | none => throw "missing"
  let tMain := partialTrie w.main.values k.slotB2.prevStateRoot (mainKeys receipts bshards ++ txKeys w.txs)
  let out ← applyNewChunkD1 prims ctxB2 tMain receipts (w.txs.zip (k.c.txValid.map (· != 0)))
  let mut acc : List (PTrie × PTrie) := [(tMain, out.trie)]
  let mut root := out.trie.hashOf
  for (M, T) in k.implicitBlks.zip w.implicit do
    let ctxM := blockCtx k.L k.H.shardId k.slotB2.gasLimit M M.hdr.nextGasPrice
    let ks := [keyDelayedIdx, keyBwState]
    let tM := partialTrie T.values root ks
    let tM' ← applyMissingChunk prims ctxM tM
    acc := acc ++ [(tM, tM')]
    root := tM'.hashOf
  pure acc

/-- A7ᴰ¹ measure: unfolded pre tries + unfolded native post tries of the D1 run (0 if the run
fails; then `RelD1` is false anyway). -/
def unfoldBytesD1 (cb w : Bytes) : Nat :=
  match triesD1 cb w with
  | .ok l => (l.map fun (pre, post) => unfoldedBytesT pre + unfoldedBytesT post).sum
  | .error _ => 0

/-- A7ᴰ¹ (`w.unfolded`). -/
def a7D1 (B : Nat) (cb w : Bytes) : Bool := decide (unfoldBytesD1 cb w ≤ B)

/-- The scheduler inputs of every applied transition of the D1 run (as `schedInsD0`, on
`triesD1`'s pre tries). -/
def schedInsD1 (cb wb : Bytes) : Except String (List SchedIn) := do
  let k ← walkD0 cb
  let w ← decodeWD1 wb
  let B2 ← match k.blks[k.b2i]? with | some b => pure b | none => throw "walk"
  let prevB2 ← match k.blks[k.b2i + 1]? with | some b => pure b | none => throw "walk"
  let ts ← triesD1 cb wb
  let ctxs := blockCtx k.L k.H.shardId k.slotB2.gasLimit B2 prevB2.hdr.nextGasPrice ::
    (k.implicitBlks.zip w.implicit).map fun (M, _) =>
      blockCtx k.L k.H.shardId k.slotB2.gasLimit M M.hdr.nextGasPrice
  pure ((ctxs.zip ts).map fun (ctx, pre, _) =>
    ⟨ctx.layout.shardIds, ctx.own, (pre.find keyBwState).getD none, ctx.statuses, ctx.requests,
     ctx.prevBlockHash⟩)

/-- Σ ChaCha20 words drawn by all scheduler runs of the D1 run. -/
def chachaWordsD1 (cb w : Bytes) : Nat :=
  match schedInsD1 cb w with
  | .ok l => (l.map schedWords).sum
  | .error _ => 0

/-- A9ᴰ¹ (`e.chacha_words`). -/
def a9D1 (W : Nat) (cb w : Bytes) : Bool := decide (chachaWordsD1 cb w ≤ W)

/-- Longest Merkle path of a used source proof of a D1 witness (`0` if none / undecodable). -/
def maxPathDepthD1 (cb w : Bytes) : Nat :=
  match walkD0 cb, decodeWD1 w with
  | .ok k, .ok sw => ((usedProofsD1 k sw).map fun e => e.proof.path.length).foldr max 0
  | _, _ => 0

/-- A10ᴰ¹ (`w.path_depth`). -/
def a10D1 (Dp : Nat) (cb w : Bytes) : Bool :=
  match walkD0 cb, decodeWD1 w with
  | .ok k, .ok sw => (usedProofsD1 k sw).all fun e => decide (e.proof.path.length ≤ Dp)
  | _, _ => false

/-! ## T1 `w.tx_count`: the transactions of the witness

Failed transactions burn no gas, so neither the gas limit nor A1 bounds how many a chunk
carries; only the 8 MiB witness does (≈ 49,000). `NT0 = 4,096` (user decision P-D1-3,
2026-10-14): above the honest-producer maximum of ≈ 2,241 successful transfers
(`max_tx_gas = 500 Tgas` / 223.18 Ggas per transfer) and of `combined_transactions_size_limit`
4,194,304 B worth of minimal transfers (≈ 18,000 · 230 B is above it, but every honest producer
stops at `max_tx_gas` first, since each included transaction is a candidate it charges). -/

/-- The number of transactions of the witness (`0` if it does not decode). -/
def txCountD1 (w : Bytes) : Nat :=
  match decodeWD1 w with
  | .ok sw => sw.txs.length
  | .error _ => 0

/-- T1 (`w.tx_count`). -/
def t1 (N : Nat) (w : Bytes) : Bool :=
  match decodeWD1 w with
  | .ok sw => decide (sw.txs.length ≤ N)
  | .error _ => false

/-- T1 bound of the challenge instance (user decision P-D1-3, 2026-10-14). -/
def NT0 : Nat := 4096

/-- **The D1a relation**, with the unfolded-size bound `B` a parameter (the challenge instance is
`B0`, P-D1-4) and the A9 / A10 / T1 bounds defaulting to `W0`, `Dp0`, `NT0`. -/
def RelD1a (B : Nat) (cb w : Bytes) (W : Nat := W0) (Dp : Nat := Dp0) (N : Nat := NT0) : Prop :=
  RelD1 cb w ∧ a1 cb = true ∧ a2D1 cb w = true ∧ canon0fD1 cb w = true ∧ a7D1 B cb w = true ∧
    a8 cb = true ∧ a9D1 W cb w = true ∧ a10D1 Dp cb w = true ∧ a12 cb = true ∧ t1 N w = true

instance (B : Nat) (cb w : Bytes) (W Dp N : Nat) : Decidable (RelD1a B cb w W Dp N) := by
  unfold RelD1a; infer_instance

/-- Executable verdict: `checkD1`, then the amendments (each reported as out of domain), in the
order A1, A2, Canon0f, A7, A8, A9, A10, A12 (as `checkD0a`), T1. -/
def checkD1a (B : Nat) (cb w : Bytes) (W : Nat := W0) (Dp : Nat := Dp0) (N : Nat := NT0) :
    Except String Unit := do
  checkD1 cb w
  check (a1 cb) "out of domain (c.gas_limit): chunk gas_limit above 10^15"
  check (a2D1 cb w) "out of domain (w.proof_routing): a used receipt proof holds a receipt routed to another shard"
  check (canon0fD1 cb w) "out of domain (e.sched_canonical): 0x0f value is not the layout's canonical link list"
  check (a7D1 B cb w) "out of domain (w.unfolded): unfolded trie bytes above the bound"
  check (a8 cb) "out of domain (c.bw_requests): a chunk's bandwidth requests repeat a to_shard"
  check (a9D1 W cb w) "out of domain (e.chacha_words): scheduler runs draw more ChaCha20 words than the bound"
  check (a10D1 Dp cb w) "out of domain (w.path_depth): a used receipt proof's Merkle path is longer than the bound"
  check (a12 cb) "out of domain (c.layout_wf): the shard layout does not have one boundary fewer than shard ids"
  check (t1 N w) "out of domain (w.tx_count): more transactions than the bound"

private theorem check_ok_iff (b : Bool) (m : String) : check b m = .ok () ↔ b = true := by
  cases b <;> simp [check]

private theorem except_bind_ok_iff (x : Except String Unit) (f : Unit → Except String Unit) :
    (x >>= f) = .ok () ↔ x = .ok () ∧ f () = .ok () := by
  cases x with
  | error e => simp [bind, Except.bind]
  | ok u => cases u; simp [bind, Except.bind]

theorem relD1a_iff (B : Nat) (cb w : Bytes) (W : Nat := W0) (Dp : Nat := Dp0) (N : Nat := NT0) :
    RelD1a B cb w W Dp N ↔ checkD1a B cb w W Dp N = .ok () := by
  unfold RelD1a RelD1 acceptsD1 checkD1a
  simp only [except_bind_ok_iff, check_ok_iff]
  cases checkD1 cb w with
  | error e => simp
  | ok u => cases u; simp

/-- The D1a domain conditions (Bool form). -/
def inD1a (B : Nat) (cb w : Bytes) (W : Nat := W0) (Dp : Nat := Dp0) (N : Nat := NT0) : Bool :=
  a1 cb && a2D1 cb w && canon0fD1 cb w && a7D1 B cb w && a8 cb && a9D1 W cb w && a10D1 Dp cb w &&
    a12 cb && t1 N w

/-- The D1a domain conditions. -/
def InD1a (B : Nat) (cb w : Bytes) (W : Nat := W0) (Dp : Nat := Dp0) (N : Nat := NT0) : Prop :=
  a1 cb = true ∧ a2D1 cb w = true ∧ canon0fD1 cb w = true ∧ a7D1 B cb w = true ∧ a8 cb = true ∧
    a9D1 W cb w = true ∧ a10D1 Dp cb w = true ∧ a12 cb = true ∧ t1 N w = true

/-- The D1a domain at the challenge bounds `B0`, `W0`, `Dp0`, `NT0`. -/
def InD1a0 (cb w : Bytes) : Prop := InD1a B0 cb w

theorem inD1a_iff (B : Nat) (cb w : Bytes) (W : Nat := W0) (Dp : Nat := Dp0) (N : Nat := NT0) :
    inD1a B cb w W Dp N = true ↔ InD1a B cb w W Dp N := by
  unfold inD1a InD1a
  simp only [Bool.and_eq_true, and_assoc]

instance (B : Nat) (cb w : Bytes) (W Dp N : Nat) : Decidable (InD1a B cb w W Dp N) :=
  decidable_of_iff _ (inD1a_iff B cb w W Dp N)

instance (cb w : Bytes) : Decidable (InD1a0 cb w) := by unfold InD1a0; infer_instance

/-- `RelD1a B` is `RelD1` restricted to the domain `InD1a B`. -/
theorem relD1a_iff_inD1a (B : Nat) (cb w : Bytes) (W : Nat := W0) (Dp : Nat := Dp0)
    (N : Nat := NT0) : RelD1a B cb w W Dp N ↔ RelD1 cb w ∧ InD1a B cb w W Dp N :=
  Iff.rfl

/-- Same at the challenge bounds. -/
theorem relD1a_iff_in (cb w : Bytes) : RelD1a B0 cb w ↔ RelD1 cb w ∧ InD1a0 cb w := Iff.rfl

/-- Soundness direction: every D1a witness is a D1 witness (for all bounds). -/
theorem relD1a_relD1 {B : Nat} {cb w : Bytes} {W Dp N : Nat} (h : RelD1a B cb w W Dp N) :
    RelD1 cb w := h.1

/-- The bounds are monotone (each of `B`, `W`, `Dp`, `N`). -/
theorem relD1a_mono_all {B B' W W' Dp Dp' N N' : Nat} (hB : B ≤ B') (hW : W ≤ W') (hD : Dp ≤ Dp')
    (hN : N ≤ N') {cb w : Bytes} (h : RelD1a B cb w W Dp N) : RelD1a B' cb w W' Dp' N' := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  refine ⟨h0, h1, h2, h3, ?_, h5, ?_, ?_, h8, ?_⟩
  · unfold a7D1 at *
    simp only [decide_eq_true_eq] at *
    omega
  · unfold a9D1 at *
    simp only [decide_eq_true_eq] at *
    omega
  · unfold a10D1 at *
    revert h7
    split
    · simp only [List.all_eq_true, decide_eq_true_eq]
      exact fun h e he => Nat.le_trans (h e he) hD
    · exact id
  · unfold t1 at *
    revert h9
    split
    · simp only [decide_eq_true_eq]
      exact fun h => Nat.le_trans h hN
    · exact id

/-- The A7 bound is monotone (at fixed `W`, `Dp`, `N`). -/
theorem relD1a_mono {B B' : Nat} (hB : B ≤ B') {cb w : Bytes} {W Dp N : Nat}
    (h : RelD1a B cb w W Dp N) : RelD1a B' cb w W Dp N :=
  relD1a_mono_all hB (Nat.le_refl W) (Nat.le_refl Dp) (Nat.le_refl N) h

end NearSpecV3
