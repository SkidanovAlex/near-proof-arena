import ZkFormal.NearV3.Assembly.ClaimFacts
import ZkFormal.NearV3.Assembly.Good

/-!
# ZkFormal.NearV3.Assembly.LinkClaim — the claim-level `GoodV3` fields from `prepD0`

`prepD0 cb h = .ok p` alone (no trace) gives the walk `walkD0 cb = .ok k` and the
claim-level `GoodV3` fields `mainTxRoot`, `ownCongestion`, `gasLimit` (A1) and
`distinctRequests` (A8): `prepClaim` checks each of them on the same decoded values
`walkD0` returns.
-/

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Sched

private theorem mapError_ok_iff' {ε ε' α : Type} (f : ε → ε') (x : Except ε α) (a : α) :
    x.mapError f = .ok a ↔ x = .ok a := by cases x <;> simp [Except.mapError]

/-- The claim-level `GoodV3` fields. -/
structure ClaimFieldsV3 (k : WalkD0) : Prop where
  mainTxRoot : k.slotB2.txRoot = zeroHash32
  ownCongestion : k.slotB2.congestion.delayedGas = 0 ∧
    k.slotB2.congestion.bufferedGas = 0 ∧ k.slotB2.congestion.receiptBytes = 0
  gasLimit : k.slotB2.gasLimit ≤ maxGasLimitD0
  distinctRequests : ∀ b ∈ k.blks, ∀ s ci, (s, ci) ∈ b.slots →
    (ci.bwRequests.map (·.toShard)).Nodup

set_option maxHeartbeats 4000000 in
/-- **The walk and the claim-level fields** whenever `prepClaim` succeeds. -/
theorem walkD0_of_prepClaim {cb : Bytes} {pc : PrepC} (hp : prepClaim cb = .ok pc) :
    ∃ k, walkD0 cb = .ok k ∧ ClaimFieldsV3 k := by
  unfold prepClaim at hp
  repeat' (first
    | (obtain ⟨_, hs, hn⟩ := bind_ok hp; clear hp; have hp := hn; clear hn)
    | (split at hp)
    | (dsimp only at hp))
  all_goals try (cases hp; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    expose_names
    simp only [mapError_ok_iff', pure, Except.pure, Except.ok.injEq] at hs_1 hs_2 hs_6 hs_14 hs_21 hs_23 hs_24 hs_27 hs_30 hs_31
    subst hs_21; subst hs_23; subst hs_24; subst hs_27; subst hs_30; subst hs_31
    have h20 := check_ok hs_20
    have h32 := check_ok hs_32
    have h34 := check_ok hs_34
    have h35 := check_ok hs_35
    unfold walkD0
    simp only [hs_1, hs_2, hs_6, hs_14, heq, bind, Except.bind, pure, Except.pure]
    split
    · rename_i i' hi'
      obtain rfl : i' = i_1 := Option.some.inj (hi'.symm.trans heq_1)
      split
      · rename_i j' hj'
        obtain rfl : j' = i_2 := Option.some.inj (hj'.symm.trans heq_3)
        simp only [heq_2, Option.bind_some, heq_5]
        refine ⟨_, rfl, ?_, ?_, ?_, ?_⟩
        · simpa only [beq_iff_eq] using h34
        · simpa only [Bool.and_eq_true, beq_iff_eq, and_assoc] using h35
        · simpa only [decide_eq_true_eq] using h32
        · intro b hb s ci hs
          have := List.all_eq_true.mp (List.all_eq_true.mp h20 b hb) (s, ci) hs
          simpa only [decide_eq_true_eq] using this
      · rename_i hj'
        exact absurd (hj'.symm.trans heq_3) (by simp)
    · rename_i hi'
      exact absurd (hi'.symm.trans heq_1) (by simp)

/-- The walk and the claim-level `GoodV3` fields from `prepD0`. -/
theorem walkD0_of_prepD0 {cb : Bytes} {h : Hint} {p : Prep} (hp : prepD0 cb h = .ok p) :
    ∃ k, walkD0 cb = .ok k ∧ ClaimFieldsV3 k := by
  obtain ⟨pc, hc, _⟩ := bind_ok hp
  exact walkD0_of_prepClaim hc

/-- The `GoodV3` fields that depend on the reconstructed views `x` (everything except the
walk, the preparation and the claim-level `ClaimFieldsV3`). -/
structure ExtFieldsV3 (B : Nat) (cb : Bytes) (k : WalkD0) (h : Hint) (p : Prep) (x : ExtV3) :
    Prop where
  shape : V3.D0Shape (stateWitnessOfV3 k x)
  witnessBytes : (V3.encodeSW (stateWitnessOfV3 k x)).length ≤ 8388608
  mainStoreBytes : ((x.store 0).map List.length).foldl (· + ·) 0 ≤ 3000000
  source : SourceSemanticsV3 k x
  receiptCount : h.n = x.applied.length
  receiptIds : (x.applied.map Receipt.receiptId).Nodup
  executions : ∃ m last, m.Valid k x ∧
    ImplicitRunV3 k x 1 m.result.trie.hashOf k.implicitBlks last ∧
    HeaderSemanticsV3 k h p m last
  canonicalScheduler : (reads0f k (stateWitnessOfV3 k x)).all (canonical0f k.L) = true
  unfoldedBytes : unfoldBytes cb (witnessOfV3 k x) ≤ B
  chachaWords : chachaWords cb (witnessOfV3 k x) ≤ W0
  pathDepth : ∀ e ∈ usedProofs k (stateWitnessOfV3 k x), e.proof.path.length ≤ Dp0

/-- `GoodV3` from its claim-level part and its view-level part. -/
theorem goodV3_of_parts {B : Nat} {cb : Bytes} {k : WalkD0} {h : Hint} {p : Prep} {x : ExtV3}
    (hw : walkD0 cb = .ok k) (hp : prepD0 cb h = .ok p) (C : ClaimFieldsV3 k)
    (E : ExtFieldsV3 B cb k h p x) : GoodV3 B cb k h p x where
  walk := hw
  prepared := hp
  shape := E.shape
  witnessBytes := E.witnessBytes
  mainStoreBytes := E.mainStoreBytes
  source := E.source
  receiptCount := E.receiptCount
  receiptIds := E.receiptIds
  mainTxRoot := C.mainTxRoot
  ownCongestion := C.ownCongestion
  executions := E.executions
  gasLimit := C.gasLimit
  canonicalScheduler := E.canonicalScheduler
  unfoldedBytes := E.unfoldedBytes
  distinctRequests := C.distinctRequests
  chachaWords := E.chachaWords
  pathDepth := E.pathDepth

/-- `GoodV3` reduces to its view-level fields: `prepD0` supplies the walk and the
claim-level fields. -/
theorem goodV3_of_ext {B : Nat} {cb : Bytes} {h : Hint} {p : Prep} (hp : prepD0 cb h = .ok p)
    (E : ∀ k, walkD0 cb = .ok k → ∃ x, ExtFieldsV3 B cb k h p x) : ∃ k x, GoodV3 B cb k h p x := by
  obtain ⟨k, hw, C⟩ := walkD0_of_prepD0 hp
  obtain ⟨x, hx⟩ := E k hw
  exact ⟨k, x, goodV3_of_parts hw hp C hx⟩

end ZkFormal.NearV3.Assembly
