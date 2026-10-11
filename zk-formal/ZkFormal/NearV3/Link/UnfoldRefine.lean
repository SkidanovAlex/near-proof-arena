import NearSpecV3.ChunkValidationV0a
import NearSpec.TrieUpsertProofs

/-!
# ZkFormal.NearV3.Link.UnfoldRefine — the A7 measure is monotone under refinement

`unfoldedBytesT t` (RelD0a A7) sums, over the revealed node occurrences of `t`, the length of
the node encoding and of its revealed value.  If `t₁.refinedBy t₂` (`t₁` is `t₂` with some
subtrees replaced by their hash and some values by their `ValueRef`), every revealed occurrence of
`t₁` is one of `t₂` with the **same** encoding (hashes, bitmaps and value refs are preserved), and
a revealed value of `t₁` is revealed in `t₂`; so `unfoldedBytesT t₁ ≤ unfoldedBytesT t₂`
(`unfoldedBytesT_le_of_refinedBy`).

Use: the relation's partial tries are refinements of the record trees (`storeBuildR`), so the
A7 measure of the reconstructed witness is bounded by the records' byte count.
-/

namespace ZkFormal.NearV3.Link3

open NearSpec NearSpecV3

/-- Bytes of one occurrence: its node encoding plus its own revealed value. -/
def occBytes (o : PTrie) : Nat := (nodeEnc o).length + ((ownVals o).map List.length).sum

theorem unfoldedBytesT_eq (t : PTrie) :
    unfoldedBytesT t = ((occs t).map occBytes).sum := by
  unfold unfoldedBytesT valsOf occBytes
  generalize occs t = l
  induction l with
  | nil => simp
  | cons o l ih => simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.map_append,
      List.sum_append]; omega

theorem slotVal_le {s₁ s₂ : Slot} (h : SlotRefines s₁ s₂) :
    ((slotVal s₁).map List.length).sum ≤ ((slotVal s₂).map List.length).sum := by
  rcases h with rfl | ⟨v, rfl, rfl⟩
  · exact Nat.le_refl _
  · simp [slotVal]

mutual
theorem occsBytes_le : ∀ (t₁ t₂ : PTrie), t₁.refinedBy t₂ →
    ((occs t₁).map occBytes).sum ≤ ((occs t₂).map occBytes).sum
  | .hash _, _, _ => by simp [occs]
  | .leaf k s m, t₂, hr => by
    cases t₂ <;> simp only [PTrie.refinedBy] at hr
    obtain ⟨rfl, rfl, hs⟩ := hr
    simp only [occs, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
      occBytes, ownVals, nodeEnc, hs.valueRef]
    exact Nat.add_le_add_left (slotVal_le hs) _
  | .ext k c m, t₂, hr => by
    cases t₂ <;> simp only [PTrie.refinedBy] at hr
    obtain ⟨rfl, rfl, hc⟩ := hr
    simp only [occs, List.map_cons, List.sum_cons, occBytes, ownVals, nodeEnc,
      PTrie.hashOf_refinedBy c _ hc]
    exact Nat.add_le_add_left (occsBytes_le c _ hc) _
  | .branch v cs m, t₂, hr => by
    cases t₂ <;> simp only [PTrie.refinedBy] at hr
    rename_i v' cs' m'
    obtain ⟨rfl, hv, hcs⟩ := hr
    have ⟨hb, hh⟩ := Kids.hashOf_refinedBy cs cs' 0 hcs
    have hk := kOccsBytes_le cs cs' hcs
    cases v <;> cases v' <;> simp only [OptSlotRefines] at hv
    · simp only [occs, List.map_cons, List.sum_cons, occBytes, ownVals, optSlotVal, nodeEnc, hb, hh]
      exact Nat.add_le_add_left hk _
    · rename_i s s'
      simp only [occs, List.map_cons, List.sum_cons, occBytes, ownVals, optSlotVal, nodeEnc, hb, hh,
        hv.valueRef]
      exact Nat.add_le_add (Nat.add_le_add_left (slotVal_le hv) _) hk
theorem kOccsBytes_le : ∀ (cs₁ cs₂ : Kids), Kids.refinedBy cs₁ cs₂ →
    ((kOccs cs₁).map occBytes).sum ≤ ((kOccs cs₂).map occBytes).sum
  | .nil, cs₂, hr => by cases cs₂ <;> simp_all [Kids.refinedBy, kOccs]
  | .none r, cs₂, hr => by
    cases cs₂ <;> simp only [Kids.refinedBy] at hr
    simp only [kOccs]; exact kOccsBytes_le r _ hr
  | .some c r, cs₂, hr => by
    cases cs₂ <;> simp only [Kids.refinedBy] at hr
    simp only [kOccs, List.map_append, List.sum_append]
    exact Nat.add_le_add (occsBytes_le c _ hr.1) (kOccsBytes_le r _ hr.2)
end

/-- **The A7 measure is monotone under refinement.** -/
theorem unfoldedBytesT_le_of_refinedBy {t₁ t₂ : PTrie} (h : t₁.refinedBy t₂) :
    unfoldedBytesT t₁ ≤ unfoldedBytesT t₂ := by
  rw [unfoldedBytesT_eq, unfoldedBytesT_eq]; exact occsBytes_le t₁ t₂ h

end ZkFormal.NearV3.Link3
