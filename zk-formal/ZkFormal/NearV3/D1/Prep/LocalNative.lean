import ZkFormal.NearV3.D1.PrepD1Lemmas

/-!
# `ZkFormal.NearV3.D1.Prep.LocalNative` — `PrepLocalNativeStmt`

Lane `v3-d1-phase2` (milestone P1).  A local receipt that `applyReceipt` applies has the native
part `localApply` computes: its outcome (the D1 leaf of `applyReceipt`'s outcome with status
`SuccessValue`), its refunds and its burnt tokens; the gas grows by `G`.
`localApply_of_applyReceipt` is the stronger form (the outcome itself and the leaf).
-/

namespace ZkFormal.NearV3.D1

open NearSpec NearSpec.TransferV1 NearSpecV3

/-- **`applyReceipt` ⇒ `localApply`**, with the outcome. -/
theorem localApply_of_applyReceipt {ctx : ApplyCtx} {st st' : Acc} {r : Receipt}
    (h : applyReceipt ⟨ctx.height, ctx.gasPrice⟩ st r = some st') :
    ∃ o rf burnt, localApply ctx r = some (({ o := o, status := .value } : OutD1).leaf, rf, burnt) ∧
      st'.outcomes = st.outcomes ++ [o] ∧
      st'.refunds = st.refunds ++ rf ∧ st'.tokensBurnt = st.tokensBurnt + burnt ∧
      st'.gasBurnt = st.gasBurnt + Params.G := by
  unfold applyReceipt at h
  simp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      split at h
      · cases h
      split at h
      · cases h
      split at h
      · cases h
      split at h
      · cases h
      split at h
      · cases h
      · rename_i hb _ _ _ _
        injection h with h
        subst h
        refine ⟨_, _, _, ?_, rfl, rfl, rfl, rfl⟩
        unfold localApply
        simp only at hb ⊢
        rw [if_neg hb]

/-- **`PrepLocalNativeStmt`.** -/
theorem prepLocalNative : PrepLocalNativeStmt := by
  intro ctx st st' r h
  obtain ⟨o, rf, burnt, h1, -, h2, h3, h4⟩ := localApply_of_applyReceipt h
  exact ⟨_, rf, burnt, h1, h2, h3, h4⟩

end ZkFormal.NearV3.D1
