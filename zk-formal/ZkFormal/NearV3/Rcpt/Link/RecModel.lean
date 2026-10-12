import ZkFormal.NearV3.Rcpt.Link.RecChain

/-!
# ZkFormal.NearV3.Rcpt.Link.RecModel — the ledger model of the records

`recModel ls as base T`: receipts `(rv ls).map toReceipt` (= `ExtV3.applied` for
`x.receipts = ls`), slot of receipt `r` = its `kslot` (the `FINAL` target of its account walk),
pre-state account of slot `k` = `accOf` of the acct record with `a.k = k` (v1 `Link.accOf`),
unwritten slots `base`, trie family `T` (both from the trie link).

Under `RecHyp` (and `ctx.gasPrice` = the public block gas price):

* `amt_inv` — the model's amount of an acct slot before receipt `r` is the value of the slot's
  last `MEM` write;
* `tok_inv` — the model's running token sum is the view's `toks`;
* **`rcptOk_all`** — `RcptOk3 ctx M r` for every receipt.
-/

namespace ZkFormal.NearV3.RcptLink

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Link NearSpec NearSpec.TransferV1 NearSpecV3

def dfltAccount : Account := ⟨0, 0, [], 0⟩

/-- The ledger model of the records. -/
def recModel (ls : RcptV3Vs) (as : List AcctV) (base : Nat → NearSpec.Bytes)
    (T : (Nat → NearSpec.Bytes) → PTrie) : RunModel where
  rs := (rv ls).map RcptV.toReceipt
  slot := fun r => (R (rv ls) r).kslot
  acc0 := fun k => ((acctOf as k).map accOf).getD dfltAccount
  base := base
  T := T

section
variable {ls : RcptV3Vs} {as : List AcctV} {base : Nat → NearSpec.Bytes}
  {T : (Nat → NearSpec.Bytes) → PTrie}

theorem recModel_length : (recModel ls as base T).rs.length = (flatR ls).length := by
  simp [recModel, rv_length]

theorem recModel_rc {r : Nat} (hr : r < (flatR ls).length) :
    (recModel ls as base T).rc r = (R (rv ls) r).toReceipt := by
  have hr' : r < (rv ls).length := by rwa [rv_length]
  simp only [RunModel.rc, recModel, R, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hr', Option.map_some, Option.getD_some]

theorem recModel_acc0 (hnd : (as.map (·.k)).Nodup) {a : AcctV} (ha : a ∈ as) :
    (recModel ls as base T).acc0 a.k = accOf a := by
  simp [recModel, acctOf_eq hnd ha]

end

section Hyp
variable {pub : List Fp} {ls : RcptV3Vs} {as : List AcctV} (h : RecHyp pub ls as)
  (base : Nat → NearSpec.Bytes) (T : (Nat → NearSpec.Bytes) → PTrie)
include h

theorem amt_inv {a : AcctV} (ha : a ∈ as) :
    ∀ r, r ≤ (flatR ls).length →
      (recModel ls as base T).amtAt a.k r = wval (rv ls) a (lastW (ksl (rv ls)) a.k r)
  | 0, _ => by
    simp only [RunModel.amtAt, recModel_acc0 h.mem.knd ha, lastW, wval, if_true, accOf]
  | r + 1, hr => by
    have ih := amt_inv ha r (by omega)
    simp only [RunModel.amtAt, lastW]
    rw [ih]
    have hs : (recModel ls as base T).slot r = ksl (rv ls) r := rfl
    rw [hs]
    split
    · next hk =>
      have hr' : r < (flatR ls).length := by omega
      obtain ⟨toks, -, hw⟩ := toks_at h
      have ar := arith_at h hr' (hw r hr')
      rw [recModel_rc hr', ← bef_val h hr' ha hk.symm]
      simp only [wval, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel, RcptV.toReceipt]
      have e : (rv ls).getD r default = ((flatR ls).getD r default).toRcptV := R_rv ls r
      rw [R_rv, e]
      exact ar.1.symm
    · simp

theorem isSys_eq {r : Nat} (hr : r < (flatR ls).length) :
    (recModel ls as base T).isSys r = ((flatR ls).getD r default).sys := by
  obtain ⟨_, _, _, w⟩ := wf_at h hr
  have hs := w.sysIff
  simp only [RunModel.isSys, recModel_rc hr, R_rv, RcptV.toReceipt]
  cases hx : ((flatR ls).getD r default).sys
  · rw [hx] at hs
    have : ¬ toBytes ((flatR ls).getD r default).toRcptV.p = AccountId.system := fun he =>
      Bool.false_ne_true (hs.mpr he)
    simpa using this
  · rw [hx] at hs
    simpa using hs.mp rfl

theorem tok_inv (ctx : ApplyCtx) (hgp : ctx.gasPrice = leN' (pubBytes pub PH_GP 16))
    {toks : List Nat} (h0 : toks.head? = some 0)
    (hw : ∀ r, r < (flatR ls).length →
      ((flatR ls).getD r default).Wf r (pubBytes pub PH_GP 16) (toks.getD r 0) (toks.getD (r + 1) 0)) :
    ∀ r, r ≤ (flatR ls).length → (recModel ls as base T).tokAt ctx r = toks.getD r 0
  | 0, _ => by
    cases toks with
    | nil => simp at h0
    | cons t l => simp at h0; subst h0; rfl
  | r + 1, hr => by
    have hr' : r < (flatR ls).length := by omega
    have ar := arith_at h hr' (hw r hr')
    simp only [RunModel.tokAt]
    rw [tok_inv ctx hgp h0 hw r (by omega), ar.2.2.2.2.2.2.2.1, ar.2.2.2.2.1]
    simp only [RunModel.burnt, isSys_eq h base T hr', burntOf, burnPrice, recModel_rc hr', R_rv,
      RcptV.toReceipt, hgp]

theorem lk_eq {r : Nat} (hr : r < (flatR ls).length) {a : AcctV} (ha : a ∈ as)
    (hk : a.k = (R (rv ls) r).kslot) : leN' (R (rv ls) r).lk = (accOf a).locked := by
  obtain ⟨_, _, _, w⟩ := wf_at h hr
  obtain ⟨-, -, -, -, -, -, l7, -⟩ := w.lens
  have hl := (acct_len h ha).1
  simp only [accOf]; congr 1
  apply ext16 (by rw [R_rv]; exact l7) (by simp [hl.1])
  intro i hi
  rw [(lanes h r hr a ha hk i hi).1, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_take, if_pos hi, List.getElem?_drop]

theorem st_eq {r : Nat} (hr : r < (flatR ls).length) {a : AcctV} (ha : a ∈ as)
    (hk : a.k = (R (rv ls) r).kslot) : leN' (R (rv ls) r).st = (accOf a).storageUsage := by
  obtain ⟨_, _, _, w⟩ := wf_at h hr
  obtain ⟨-, -, -, -, -, -, -, l8, -⟩ := w.lens
  have hl := (acct_len h ha).1
  have : (R (rv ls) r).st = a.pre.drop 64 ++ List.replicate 8 0 := by
    apply ext16 (by rw [R_rv]; exact l8) (by simp [hl.1])
    intro i hi
    rw [(lanes h r hr a ha hk i hi).2.1]
    have hd : (a.pre.drop 64).length = 8 := by simp [hl.1]
    split
    · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
        List.getElem?_drop]
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), List.getElem?_replicate,
        if_pos (by rw [hd]; omega)]; rfl
  simp only [accOf]; rw [this, leN'_append_zeros]

/-- **Per-receipt arithmetic of the record model.** -/
theorem rcptOk_all (ctx : ApplyCtx) (hgp : ctx.gasPrice = leN' (pubBytes pub PH_GP 16)) :
    ∀ r, r < (recModel ls as base T).rs.length → (recModel ls as base T).RcptOk3 ctx r := by
  intro r hr
  rw [recModel_length] at hr
  obtain ⟨toks, h0, hw⟩ := toks_at h
  have ar := arith_at h hr (hw r hr)
  obtain ⟨a, ha, hk⟩ := slot_acct h r hr
  obtain ⟨hl, hnm⟩ := acct_len h ha
  have hs : (recModel ls as base T).slot r = a.k := hk.symm
  have hacc := recModel_acc0 (base := base) (T := T) (ls := ls) h.mem.knd ha
  have hamt : (recModel ls as base T).amtAt a.k r = leN' (R (rv ls) r).bef := by
    rw [amt_inv h base T ha r (by omega), bef_val h hr ha hk]
  have hdep : ((recModel ls as base T).rc r).deposit = leN' (R (rv ls) r).dep := by
    rw [recModel_rc hr]; rfl
  have hgpr : ((recModel ls as base T).rc r).gasPrice = leN' (R (rv ls) r).gp := by
    rw [recModel_rc hr]; rfl
  have hsys := isSys_eq h base T hr
  have hlk := lk_eq h hr ha hk
  have hst := st_eq h hr ha hk
  have htok := tok_inv h base T ctx hgp h0 hw r (by omega)
  rw [R_rv] at hamt hdep hgpr hlk hst
  obtain ⟨_, _, _, wr⟩ := wf_at h hr
  obtain ⟨-, -, -, -, -, -, -, -, -, lb, lra, -⟩ := wr.lens
  obtain ⟨a1, a2, a3, a4, a6, a7, a8, a9, a10⟩ := ar
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> try simp only [hs, hacc, hamt, hdep]
  · exact ⟨toBytes a.pre, decode_pre hl.1 (h.preB a ha) hnm⟩
  · rw [← a1]; exact a2
  · rw [← a1, ← hlk]; exact a3
  · rw [← a1, ← hlk, ← hst]; exact a4
  · intro hns
    rw [hsys] at hns
    have hb : burntOf ctx.gasPrice ((recModel ls as base T).rc r) =
        leN' ((flatR ls).getD r default).burnt := by
      rw [a6, hns]; simp [burntOf, burnPrice, hgpr, hgp]
    rw [hb]; exact leN'_16 lb
  · intro hns
    rw [hsys] at hns
    have hsur : surplusOf ctx.gasPrice ((recModel ls as base T).rc r) =
        Params.G * (leN' ((flatR ls).getD r default).gp -
          min (leN' ((flatR ls).getD r default).gp) (leN' (pubBytes pub PH_GP 16))) := by
      simp [surplusOf, burnPrice, hgpr, hgp]
    rw [hsur]
    cases hhr : ((flatR ls).getD r default).hr
    · have h0 : Params.G * (leN' ((flatR ls).getD r default).gp -
          min (leN' ((flatR ls).getD r default).gp) (leN' (pubBytes pub PH_GP 16))) = 0 := by
        apply Decidable.of_not_not
        intro hne
        have := a7.mpr ⟨hns, hne⟩
        rw [hhr] at this; cases this
      rw [h0]; decide
    · rw [← a8 hhr]; exact leN'_16 lra
  · intro hns
    rw [hsys] at hns
    have hb : burntOf ctx.gasPrice ((recModel ls as base T).rc r) =
        leN' ((flatR ls).getD r default).burnt := by
      rw [a6, hns]; simp [burntOf, burnPrice, hgpr, hgp]
    rw [hb, htok, ← a9]; exact a10

end Hyp

end ZkFormal.NearV3.RcptLink
