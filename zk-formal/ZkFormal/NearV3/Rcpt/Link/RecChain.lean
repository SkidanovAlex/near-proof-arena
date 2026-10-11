import ZkFormal.NearV3.Rcpt.Link.MemOf
import ZkFormal.NearV3.Rcpt.Link.RunModel
import ZkFormal.Near.Link.Run

/-!
# ZkFormal.NearV3.Rcpt.Link.RecChain — slot values along the `MEM` chain, per-receipt arithmetic

v1's `Link/RunChain` + `Link/Run` for the v3 records, over the hypothesis bundle `RecHyp`:
the `MEM` chain (`MemHyp`), the receipt view (`RcptV3Wf`), the account view, and the byte-ness
facts the `RcptE.Wf.arith` statement needs (each a separate field, with its source in the
module `RecModel`'s doc).

* `slot_acct` — every receipt's slot has an acct record;
* `lanes` — `lk`, `st` are the slot's pre-state lanes, `bef` is bytes;
* `arith_at` — the arithmetic facts of every receipt with all byte hypotheses discharged;
* `bef_val` — a receipt reads the value of the slot's last write (`Link.wval`).
-/

namespace ZkFormal.NearV3.RcptLink

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Link NearSpec

/-- The hypotheses of the receipt-side chain. -/
structure RecHyp (pub : List Fp) (ls : RcptV3Vs) (as : List AcctV) : Prop where
  mem : MemHyp (rv ls) as
  wf : RcptV3Wf pub ls
  acct : AcctV3WfE 19 as
  /-- the account records' pre bytes are bytes (`VBYTES`: the value records' bytes) -/
  preB : ∀ a ∈ as, Bytes8 a.pre
  /-- receipt encodings are bytes (`LinkRidBytes.encBytes`) -/
  encB : ∀ x ∈ flatR ls, Bytes8 x.enc
  /-- the burnt amounts are bytes (they are in the hashed `PEO` outcome bytes) -/
  burntB : ∀ x ∈ flatR ls, Bytes8 x.burnt
  /-- the refund amounts are bytes (they are in the public refund body) -/
  ramtB : ∀ x ∈ flatR ls, x.hr = true → Bytes8 x.ramt
  /-- the public block gas price is bytes (`LinkFields.pubNat_pubOf_lt`) -/
  bgpB : Bytes8 (pubBytes pub PH_GP 16)

section Hyp
variable {pub : List Fp} {ls : RcptV3Vs} {as : List AcctV} (h : RecHyp pub ls as)
include h

theorem acct_len {a : AcctV} (ha : a ∈ as) :
    (a.pre.length = 72 ∧ a.post.length = 16 ∧ a.k < P ∧ a.tlast < P) ∧
      ∃ i, i < 16 ∧ a.pre.getD i 0 ≠ 255 := by
  rcases h.acct with he | hw
  · rw [he] at ha; cases ha
  · exact ⟨hw.v1.len a ha, hw.v1.notMax a ha (fun i _ => getD_lt_of_bytes8 (h.preB a ha) i)⟩

theorem toks_at : ∃ toks : List Nat, toks.head? = some 0 ∧
    ∀ r, r < (flatR ls).length →
      ((flatR ls).getD r default).Wf r (pubBytes pub PH_GP 16) (toks.getD r 0) (toks.getD (r + 1) 0) := by
  obtain ⟨toks, -, h0, hw, -⟩ := h.wf.toks
  refine ⟨toks, h0, fun r hr => ?_⟩
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr]
  exact hw r hr

theorem wf_at {r : Nat} (hr : r < (flatR ls).length) :
    ∃ a b c, ((flatR ls).getD r default).Wf r a b c := by
  obtain ⟨toks, -, hw⟩ := toks_at h
  exact ⟨_, _, _, hw r hr⟩

theorem slot_acct : ∀ r, r < (flatR ls).length → ∃ a ∈ as, a.k = (R (rv ls) r).kslot := by
  intro r
  induction r using Nat.strongRecOn with
  | _ r ih =>
    intro hr
    have hr' : r < (rv ls).length := by rwa [rv_length]
    rcases lastW_cases (ksl (rv ls)) (R (rv ls) r).kslot r with e | ⟨r0, -, -, e⟩
    · obtain ⟨a, ha, hk, -⟩ := (mem_read h.mem hr' (i := 0) (by decide)).1 e
      exact ⟨a, ha, hk⟩
    · obtain ⟨hlt, hk, -⟩ := (mem_read h.mem hr' (i := 0) (by decide)).2 r0 e
      obtain ⟨a, ha, hk'⟩ := ih r0 hlt (by omega)
      exact ⟨a, ha, hk'.trans hk⟩

/-- Lanes of a receipt's read: locked and storage are the slot's pre-state lanes. -/
theorem lanes : ∀ r, r < (flatR ls).length → ∀ a ∈ as, a.k = (R (rv ls) r).kslot → ∀ i, i < 16 →
    (R (rv ls) r).lk.getD i 0 = a.pre.getD (16 + i) 0 ∧
    (R (rv ls) r).st.getD i 0 = (if i < 8 then a.pre.getD (64 + i) 0 else 0) ∧
    (R (rv ls) r).bef.getD i 0 < 256 := by
  intro r
  induction r using Nat.strongRecOn with
  | _ r ih =>
    intro hr a ha hk i hi
    have hr' : r < (rv ls).length := by rwa [rv_length]
    rcases lastW_cases (ksl (rv ls)) (R (rv ls) r).kslot r with e | ⟨r0, -, -, e⟩
    · obtain ⟨b, hb, hbk, he⟩ := (mem_read h.mem hr' hi).1 e
      have : b = a := acct_eq_of_k h.mem.knd hb ha (hbk.trans hk.symm)
      subst this
      simp only [rdMsg, awMsg, acctLane, List.cons_append, List.nil_append, List.cons.injEq] at he
      refine ⟨he.2.2.2.2.1, he.2.2.2.2.2.1, ?_⟩
      rw [he.2.2.2.1]; exact getD_lt_of_bytes8 (h.preB b hb) _
    · obtain ⟨hlt, hk0, he⟩ := (mem_read h.mem hr' hi).2 r0 e
      have hr0 : r0 < (flatR ls).length := by omega
      obtain ⟨_, _, _, w0⟩ := wf_at h hr0
      obtain ⟨i1, i2, -⟩ := ih r0 hlt hr0 a ha (hk.trans hk0.symm) i hi
      simp only [rdMsg, wrMsg, List.cons.injEq] at he
      refine ⟨he.2.2.2.2.1.trans i1, he.2.2.2.2.2.1.trans i2, ?_⟩
      rw [he.2.2.2.1, R_rv]; exact getD_lt_of_bytes8 w0.aft8 _

/-- The arithmetic facts of receipt `r` with every byte hypothesis discharged. -/
theorem arith_at {r : Nat} (hr : r < (flatR ls).length) {tok tok' : Nat}
    (w : ((flatR ls).getD r default).Wf r (pubBytes pub PH_GP 16) tok tok') :
    let x := (flatR ls).getD r default; let bgp := leN' (pubBytes pub PH_GP 16)
    leN' x.aft = leN' x.bef + leN' x.dep ∧ leN' x.aft < Params.u128Max ∧
    leN' x.aft + leN' x.lk < Params.two128 ∧
    (Params.storageAmountPerByte * leN' x.st ≤ leN' x.aft + leN' x.lk ∨
      leN' x.st ≤ Params.zeroBalanceStorageLimit) ∧
    leN' x.burnt = (if x.sys then 0 else Params.G * min (leN' x.gp) bgp) ∧
    (x.hr = true ↔ x.sys = false ∧ Params.G * (leN' x.gp - min (leN' x.gp) bgp) ≠ 0) ∧
    (x.hr = true → leN' x.ramt = Params.G * (leN' x.gp - min (leN' x.gp) bgp)) ∧
    tok' = tok + leN' x.burnt ∧ tok' < Params.two128 := by
  intro x bgp
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13⟩ := w.lens
  have hx : x ∈ flatR ls := getElem_flatR_mem hr
  have hencb := h.encB x hx
  have hgp : Bytes8 x.gp := bytes8_of_sub hencb (fun y hy => by simp [RcptV.enc, hy])
  have hdep : Bytes8 x.dep := bytes8_of_sub hencb (fun y hy => by simp [RcptV.enc, hy])
  obtain ⟨a, ha, hk⟩ := slot_acct h r hr
  have hl := lanes h r hr a ha hk
  rw [R_rv] at hl
  have hpre := h.preB a ha
  have hbef : Bytes8 x.bef := bytes8_of_getD l6 (fun i hi => (hl i hi).2.2)
  have hlk : Bytes8 x.lk := bytes8_of_getD l7 (fun i hi => by
    rw [(hl i hi).1]; exact getD_lt_of_bytes8 hpre _)
  have hst : Bytes8 x.st := bytes8_of_getD l8 (fun i hi => by
    rw [(hl i hi).2.1]; split
    · exact getD_lt_of_bytes8 hpre _
    · decide)
  obtain ⟨a1, a2, a3, a4, -, a6, a7, a8, a9, a10⟩ :=
    w.arith h.bgpB hgp hdep hbef hlk hst (h.burntB x hx) (h.ramtB x hx)
  refine ⟨a1, a2, a3, ?_, a6, a7, a8, a9, a10⟩
  have hst64 : leN' x.st < 2 ^ 64 := leN'_lt64 l8 hst (fun i h1 h2 => by
    rw [(hl i h2).2.1, if_neg (by omega)])
  have hm : Params.storageAmountPerByte * leN' x.st < Params.two128 := by
    unfold Params.storageAmountPerByte Params.two128; omega
  rw [Nat.mod_eq_of_lt hm] at a4
  exact a4

/-- A receipt reads the value of the slot's last write. -/
theorem bef_val {r : Nat} (hr : r < (flatR ls).length) {a : AcctV} (ha : a ∈ as)
    (hk : a.k = (R (rv ls) r).kslot) :
    leN' (R (rv ls) r).bef = wval (rv ls) a (lastW (ksl (rv ls)) a.k r) := by
  have hr' : r < (rv ls).length := by rwa [rv_length]
  obtain ⟨_, _, _, w⟩ := wf_at h hr
  obtain ⟨-, -, -, -, -, l6, -⟩ := w.lens
  have hl := (acct_len h ha).1
  rw [hk]
  rcases lastW_cases (ksl (rv ls)) (R (rv ls) r).kslot r with e | ⟨r0, -, -, e⟩
  · rw [e]; simp only [wval, if_true]
    congr 1
    apply ext16 (by rw [R_rv]; exact l6) (by simp [hl.1])
    intro i hi
    obtain ⟨b, hb, hbk, he⟩ := (mem_read h.mem hr' hi).1 e
    have : b = a := acct_eq_of_k h.mem.knd hb ha (hbk.trans hk.symm)
    subst this
    simp only [rdMsg, awMsg, acctLane, List.cons_append, List.nil_append, List.cons.injEq] at he
    rw [he.2.2.2.1, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take,
      if_pos hi]
  · rw [e]; simp only [wval, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
    obtain ⟨hlt, -, -⟩ := (mem_read h.mem hr' (i := 0) (by decide)).2 r0 e
    have hr0 : r0 < (flatR ls).length := by omega
    obtain ⟨_, _, _, w0⟩ := wf_at h hr0
    obtain ⟨-, -, -, -, -, -, -, -, l9, -⟩ := w0.lens
    congr 1
    apply ext16 (by rw [R_rv]; exact l6) (by
      show (R (rv ls) r0).aft.length = 16
      rw [R_rv]; exact l9)
    intro i hi
    obtain ⟨-, -, he2⟩ := (mem_read h.mem hr' hi).2 r0 e
    simp only [rdMsg, wrMsg, List.cons.injEq] at he2
    exact he2.2.2.2.1

end Hyp

end ZkFormal.NearV3.RcptLink
