import ZkFormal.NearV3.D1.Extract.Tx.ChainN

/-!
# `ZkFormal.NearV3.D1.Extract.Tx.ChainC` — the amount chain `C` and the total chain `T`

`C`: `rC = amt + σ·(C + cin − 256·coC)`, `σ = 2·kind − 1`, `cin₀ = 0`:
debit `amt + 2¹²⁸·coC₁₅ = rC + C`, credit `rC + 2¹²⁸·coC₁₅ = amt + C`.
`T`: `tT + 256·coT = rC + lk + cin`, `cin₀ = 0`: `tT + 2¹²⁸·coT₁₅ = rC + lk`.
-/

namespace ZkFormal.NearV3.D1.TxProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.D1
  ZkFormal.NearV3.D1.TxV3

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

theorem rCb_bool : ∀ b, b < 8 → rCb b ∈ boolCols := by
  intro b hb; simp [boolCols, rCb, hb]
theorem tTb_bool : ∀ b, b < 8 → tTb b ∈ boolCols := by
  intro b hb; simp [boolCols, tTb, hb]

section
variable (hL : TableLocal TxV3.table tr tt pub)
include hL

theorem kind_at {s : Nat} (hop : OpAt tr tt s) (j : Nat) (hj : j < 16) :
    tr.cell tt (s + j) kind = tr.cell tt s kind := hop.const j hj kind (by simp [opConst])

/-- Lane `j` of chain `C`: debit (`kind = 0`) and credit (`kind = 1`). -/
theorem laneC {s : Nat} (hop : OpAt tr tt s) (j : Nat) (hj : j < 16)
    (ha : cv tr tt (s + j) amt < 256) (hc : cv tr tt (s + j) xC < 256) :
    (tr.cell tt s kind = 0 →
      cv tr tt (s + j) amt + 256 * cv tr tt (s + j) coC =
        bv tr tt (s + j) rCb + cv tr tt (s + j) xC + (if j = 0 then 0 else cv tr tt (s + j - 1) coC)) ∧
    (tr.cell tt s kind = 1 →
      bv tr tt (s + j) rCb + 256 * cv tr tt (s + j) coC =
        cv tr tt (s + j) amt + cv tr tt (s + j) xC + (if j = 0 then 0 else cv tr tt (s + j - 1) coC)) := by
  have hH := hop.h
  have hbo : cv tr tt (s + j) coC ≤ 1 := cv_bool' hL (by omega) (by simp [boolCols])
  have hd := bv_lt hL (r := s + j) (by omega) rCb_bool
  rcases Nat.eq_zero_or_pos j with h0 | hpos
  · subst h0
    have e := con hL (r := s) (by omega)
      (mem_chains (e := first (sub rC (.add (c amt) (.mul sigma (sub (c xC) (smul 256 (c coC)))))))
        (by simp [cChains, chain]))
    have hlf := hop.lf 0 (by omega)
    simp only [Nat.add_zero, ite_true] at hlf ha hc hbo hd ⊢
    simp only [first, rC, byteC, sigma, eval_mul, eval_sub, eval_add, eval_c, eval_k, eval_smul, hlf,
      eval_byte hL (r := s) (by omega) rCb_bool] at e
    refine ⟨fun hk => ?_, fun hk => ?_⟩ <;> rw [hk] at e <;>
      apply natEq (by unfold P; omega) (by unfold P; omega) <;>
      simp only [natCast_add, natCast_mul, ← cell_eq_cast] <;> grind
  · have hb' : cv tr tt (s + j - 1) coC ≤ 1 := cv_bool' hL (by omega) (by simp [boolCols])
    have e := con hL (r := s + j - 1) (by omega)
      (mem_chains (e := inOpE (sub (byteN rCb) (.add (n amt) (.mul sigma
        (sub (.add (n xC) (c coC)) (smul 256 (n coC))))))) (by simp [cChains, chain]))
    have hac := hop.act (j - 1) (by omega)
    have hl := hop.ll (j - 1) (by omega)
    have hkd := kind_at hL hop (j - 1) (by omega)
    rw [if_neg (by omega)] at hl
    rw [show s + (j - 1) = s + j - 1 by omega] at hac hl hkd
    have hn : s + j - 1 + 1 < tr.height tt := by omega
    simp only [inOpE, inOp, byteN, sigma, eval_mul, eval_sub, eval_add, eval_c, eval_n, eval_k,
      eval_smul, eval_not, hac, hl, hkd, eval_bitsN hn, nxt hn, show s + j - 1 + 1 = s + j by omega,
      Nat.mod_eq_of_lt (show s + j < tr.height tt by omega),
      eval_byte hL (r := s + j) (by omega) rCb_bool] at e
    rw [if_neg (by omega)]
    refine ⟨fun hk => ?_, fun hk => ?_⟩ <;> rw [hk] at e <;>
      apply natEq (by unfold P; omega) (by unfold P; omega) <;>
      simp only [natCast_add, natCast_mul, ← cell_eq_cast] <;> grind

/-- Lane `j` of chain `T`. -/
theorem laneT {s : Nat} (hop : OpAt tr tt s) (j : Nat) (hj : j < 16)
    (hk : cv tr tt (s + j) lk < 256) :
    bv tr tt (s + j) tTb + 256 * cv tr tt (s + j) coT =
      bv tr tt (s + j) rCb + cv tr tt (s + j) lk + (if j = 0 then 0 else cv tr tt (s + j - 1) coT) := by
  have hH := hop.h
  have hbo : cv tr tt (s + j) coT ≤ 1 := cv_bool' hL (by omega) (by simp [boolCols])
  have hd := bv_lt hL (r := s + j) (by omega) rCb_bool
  have ht := bv_lt hL (r := s + j) (by omega) tTb_bool
  rcases Nat.eq_zero_or_pos j with h0 | hpos
  · subst h0
    have e := con hL (r := s) (by omega)
      (mem_chains (e := first (sub (.add tT (smul 256 (c coT))) (.add rC (c lk))))
        (by simp [cChains, chain]))
    have hlf := hop.lf 0 (by omega)
    simp only [Nat.add_zero, ite_true] at hlf hk hbo hd ht ⊢
    simp only [first, rC, tT, byteC, eval_mul, eval_sub, eval_add, eval_c, eval_k, eval_smul, hlf,
      eval_byte hL (r := s) (by omega) rCb_bool, eval_byte hL (r := s) (by omega) tTb_bool] at e
    apply natEq (by unfold P; omega) (by unfold P; omega)
    simp only [natCast_add, natCast_mul, ← cell_eq_cast]
    grind
  · have hb' : cv tr tt (s + j - 1) coT ≤ 1 := cv_bool' hL (by omega) (by simp [boolCols])
    have e := con hL (r := s + j - 1) (by omega)
      (mem_chains (e := inOpE (sub (.add (byteN tTb) (smul 256 (n coT))) (sum [byteN rCb, n lk, c coT])))
        (by simp [cChains, chain]))
    have hac := hop.act (j - 1) (by omega)
    have hl := hop.ll (j - 1) (by omega)
    rw [if_neg (by omega)] at hl
    rw [show s + (j - 1) = s + j - 1 by omega] at hac hl
    have hn : s + j - 1 + 1 < tr.height tt := by omega
    simp only [inOpE, inOp, byteN, eval_mul, eval_sub, eval_add, eval_c, eval_n, eval_k,
      eval_smul, eval_not, eval_sum_cons, eval_sum_nil, hac, hl, eval_bitsN hn, nxt hn,
      show s + j - 1 + 1 = s + j by omega, Nat.mod_eq_of_lt (show s + j < tr.height tt by omega),
      eval_byte hL (r := s + j) (by omega) rCb_bool, eval_byte hL (r := s + j) (by omega) tTb_bool] at e
    rw [if_neg (by omega)]
    apply natEq (by unfold P; omega) (by unfold P; omega)
    simp only [natCast_add, natCast_mul, ← cell_eq_cast]
    grind

theorem chainC_debit {s : Nat} (hop : OpAt tr tt s) (hk : tr.cell tt s kind = 0)
    (ha : ∀ j, j < 16 → cv tr tt (s + j) amt < 256) (hc : ∀ j, j < 16 → cv tr tt (s + j) xC < 256) :
    RcptProof.sumL (fun j => cv tr tt (s + j) amt) 16 + 256 ^ 16 * cv tr tt (s + 15) coC =
      RcptProof.sumL (fun j => bv tr tt (s + j) rCb) 16 + RcptProof.sumL (fun j => cv tr tt (s + j) xC) 16 := by
  have := RcptProof.chainC 16 (by omega) (fun j => cv tr tt (s + j) amt)
    (fun j => bv tr tt (s + j) rCb + cv tr tt (s + j) xC)
    (fun j => if j = 0 then 0 else cv tr tt (s + j - 1) coC) (fun j => cv tr tt (s + j) coC)
    (fun j hj => by have := (laneC hL hop j hj (ha j hj) (hc j hj)).1 hk; omega)
    (fun j hj => by simp [show s + (j + 1) - 1 = s + j by omega])
  rw [RcptProof.sumL_add] at this
  simpa using this

theorem chainC_credit {s : Nat} (hop : OpAt tr tt s) (hk : tr.cell tt s kind = 1)
    (ha : ∀ j, j < 16 → cv tr tt (s + j) amt < 256) (hc : ∀ j, j < 16 → cv tr tt (s + j) xC < 256) :
    RcptProof.sumL (fun j => bv tr tt (s + j) rCb) 16 + 256 ^ 16 * cv tr tt (s + 15) coC =
      RcptProof.sumL (fun j => cv tr tt (s + j) amt) 16 + RcptProof.sumL (fun j => cv tr tt (s + j) xC) 16 := by
  have := RcptProof.chainC 16 (by omega) (fun j => bv tr tt (s + j) rCb)
    (fun j => cv tr tt (s + j) amt + cv tr tt (s + j) xC)
    (fun j => if j = 0 then 0 else cv tr tt (s + j - 1) coC) (fun j => cv tr tt (s + j) coC)
    (fun j hj => by have := (laneC hL hop j hj (ha j hj) (hc j hj)).2 hk; omega)
    (fun j hj => by simp [show s + (j + 1) - 1 = s + j by omega])
  rw [RcptProof.sumL_add] at this
  simpa using this

theorem chainT {s : Nat} (hop : OpAt tr tt s) (hk : ∀ j, j < 16 → cv tr tt (s + j) lk < 256) :
    RcptProof.sumL (fun j => bv tr tt (s + j) tTb) 16 + 256 ^ 16 * cv tr tt (s + 15) coT =
      RcptProof.sumL (fun j => bv tr tt (s + j) rCb) 16 + RcptProof.sumL (fun j => cv tr tt (s + j) lk) 16 := by
  have := RcptProof.chainC 16 (by omega) (fun j => bv tr tt (s + j) tTb)
    (fun j => bv tr tt (s + j) rCb + cv tr tt (s + j) lk)
    (fun j => if j = 0 then 0 else cv tr tt (s + j - 1) coT) (fun j => cv tr tt (s + j) coT)
    (fun j hj => by have := laneT hL hop j hj (hk j hj); omega)
    (fun j hj => by simp [show s + (j + 1) - 1 = s + j by omega])
  rw [RcptProof.sumL_add] at this
  simpa using this

end

end ZkFormal.NearV3.D1.TxProof
