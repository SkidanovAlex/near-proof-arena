import ZkFormal.NearV3.D1.Extract.Tx.ChainQ

/-!
# `ZkFormal.NearV3.D1.Extract.Tx.ChainD` — chains `D` (`tot ≥ q`), `S` (`storage ≤ 770`), the
credit sum `msum` and the strict-nonce zero test `zN`
-/

namespace ZkFormal.NearV3.D1.TxProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.D1
  ZkFormal.NearV3.D1.TxV3

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

/-- `770` little endian, lane `k`. -/
def b770 (k : Nat) : Nat := if k = 0 then 2 else if k = 1 then 3 else 0

theorem sumL_b770 : RcptProof.sumL b770 16 = 770 := by
  simp [RcptProof.sumL, b770]

section
variable (hL : TableLocal TxV3.table tr tt pub)
include hL

theorem laneD {s : Nat} (hop : OpAt tr tt s) (j : Nat) (hj : j < 16) :
    bv tr tt (s + j) tTb + 256 * cv tr tt (s + j) boQ =
      bv tr tt (s + j) dQb + bv tr tt (s + j) qb + (if j = 0 then 0 else cv tr tt (s + j - 1) boQ) := by
  have hH := hop.h
  have hbo : cv tr tt (s + j) boQ ≤ 1 := cv_bool' hL (by omega) (by simp [boolCols])
  have hd := bv_lt hL (r := s + j) (by omega) dQb_bool
  have ht := bv_lt hL (r := s + j) (by omega) tTb_bool
  have hq := bv_lt hL (r := s + j) (by omega) qb_bool
  rcases Nat.eq_zero_or_pos j with h0 | hpos
  · subst h0
    have e := con hL (r := s) (by omega)
      (mem_chains (e := first (sub dQ (.add (sub tT q) (smul 256 (c boQ))))) (by simp [cChains, chain]))
    have hlf := hop.lf 0 (by omega)
    simp only [Nat.add_zero, ite_true] at hlf hbo hd ht hq ⊢
    simp only [first, dQ, tT, q, byteC, eval_mul, eval_sub, eval_add, eval_c, eval_k, eval_smul, hlf,
      eval_byte hL (r := s) (by omega) dQb_bool, eval_byte hL (r := s) (by omega) tTb_bool,
      eval_byte hL (r := s) (by omega) qb_bool] at e
    apply natEq (by unfold P; omega) (by unfold P; omega)
    simp only [natCast_add, natCast_mul, ← cell_eq_cast]
    grind
  · have hb' : cv tr tt (s + j - 1) boQ ≤ 1 := cv_bool' hL (by omega) (by simp [boolCols])
    have e := con hL (r := s + j - 1) (by omega)
      (mem_chains (e := inOpE (sub (byteN dQb) (sub (sub (byteN tTb) (byteN qb))
        (sub (c boQ) (smul 256 (n boQ)))))) (by simp [cChains, chain]))
    have hac := hop.act (j - 1) (by omega)
    have hl := hop.ll (j - 1) (by omega)
    rw [if_neg (by omega)] at hl
    rw [show s + (j - 1) = s + j - 1 by omega] at hac hl
    have hn : s + j - 1 + 1 < tr.height tt := by omega
    simp only [inOpE, inOp, byteN, eval_mul, eval_sub, eval_add, eval_c, eval_n, eval_k,
      eval_smul, eval_not, hac, hl, eval_bitsN hn, nxt hn, show s + j - 1 + 1 = s + j by omega,
      Nat.mod_eq_of_lt (show s + j < tr.height tt by omega),
      eval_byte hL (r := s + j) (by omega) dQb_bool, eval_byte hL (r := s + j) (by omega) tTb_bool,
      eval_byte hL (r := s + j) (by omega) qb_bool] at e
    rw [if_neg (by omega)]
    apply natEq (by unfold P; omega) (by unfold P; omega)
    simp only [natCast_add, natCast_mul, ← cell_eq_cast]
    grind

theorem laneS {s : Nat} (hop : OpAt tr tt s) (j : Nat) (hj : j < 16)
    (hst : cv tr tt (s + j) st < 256) :
    b770 j + 256 * cv tr tt (s + j) boS =
      bv tr tt (s + j) dSb + cv tr tt (s + j) st + (if j = 0 then 0 else cv tr tt (s + j - 1) boS) := by
  have hH := hop.h
  have hbo : cv tr tt (s + j) boS ≤ 1 := cv_bool' hL (by omega) (by simp [boolCols])
  have hd := bv_lt hL (r := s + j) (by omega) dSb_bool
  rcases Nat.eq_zero_or_pos j with h0 | hpos
  · subst h0
    have e := con hL (r := s) (by omega)
      (mem_chains (e := first (sub dS (.add (sub (k 2) (c st)) (smul 256 (c boS)))))
        (by simp [cChains, chain]))
    have hlf := hop.lf 0 (by omega)
    simp only [Nat.add_zero, ite_true, b770] at hlf hbo hd hst ⊢
    simp only [first, dS, byteC, eval_mul, eval_sub, eval_add, eval_c, eval_k, eval_smul, hlf,
      eval_byte hL (r := s) (by omega) dSb_bool] at e
    apply natEq (by unfold P; omega) (by unfold P; omega)
    simp only [natCast_add, natCast_mul, ← cell_eq_cast]
    grind
  · have hb' : cv tr tt (s + j - 1) boS ≤ 1 := cv_bool' hL (by omega) (by simp [boolCols])
    have e := con hL (r := s + j - 1) (by omega)
      (mem_chains (e := inOpE (sub (byteN dSb) (sub (sub (smul 3 (n l1)) (n st))
        (sub (c boS) (smul 256 (n boS)))))) (by simp [cChains, chain]))
    have hac := hop.act (j - 1) (by omega)
    have hl := hop.ll (j - 1) (by omega)
    have hl1 := hop.l1 j hj
    rw [if_neg (by omega)] at hl
    rw [show s + (j - 1) = s + j - 1 by omega] at hac hl
    have hn : s + j - 1 + 1 < tr.height tt := by omega
    simp only [inOpE, inOp, byteN, eval_mul, eval_sub, eval_add, eval_c, eval_n, eval_k,
      eval_smul, eval_not, hac, hl, eval_bitsN hn, nxt hn, show s + j - 1 + 1 = s + j by omega,
      Nat.mod_eq_of_lt (show s + j < tr.height tt by omega), hl1,
      eval_byte hL (r := s + j) (by omega) dSb_bool] at e
    rw [if_neg (by omega)]
    by_cases h1 : j = 1
    · subst h1
      simp only [b770, show ¬ (1 = 0) by omega, ite_true, ite_false] at e ⊢
      apply natEq (by unfold P; omega) (by unfold P; omega)
      simp only [natCast_add, natCast_mul, ← cell_eq_cast]
      grind
    · simp only [b770, show ¬ (j = 0) by omega, h1, ite_false] at e ⊢
      apply natEq (by unfold P; omega) (by unfold P; omega)
      simp only [natCast_add, natCast_mul, ← cell_eq_cast]
      grind

theorem chainD {s : Nat} (hop : OpAt tr tt s) :
    RcptProof.sumL (fun j => bv tr tt (s + j) tTb) 16 + 256 ^ 16 * cv tr tt (s + 15) boQ =
      RcptProof.sumL (fun j => bv tr tt (s + j) dQb) 16 + RcptProof.sumL (fun j => bv tr tt (s + j) qb) 16 := by
  have := RcptProof.chainC 16 (by omega) (fun j => bv tr tt (s + j) tTb)
    (fun j => bv tr tt (s + j) dQb + bv tr tt (s + j) qb)
    (fun j => if j = 0 then 0 else cv tr tt (s + j - 1) boQ) (fun j => cv tr tt (s + j) boQ)
    (fun j hj => by have := laneD hL hop j hj; omega)
    (fun j hj => by simp [show s + (j + 1) - 1 = s + j by omega])
  rw [RcptProof.sumL_add] at this
  simpa using this

theorem chainS {s : Nat} (hop : OpAt tr tt s) (hst : ∀ j, j < 16 → cv tr tt (s + j) st < 256) :
    770 + 256 ^ 16 * cv tr tt (s + 15) boS =
      RcptProof.sumL (fun j => bv tr tt (s + j) dSb) 16 + RcptProof.sumL (fun j => cv tr tt (s + j) st) 16 := by
  have := RcptProof.chainC 16 (by omega) b770
    (fun j => bv tr tt (s + j) dSb + cv tr tt (s + j) st)
    (fun j => if j = 0 then 0 else cv tr tt (s + j - 1) boS) (fun j => cv tr tt (s + j) boS)
    (fun j hj => by have := laneS hL hop j hj (hst j hj); omega)
    (fun j hj => by simp [show s + (j + 1) - 1 = s + j by omega])
  rw [RcptProof.sumL_add, sumL_b770] at this
  simpa using this

end

end ZkFormal.NearV3.D1.TxProof
