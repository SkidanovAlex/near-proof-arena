import ZkFormal.NearV3.D1.Extract.Tx.Lane

/-!
# `ZkFormal.NearV3.D1.Extract.Tx.ChainN` — the nonce chains `N` (vs the key nonce) and `B` (vs the bound)

`N`: `dN = N − kn − cin + 256·boN` (`cin₀ = 1`): `N + 2¹²⁸·boN₁₅ = dN + kn + 1`.
`B`: `dB = Bd − N − cin + 256·boB` (`cin₀ = 1`): `Bd + 2¹²⁸·boB₁₅ = dB + N + 1`.
-/

namespace ZkFormal.NearV3.D1.TxProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.D1
  ZkFormal.NearV3.D1.TxV3

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

theorem dNb_bool : ∀ b, b < 8 → dNb b ∈ boolCols := by
  intro b hb; simp [boolCols, dNb, hb]
theorem dBb_bool : ∀ b, b < 8 → dBb b ∈ boolCols := by
  intro b hb; simp [boolCols, dBb, hb]

section
variable (hL : TableLocal TxV3.table tr tt pub)
include hL

/-- A borrow chain over columns: `d = X − Y − cin + 256·bo`, `cin₀ = 1`. -/
theorem laneSub (X Y bo : Nat) (d : Nat → Nat) (hdb : ∀ b, b < 8 → d b ∈ boolCols)
    (hbob : bo ∈ boolCols)
    (m0 : first (sub (byteC d) (sub (sub (c X) (c Y)) (sub (k 1) (smul 256 (c bo))))) ∈ cChains)
    (m1 : inOpE (sub (byteN d) (sub (sub (n X) (n Y)) (sub (c bo) (smul 256 (n bo))))) ∈ cChains)
    {s : Nat} (hop : OpAt tr tt s) (j : Nat) (hj : j < 16)
    (hx : cv tr tt (s + j) X < 256) (hk : cv tr tt (s + j) Y < 256) :
    cv tr tt (s + j) X + 256 * cv tr tt (s + j) bo =
      bv tr tt (s + j) d + cv tr tt (s + j) Y +
        (if j = 0 then 1 else cv tr tt (s + j - 1) bo) := by
  have hH := hop.h
  have hbo : cv tr tt (s + j) bo ≤ 1 := cv_bool' hL (by omega) hbob
  have hd := bv_lt hL (r := s + j) (by omega) hdb
  rcases Nat.eq_zero_or_pos j with h0 | hpos
  · subst h0
    have e := con hL (r := s) (by omega)
      (mem_chains m0)
    have hlf := hop.lf 0 (by omega)
    simp only [Nat.add_zero, ite_true] at hlf hx hk hbo hd ⊢
    simp only [first, byteC, eval_mul, eval_sub, eval_c, eval_k, eval_smul, hlf,
      eval_byte hL (r := s) (by omega) hdb] at e
    apply natEq (by unfold P; omega) (by unfold P; omega)
    simp only [natCast_add, natCast_mul, ← cell_eq_cast]
    grind
  · have hb' : cv tr tt (s + j - 1) bo ≤ 1 := cv_bool' hL (by omega) hbob
    have e := con hL (r := s + j - 1) (by omega)
      (mem_chains m1)
    have ha := hop.act (j - 1) (by omega)
    have hl := hop.ll (j - 1) (by omega)
    rw [if_neg (by omega)] at hl
    rw [show s + (j - 1) = s + j - 1 by omega] at ha hl
    have hn : s + j - 1 + 1 < tr.height tt := by omega
    simp only [inOpE, inOp, byteN, eval_mul, eval_sub, eval_c, eval_n, eval_k, eval_smul, eval_not,
      ha, hl, eval_bitsN hn, nxt hn, show s + j - 1 + 1 = s + j by omega,
      Nat.mod_eq_of_lt (show s + j < tr.height tt by omega),
      eval_byte hL (r := s + j) (by omega) hdb] at e
    rw [if_neg (by omega)]
    apply natEq (by unfold P; omega) (by unfold P; omega)
    simp only [natCast_add, natCast_mul, ← cell_eq_cast]
    grind


theorem chainSub (X Y bo : Nat) (d : Nat → Nat) (hdb : ∀ b, b < 8 → d b ∈ boolCols)
    (hbob : bo ∈ boolCols)
    (m0 : first (sub (byteC d) (sub (sub (c X) (c Y)) (sub (k 1) (smul 256 (c bo))))) ∈ cChains)
    (m1 : inOpE (sub (byteN d) (sub (sub (n X) (n Y)) (sub (c bo) (smul 256 (n bo))))) ∈ cChains)
    {s : Nat} (hop : OpAt tr tt s)
    (hx : ∀ j, j < 16 → cv tr tt (s + j) X < 256) (hy : ∀ j, j < 16 → cv tr tt (s + j) Y < 256) :
    RcptProof.sumL (fun j => cv tr tt (s + j) X) 16 + 256 ^ 16 * cv tr tt (s + 15) bo =
      RcptProof.sumL (fun j => bv tr tt (s + j) d) 16 + RcptProof.sumL (fun j => cv tr tt (s + j) Y) 16 + 1 := by
  have := RcptProof.chainC 16 (by omega) (fun j => cv tr tt (s + j) X)
    (fun j => bv tr tt (s + j) d + cv tr tt (s + j) Y)
    (fun j => if j = 0 then 1 else cv tr tt (s + j - 1) bo) (fun j => cv tr tt (s + j) bo)
    (fun j hj => laneSub hL X Y bo d hdb hbob m0 m1 hop j hj (hx j hj) (hy j hj))
    (fun j hj => by simp [show s + (j + 1) - 1 = s + j by omega])
  rw [RcptProof.sumL_add] at this
  simpa using this

/-- `N + 2¹²⁸·boN₁₅ = dN + kn + 1`. -/
theorem chainN {s : Nat} (hop : OpAt tr tt s)
    (hx : ∀ j, j < 16 → cv tr tt (s + j) xN < 256) (hy : ∀ j, j < 16 → cv tr tt (s + j) kn < 256) :
    RcptProof.sumL (fun j => cv tr tt (s + j) xN) 16 + 256 ^ 16 * cv tr tt (s + 15) boN =
      RcptProof.sumL (fun j => bv tr tt (s + j) dNb) 16 + RcptProof.sumL (fun j => cv tr tt (s + j) kn) 16 + 1 :=
  chainSub hL xN kn boN dNb dNb_bool (by simp [boolCols]) (by simp [cChains, chain, dN])
    (by simp [cChains, chain]) hop hx hy

/-- `Bd + 2¹²⁸·boB₁₅ = dB + N + 1`. -/
theorem chainB {s : Nat} (hop : OpAt tr tt s)
    (hx : ∀ j, j < 16 → cv tr tt (s + j) xB < 256) (hy : ∀ j, j < 16 → cv tr tt (s + j) xN < 256) :
    RcptProof.sumL (fun j => cv tr tt (s + j) xB) 16 + 256 ^ 16 * cv tr tt (s + 15) boB =
      RcptProof.sumL (fun j => bv tr tt (s + j) dBb) 16 + RcptProof.sumL (fun j => cv tr tt (s + j) xN) 16 + 1 :=
  chainSub hL xB xN boB dBb dBb_bool (by simp [boolCols]) (by simp [cChains, chain, dB])
    (by simp [cChains, chain]) hop hx hy

end

end ZkFormal.NearV3.D1.TxProof
