import ZkFormal.Near.Render.Proof.RcptStr
import ZkFormal.Near.Render.Proof.RcptLemCore

/-!
# ZkFormal.Near.Render.Proof.RcptLem — arithmetic toolkit for the `rcpt` rows

* `Fp.ofNat` of `x % P`, of `sqd`, of a truncated difference, inverses `invP`;
* bit pools: `bitsX off len` of the bits of `x < 2^len` is `x` (`evR_bitsX_of`);
* `evR_congr`: an expression only depends on the cells it reads (`colsC`,
  `colsN`), so a row can be replaced by a synthetic one.
-/

namespace ZkFormal.Near.Render

open NearSpec NearSpec.TransferV1 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.Near.Dsl

namespace RcptP

open RcptGen

/-! ## `Fp` -/

theorem ofNat_modA (x : Nat) : Fp.ofNat (x % ZkFormal.Algebra.P) = Fp.ofNat x := by
  apply Fp.ext; simp [Fp.toNat_ofNat, Nat.mod_mod]

theorem ofNat_invP {x : Nat} (h : Fp.ofNat x ≠ 0) : Fp.ofNat x * Fp.ofNat (invP x) = 1 := by
  simp only [invP, Fp.ofNat_toNat]
  exact Fp.mul_inv_cancel h

theorem ofNat_lt_eq {x : Nat} (h : x < P) : (Fp.ofNat x).toNat = x := by
  rw [Fp.toNat_ofNat, Nat.mod_eq_of_lt (by rw [← P_def]; exact h)]

/-! ## Bits -/

theorem bitOf_le (x j : Nat) : bitOf x j ≤ 1 := by unfold bitOf; omega

theorem bitsVal_bitOf (x : Nat) : ∀ len, bitsVal (fun j => bitOf x j) 0 len = x % 2 ^ len
  | 0 => by simp [bitsVal, Nat.mod_one]
  | len + 1 => by
    rw [bitsVal, bitsVal_bitOf x len, Nat.zero_add, bitOf, Nat.pow_succ, Nat.mod_mul]

theorem evR_bitsX {cur nx : Nat → Fp} {fst lst : Bool} {pub : List Fp} {v : Nat → Nat} (off : Nat) :
    ∀ len, (∀ j, off ≤ j → j < off + len → cur (Rcpt.xb j) = Fp.ofNat (v j)) →
      evR cur nx fst lst pub (Rcpt.bitsX off len) = Fp.ofNat (bitsVal v off len)
  | 0, _ => rfl
  | len + 1, hv => by
    rw [Rcpt.bitsX, bits_succ]
    have h := evR_bitsX (nx := nx) (fst := fst) (lst := lst) (pub := pub) off len (fun j h1 h2 => hv j h1 (by omega))
    have hv := hv (off + len) (by omega) (by omega)
    rw [Rcpt.bitsX, bits] at h
    have e : ∀ (l1 l2 : List Expr), evR cur nx fst lst pub (sum (l1 ++ l2)) =
        evR cur nx fst lst pub (sum l1) + evR cur nx fst lst pub (sum l2) := by
      intro l1 l2; induction l1 with
      | nil => simp; grind
      | cons a l ih => simp [ih]; grind
    rw [e, h]
    simp only [evR_sum_cons, evR_sum_nil, evR_smul, evR_c, hv, bitsVal, natCast_eq, ofNat_add_e, ofNat_mul_e]
    grind

theorem evR_bitsXn {cur nx : Nat → Fp} {fst lst : Bool} {pub : List Fp} {v : Nat → Nat} (off : Nat) :
    ∀ len, (∀ j, off ≤ j → j < off + len → nx (Rcpt.xb j) = Fp.ofNat (v j)) →
      evR cur nx fst lst pub (Rcpt.bitsXn off len) = Fp.ofNat (bitsVal v off len)
  | 0, _ => rfl
  | len + 1, hv => by
    rw [Rcpt.bitsXn, bits_succ]
    have h := evR_bitsXn (cur := cur) (fst := fst) (lst := lst) (pub := pub) off len (fun j h1 h2 => hv j h1 (by omega))
    have hv := hv (off + len) (by omega) (by omega)
    rw [Rcpt.bitsXn, bits] at h
    have e : ∀ (l1 l2 : List Expr), evR cur nx fst lst pub (sum (l1 ++ l2)) =
        evR cur nx fst lst pub (sum l1) + evR cur nx fst lst pub (sum l2) := by
      intro l1 l2; induction l1 with
      | nil => simp; grind
      | cons a l ih => simp [ih]; grind
    rw [e, h]
    simp only [evR_sum_cons, evR_sum_nil, evR_smul, evR_n, hv, bitsVal, natCast_eq, ofNat_add_e, ofNat_mul_e]
    grind

/-- Bits `off … off + len − 1` of a pool holding the bits of `x` from `off`. -/
theorem bitsVal_pool {v : Nat → Nat} {off len x : Nat} (hv : ∀ j, j < len → v (off + j) = bitOf x j)
    (hx : x < 2 ^ len) : bitsVal v off len = x := by
  rw [bitsVal_congr off len hv, bitsVal_bitOf, Nat.mod_eq_of_lt hx]

/-! ## Reads -/

end RcptP

end ZkFormal.Near.Render
