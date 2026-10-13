import ZkFormal.Near.Render.Proof.RcptBase

/-! Declarations of `ZkFormal.Near.Render.Proof.RcptLem` split out (unchanged names and statements) so that
  importers needing only these do not pull in the rest of the module (certificate pruning). -/

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

theorem P_def : Render.P = ZkFormal.Algebra.P := rfl

theorem ofNat_mod (x : Nat) : Fp.ofNat (x % Render.P) = Fp.ofNat x := by
  apply Fp.ext; simp [Fp.toNat_ofNat, Nat.mod_mod, P_def]

theorem ofNat_sub {a b : Nat} (h : b ≤ a) : Fp.ofNat (a - b) = Fp.ofNat a - Fp.ofNat b := by
  have : Fp.ofNat a = Fp.ofNat (a - b) + Fp.ofNat b := by rw [ofNat_add']; congr 1; omega
  rw [this]; grind

theorem ofNat_sqd (a b : Nat) : Fp.ofNat (sqd a b) = (Fp.ofNat a - Fp.ofNat b) * (Fp.ofNat a - Fp.ofNat b) := by
  unfold sqd
  rcases Nat.le_total b a with h | h
  · rw [show b - a = 0 by omega, Nat.zero_mul, Nat.add_zero, ← ofNat_mul', ofNat_sub h]
  · rw [show a - b = 0 by omega, Nat.zero_mul, Nat.zero_add, ← ofNat_mul', ofNat_sub h]; grind

theorem ofNat_ne_zero {x : Nat} (h1 : x ≠ 0) (h2 : x < P) : Fp.ofNat x ≠ 0 := by
  intro h
  have := congrArg Fp.toNat h
  rw [Fp.toNat_ofNat, Nat.mod_eq_of_lt (by rw [← P_def]; exact h2)] at this
  exact h1 (this.trans rfl)

theorem bitsVal_congr {v w : Nat → Nat} (off : Nat) : ∀ len, (∀ j, j < len → v (off + j) = w j) →
    bitsVal v off len = bitsVal w 0 len
  | 0, _ => rfl
  | len + 1, h => by
    rw [bitsVal, bitsVal, bitsVal_congr off len (fun j hj => h j (by omega)), h len (by omega), Nat.zero_add]

/-- Columns read on the current / next row. -/
def colsC : Expr → List Nat
  | .col x false => [x]
  | .add a d | .mul a d => colsC a ++ colsC d
  | .neg a => colsC a
  | _ => []

def colsN : Expr → List Nat
  | .col x true => [x]
  | .add a d | .mul a d => colsN a ++ colsN d
  | .neg a => colsN a
  | _ => []

theorem evR_congr {cur cur' nx nx' : Nat → Fp} {fst lst : Bool} {pub : List Fp} :
    ∀ e, (∀ x ∈ colsC e, cur x = cur' x) → (∀ x ∈ colsN e, nx x = nx' x) →
      evR cur nx fst lst pub e = evR cur' nx' fst lst pub e
  | .const _, _, _ => rfl
  | .col x false, h, _ => h x (by simp [colsC])
  | .col x true, _, h => h x (by simp [colsN])
  | .pub _, _, _ => rfl
  | .isFirst, _, _ => rfl
  | .isLast, _, _ => rfl
  | .isTransition, _, _ => rfl
  | .add a d, h1, h2 => by
    simp only [evR_add]
    rw [evR_congr a (fun x hx => h1 x (by simp [colsC, hx])) (fun x hx => h2 x (by simp [colsN, hx])),
      evR_congr d (fun x hx => h1 x (by simp [colsC, hx])) (fun x hx => h2 x (by simp [colsN, hx]))]
  | .mul a d, h1, h2 => by
    simp only [evR_mul]
    rw [evR_congr a (fun x hx => h1 x (by simp [colsC, hx])) (fun x hx => h2 x (by simp [colsN, hx])),
      evR_congr d (fun x hx => h1 x (by simp [colsC, hx])) (fun x hx => h2 x (by simp [colsN, hx]))]
  | .neg a, h1, h2 => by
    simp only [evR_neg]
    rw [evR_congr a (fun x hx => h1 x (by simp [colsC, hx])) (fun x hx => h2 x (by simp [colsN, hx]))]

end RcptP
end ZkFormal.Near.Render
