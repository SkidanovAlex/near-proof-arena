import WasmBase.Air
/-!
# WasmBase.Prelude — from field equations to natural-number facts

Every trace cell is a BabyBear element `x`; we reason about its canonical representative
`x.toNat < P`.  A constraint `E = 0` over cells whose Nat values are bounded turns into an exact
equation of naturals when both sides stay below `P` (`natEq`).
-/
namespace WasmBase
open ZkFormal.Algebra

theorem Fp.cast_toNat (x : Fp) : ((x.toNat : Nat) : Fp) = x := Fp.ofNat_toNat x

theorem Fp.toNat_cast (n : Nat) : ((n : Fp)).toNat = n % P := Fp.toNat_ofNat n

theorem Fp.toNat_cast_of_lt {n : Nat} (h : n < P) : ((n : Fp)).toNat = n := by
  rw [Fp.toNat_cast, Nat.mod_eq_of_lt h]

/-- Exact equality of naturals from equality of their casts (both below `P`). -/
theorem natEq {L R : Nat} (h : (L : Fp) = (R : Fp)) (hL : L < P) (hR : R < P) : L = R := by
  have := congrArg Fp.toNat h
  rwa [Fp.toNat_cast_of_lt hL, Fp.toNat_cast_of_lt hR] at this

theorem cast_inj_iff {L R : Nat} (hL : L < P) (hR : R < P) : (L : Fp) = (R : Fp) ↔ L = R :=
  ⟨fun h => natEq h hL hR, fun h => h ▸ rfl⟩

theorem P_val : P = 2013265921 := rfl

/-- A boolean field element. -/
theorem bool_cases {x : Fp} (h : x * (x - 1) = 0) : x = 0 ∨ x = 1 := by grind

theorem mul_eq_zero' {x y : Fp} (h : x * y = 0) : x = 0 ∨ y = 0 := by grind

theorem toNat_of_eq_zero {x : Fp} (h : x = 0) : x.toNat = 0 := by rw [h]; rfl
theorem toNat_of_eq_one {x : Fp} (h : x = 1) : x.toNat = 1 := by rw [h]; rfl

theorem eq_of_toNat {x : Fp} {n : Nat} (h : x.toNat = n) : x = (n : Fp) := by
  rw [← h, Fp.cast_toNat]

theorem cast_zero : ((0 : Nat) : Fp) = 0 := rfl
theorem cast_one : ((1 : Nat) : Fp) = 1 := rfl

/-- Little-endian value of four 16-bit limbs. -/
def val4 (l0 l1 l2 l3 : Nat) : Nat := l0 + 65536 * l1 + 2 ^ 32 * l2 + 2 ^ 48 * l3

/-- Little-endian value of eight bytes. -/
def val8 (b : Nat → Nat) : Nat :=
  b 0 + 256 * b 1 + 2 ^ 16 * b 2 + 2 ^ 24 * b 3 + 2 ^ 32 * b 4 + 2 ^ 40 * b 5 + 2 ^ 48 * b 6 + 2 ^ 56 * b 7

end WasmBase

namespace WasmBase
open ZkFormal.Algebra

theorem bool_nat {n : Nat} (hn : n < P) (h : (n : Fp) * ((n : Fp) - ((1 : Nat) : Fp)) = 0) :
    n = 0 ∨ n = 1 := by
  rcases bool_cases (x := (n : Fp)) h with h0 | h1
  · exact Or.inl (natEq h0 hn (by decide))
  · exact Or.inr (natEq h1 hn (by decide))

/-- `x · y = 0` with `x` the cast of a natural `< P`. -/
theorem zero_of_mul_nat {x y : Nat} (hx : x < P) (hy : y < P) (h : (x : Fp) * (y : Fp) = 0) :
    x = 0 ∨ y = 0 := by
  rcases mul_eq_zero' h with h | h
  · exact Or.inl (natEq (h.trans rfl) hx (by decide))
  · exact Or.inr (natEq (h.trans rfl) hy (by decide))

/-- `(1 - s) · y = 0` with `s ∈ {0,1}`. -/
theorem zero_of_sel0 {y : Nat} (hy : y < P) (h : (((1 : Nat) : Fp) - ((0 : Nat) : Fp)) * (y : Fp) = 0) :
    y = 0 := by
  have : (y : Fp) = ((0 : Nat) : Fp) := by grind
  exact natEq this hy (by decide)

end WasmBase

/-- Push `Nat.cast` through `+`, `*` and close a ring equation in `F_p`. -/
macro "fp_ring" : tactic =>
  `(tactic| (simp only [Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_mul]; grind))
