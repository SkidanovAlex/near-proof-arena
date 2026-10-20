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

namespace WasmBase

theorem val8_horner (b : Nat → Nat) :
    val8 b = b 0 + 2 ^ 8 * (b 1 + 2 ^ 8 * (b 2 + 2 ^ 8 * (b 3 + 2 ^ 8 * (b 4 + 2 ^ 8 * (b 5 +
      2 ^ 8 * (b 6 + 2 ^ 8 * b 7)))))) := by
  simp only [val8, Nat.reducePow]; omega

/-- A bitwise operation acts byte by byte. -/
theorem byteop_split (f : Bool → Bool → Bool) (op : Nat → Nat → Nat)
    (hop : ∀ x y i, (op x y).testBit i = f (x.testBit i) (y.testBit i))
    (a b A B : Nat) (ha : a < 2 ^ 8) (hb : b < 2 ^ 8) (hab : op a b < 2 ^ 8) :
    op (a + 2 ^ 8 * A) (b + 2 ^ 8 * B) = op a b + 2 ^ 8 * op A B := by
  rw [Nat.add_comm a, Nat.add_comm b, Nat.add_comm (op a b)]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [hop, Nat.testBit_two_pow_mul_add _ ha, Nat.testBit_two_pow_mul_add _ hb,
    Nat.testBit_two_pow_mul_add _ hab]
  split <;> simp [hop]

theorem val8_byteop (f : Bool → Bool → Bool) (op : Nat → Nat → Nat)
    (hop : ∀ x y i, (op x y).testBit i = f (x.testBit i) (y.testBit i))
    (a b r : Nat → Nat) (ha : ∀ k, k < 8 → a k < 2 ^ 8) (hb : ∀ k, k < 8 → b k < 2 ^ 8)
    (hr : ∀ k, k < 8 → r k = op (a k) (b k)) (hlt : ∀ k, k < 8 → op (a k) (b k) < 2 ^ 8) :
    op (val8 a) (val8 b) = val8 r := by
  rw [val8_horner, val8_horner, val8_horner]
  have s := byteop_split f op hop
  rw [s _ _ _ _ (ha 0 (by decide)) (hb 0 (by decide)) (hlt 0 (by decide)),
    s _ _ _ _ (ha 1 (by decide)) (hb 1 (by decide)) (hlt 1 (by decide)),
    s _ _ _ _ (ha 2 (by decide)) (hb 2 (by decide)) (hlt 2 (by decide)),
    s _ _ _ _ (ha 3 (by decide)) (hb 3 (by decide)) (hlt 3 (by decide)),
    s _ _ _ _ (ha 4 (by decide)) (hb 4 (by decide)) (hlt 4 (by decide)),
    s _ _ _ _ (ha 5 (by decide)) (hb 5 (by decide)) (hlt 5 (by decide)),
    s _ _ _ _ (ha 6 (by decide)) (hb 6 (by decide)) (hlt 6 (by decide)),
    hr 0 (by decide), hr 1 (by decide), hr 2 (by decide), hr 3 (by decide), hr 4 (by decide),
    hr 5 (by decide), hr 6 (by decide), hr 7 (by decide)]

theorem and_byte {a b : Nat} (ha : a < 2 ^ 8) : a &&& b < 2 ^ 8 := Nat.lt_of_le_of_lt Nat.and_le_left ha
theorem or_byte {a b : Nat} (ha : a < 2 ^ 8) (hb : b < 2 ^ 8) : a ||| b < 2 ^ 8 := Nat.or_lt_two_pow ha hb
theorem xor_byte {a b : Nat} (ha : a < 2 ^ 8) (hb : b < 2 ^ 8) : a ^^^ b < 2 ^ 8 := Nat.xor_lt_two_pow ha hb

end WasmBase

namespace WasmBase
theorem val4_bytes (b : Nat → Nat) :
    val4 (b 0 + 256 * b 1) (b 2 + 256 * b 3) (b 4 + 256 * b 5) (b 6 + 256 * b 7) = val8 b := by
  simp only [val4, val8, Nat.reducePow]; omega

/-- The BYTE table's function of kind `K`. -/
def byteF (K x y : Nat) : Nat :=
  if K = 1 then x &&& y else if K = 2 then x ||| y else if K = 3 then x ^^^ y else 0
end WasmBase
