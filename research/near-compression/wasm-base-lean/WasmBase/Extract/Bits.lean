import WasmBase.Prelude

namespace WasmBase
theorem bitop_split_n (n : Nat) (f : Bool → Bool → Bool) (op : Nat → Nat → Nat)
    (hop : ∀ x y i, (op x y).testBit i = f (x.testBit i) (y.testBit i))
    (a b A B : Nat) (ha : a < 2 ^ n) (hb : b < 2 ^ n) (hab : op a b < 2 ^ n) :
    op (a + 2 ^ n * A) (b + 2 ^ n * B) = op a b + 2 ^ n * op A B := by
  rw [Nat.add_comm a, Nat.add_comm b, Nat.add_comm (op a b)]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [hop, Nat.testBit_two_pow_mul_add _ ha, Nat.testBit_two_pow_mul_add _ hb,
    Nat.testBit_two_pow_mul_add _ hab]
  split <;> simp [hop]

/-- 8 bits packed little-endian. -/
def bits8 (x : Nat → Nat) : Nat :=
  x 0 + 2 * (x 1 + 2 * (x 2 + 2 * (x 3 + 2 * (x 4 + 2 * (x 5 + 2 * (x 6 + 2 * x 7))))))

theorem bits8_lt (x : Nat → Nat) (hx : ∀ i, i < 8 → x i ≤ 1) : bits8 x < 256 := by
  have := hx 0 (by decide); have := hx 1 (by decide); have := hx 2 (by decide); have := hx 3 (by decide)
  have := hx 4 (by decide); have := hx 5 (by decide); have := hx 6 (by decide); have := hx 7 (by decide)
  simp only [bits8]; omega

theorem bits8_op (f : Bool → Bool → Bool) (op : Nat → Nat → Nat)
    (hop : ∀ x y i, (op x y).testBit i = f (x.testBit i) (y.testBit i))
    (hbit : ∀ a b, a ≤ 1 → b ≤ 1 → op a b ≤ 1)
    (x y : Nat → Nat) (hx : ∀ i, i < 8 → x i ≤ 1) (hy : ∀ i, i < 8 → y i ≤ 1) :
    op (bits8 x) (bits8 y) = bits8 (fun i => op (x i) (y i)) := by
  have s := bitop_split_n 1 f op hop
  simp only [bits8, Nat.pow_one] at *
  have h : ∀ i, i < 8 → x i < 2 ∧ y i < 2 ∧ op (x i) (y i) < 2 := fun i hi =>
    ⟨by have := hx i hi; omega, by have := hy i hi; omega, by have := hbit (x i) (y i) (hx i hi) (hy i hi); omega⟩
  rw [s _ _ _ _ (h 0 (by decide)).1 (h 0 (by decide)).2.1 (h 0 (by decide)).2.2,
    s _ _ _ _ (h 1 (by decide)).1 (h 1 (by decide)).2.1 (h 1 (by decide)).2.2,
    s _ _ _ _ (h 2 (by decide)).1 (h 2 (by decide)).2.1 (h 2 (by decide)).2.2,
    s _ _ _ _ (h 3 (by decide)).1 (h 3 (by decide)).2.1 (h 3 (by decide)).2.2,
    s _ _ _ _ (h 4 (by decide)).1 (h 4 (by decide)).2.1 (h 4 (by decide)).2.2,
    s _ _ _ _ (h 5 (by decide)).1 (h 5 (by decide)).2.1 (h 5 (by decide)).2.2,
    s _ _ _ _ (h 6 (by decide)).1 (h 6 (by decide)).2.1 (h 6 (by decide)).2.2]

theorem and_bit {a b : Nat} (ha : a ≤ 1) (hb : b ≤ 1) : a &&& b = a * b := by
  rcases (show a = 0 ∨ a = 1 by omega) with rfl | rfl <;> rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl <;> rfl
theorem or_bit {a b : Nat} (ha : a ≤ 1) (hb : b ≤ 1) : a ||| b = a + b - a * b := by
  rcases (show a = 0 ∨ a = 1 by omega) with rfl | rfl <;> rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl <;> rfl
theorem xor_bit {a b : Nat} (ha : a ≤ 1) (hb : b ≤ 1) : a ^^^ b = a + b - 2 * (a * b) := by
  rcases (show a = 0 ∨ a = 1 by omega) with rfl | rfl <;> rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl <;> rfl
end WasmBase
