import WasmBase.Local.ShiftSem
/-!
# WasmBase.Local.ShiftBytes — byte-chain arithmetic for the SHIFT chip (generic in the length)

`bsum f n` is the little-endian base-256 value of `f 0 .. f (n-1)`.  A byte chain
`pw · m_j + cy_{j-1} = p_j + 256 · cy_j` telescopes (`bsum_tele`); with `m_j = A_{j-t}` it computes
`p = (A · pw · 256^t) mod 256^n` (`chain_prod`).  `byte_disjoint` is the no-carry fact for rotations.
-/
namespace WasmBase.Local
set_option linter.unusedSimpArgs false

def bsum (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => bsum f n + f n * 256 ^ n

theorem bsum_lt (f : Nat → Nat) (n : Nat) (h : ∀ j, j < n → f j < 256) : bsum f n < 256 ^ n := by
  induction n with
  | zero => simp [bsum]
  | succ n ih =>
    simp only [bsum]
    have h1 := ih (fun j hj => h j (by omega))
    have h2 : f n * 256 ^ n ≤ 255 * 256 ^ n := Nat.mul_le_mul_right _ (by have := h n (by omega); omega)
    rw [Nat.pow_succ]; omega

theorem bsum_congr {f g : Nat → Nat} {n : Nat} (h : ∀ j, j < n → f j = g j) : bsum f n = bsum g n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [bsum]; rw [ih (fun j hj => h j (by omega)), h n (by omega)]

theorem bsum_zero_of {f : Nat → Nat} {n : Nat} (h : ∀ j, j < n → f j = 0) : bsum f n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [bsum]; rw [ih (fun j hj => h j (by omega)), h n (by omega)]; simp

theorem bsum_split (f : Nat → Nat) (k m : Nat) :
    bsum f (k + m) = bsum f k + 256 ^ k * bsum (fun j => f (k + j)) m := by
  induction m with
  | zero => simp [bsum]
  | succ m ih =>
    rw [← Nat.add_assoc]; simp only [bsum]; rw [ih, Nat.pow_add]
    grind

theorem bsum_mod (f : Nat → Nat) (n k : Nat) (hk : k ≤ n) (hf : ∀ j, j < n → f j < 256) :
    bsum f n % 256 ^ k = bsum f k := by
  obtain ⟨m, rfl⟩ : ∃ m, n = k + m := ⟨n - k, by omega⟩
  rw [bsum_split, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (bsum_lt f k (fun j hj => hf j (by omega)))]

/-- The carry chain telescopes. -/
theorem bsum_tele (pw : Nat) (m p cy : Nat → Nat) (n : Nat)
    (h : ∀ j, j < n → pw * m j + (if j = 0 then 0 else cy (j - 1)) = p j + 256 * cy j) :
    bsum p n + 256 ^ n * (if n = 0 then 0 else cy (n - 1)) = pw * bsum m n := by
  induction n with
  | zero => simp [bsum]
  | succ n ih =>
    have ih' := ih (fun j hj => h j (by omega))
    have hn := h n (by omega)
    simp only [bsum, Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel]
    have e : 256 ^ n * (pw * m n + (if n = 0 then 0 else cy (n - 1))) = 256 ^ n * (p n + 256 * cy n) := by
      rw [hn]
    rw [Nat.pow_succ]
    grind

/-- `m_j = A_{j-t}` (zero below `t`): the shifted sum. -/
theorem bsum_shift (A : Nat → Nat) (t : Nat) : ∀ n, t ≤ n →
    bsum (fun j => if t ≤ j then A (j - t) else 0) n = 256 ^ t * bsum A (n - t) := by
  intro n
  induction n with
  | zero => intro h; have : t = 0 := by omega
            subst this; simp [bsum]
  | succ n ih =>
    intro h
    by_cases htn : t ≤ n
    · simp only [bsum]
      rw [ih htn, show n + 1 - t = (n - t) + 1 by omega]
      simp only [bsum, htn, ite_true]
      rw [show 256 ^ n = 256 ^ t * 256 ^ (n - t) by rw [← Nat.pow_add]; congr 1; omega]
      grind
    · have ht : t = n + 1 := by omega
      subst ht
      rw [Nat.sub_self, show bsum A 0 = 0 from rfl, Nat.mul_zero]
      exact bsum_zero_of (fun j hj => by simp only [show ¬(n + 1 ≤ j) by omega, ite_false])

/-- `(pw · 256^t · (X mod 256^(n-t))) mod 256^n = (X · (pw · 256^t)) mod 256^n`. -/
theorem shifted_mod (pw t n X : Nat) (htn : t ≤ n) :
    (pw * 256 ^ t * (X % 256 ^ (n - t))) % 256 ^ n = (X * (pw * 256 ^ t)) % 256 ^ n := by
  have h1 : 256 ^ t * (X % 256 ^ (n - t)) = (256 ^ t * X) % 256 ^ n := by
    rw [show 256 ^ n = 256 ^ t * 256 ^ (n - t) by rw [← Nat.pow_add]; congr 1; omega, Nat.mul_mod_mul_left]
  rw [Nat.mul_assoc, h1, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.mul_assoc, Nat.mul_comm X]

/-- **The byte chain computes the shifted product.** -/
theorem chain_prod (pw t n : Nat) (A p cy : Nat → Nat) (htn : t ≤ n)
    (hp : ∀ j, j < n → p j < 256) (hA : ∀ j, j < n → A j < 256)
    (h : ∀ j, j < n → pw * (if t ≤ j then A (j - t) else 0) + (if j = 0 then 0 else cy (j - 1)) =
      p j + 256 * cy j) :
    bsum p n = (bsum A n * (pw * 256 ^ t)) % 256 ^ n := by
  have T := bsum_tele pw _ p cy n h
  rw [bsum_shift A t n htn, ← bsum_mod A n (n - t) (by omega) hA, ← Nat.mul_assoc] at T
  rw [← shifted_mod pw t n _ htn, ← T, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt (bsum_lt p n hp)]

theorem pow256 (k : Nat) : (256 : Nat) ^ k = 2 ^ (8 * k) := by
  rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]

/-! ## Rotations: low and high halves have disjoint bits, so byte sums do not carry -/

theorem byte_disjoint (lo hi k m : Nat) (hlo : lo % 2 ^ k = 0) (hhi : hi < 2 ^ k) :
    lo / 2 ^ m % 256 + hi / 2 ^ m % 256 < 256 := by
  have h256 : (256 : Nat) = 2 ^ 8 := rfl
  by_cases h1 : k ≤ m
  · have : hi / 2 ^ m = 0 := Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hhi (Nat.pow_le_pow_right (by decide) h1))
    rw [this]; simp only [Nat.zero_mod, Nat.add_zero]; exact Nat.mod_lt _ (by decide)
  · by_cases h2 : m + 8 ≤ k
    · -- lo / 2^m is a multiple of 2^8
      obtain ⟨q, hq⟩ : ∃ q, lo = 2 ^ k * q := ⟨lo / 2 ^ k, (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hlo)).symm⟩
      have : lo / 2 ^ m % 256 = 0 := by
        rw [hq, show 2 ^ k = 2 ^ m * (2 ^ 8 * 2 ^ (k - m - 8)) by
          rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; omega]
        rw [Nat.mul_assoc, Nat.mul_div_cancel_left _ (Nat.two_pow_pos m), h256, Nat.mul_assoc,
          Nat.mul_mod_right]
      rw [this, Nat.zero_add]; exact Nat.mod_lt _ (by decide)
    · -- 0 < k - m < 8: the low byte of `lo / 2^m` is a multiple of `2^(k-m)`, that of `hi` is below it
      have hd : k - m < 8 := by omega
      obtain ⟨q, hq⟩ : ∃ q, lo = 2 ^ k * q := ⟨lo / 2 ^ k, (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hlo)).symm⟩
      have e1 : lo / 2 ^ m = 2 ^ (k - m) * q := by
        rw [hq, show 2 ^ k = 2 ^ m * 2 ^ (k - m) by rw [← Nat.pow_add]; congr 1; omega, Nat.mul_assoc,
          Nat.mul_div_cancel_left _ (Nat.two_pow_pos m)]
      have e2 : hi / 2 ^ m < 2 ^ (k - m) := by
        rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos m), ← Nat.pow_add, show k - m + m = k by omega]; exact hhi
      rw [e1]
      have hmod : 2 ^ (k - m) * q % 256 = 2 ^ (k - m) * (q % 2 ^ (8 - (k - m))) := by
        rw [h256, show 2 ^ 8 = 2 ^ (k - m) * 2 ^ (8 - (k - m)) by rw [← Nat.pow_add]; congr 1; omega,
          Nat.mul_mod_mul_left]
      have e3 : hi / 2 ^ m < 256 := by
        have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show k - m ≤ 8 by omega)
        rw [h256]; omega
      rw [hmod, Nat.mod_eq_of_lt e3]
      have hq' : q % 2 ^ (8 - (k - m)) + 1 ≤ 2 ^ (8 - (k - m)) := Nat.mod_lt _ (Nat.two_pow_pos _)
      have : 2 ^ (k - m) * (q % 2 ^ (8 - (k - m)) + 1) ≤ 2 ^ (k - m) * 2 ^ (8 - (k - m)) :=
        Nat.mul_le_mul_left _ hq'
      rw [← Nat.pow_add, show k - m + (8 - (k - m)) = 8 by omega, Nat.mul_add, Nat.mul_one] at this
      omega

end WasmBase.Local
