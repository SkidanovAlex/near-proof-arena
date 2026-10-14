import Std

/-!
Exact arithmetic only. No theorem here proves a quantum attack bound.
Fractions are represented by integer numerators and positive denominators.
The caller must establish the cryptographic bound, constants and resources.
-/
namespace HashRecursion

set_option maxRecDepth 4096
set_option exponentiation.threshold 1024

/-- n/d ≤ 2^-bits, without division or rounding. -/
def Meets (n d bits : Nat) : Prop := 0 < d ∧ n * 2 ^ bits ≤ d

/-- Two independently justified error bounds, on arbitrary denominators,
compose with one reserved security bit per component. -/
theorem meets_add {a b d e bits : Nat}
    (ha : Meets a d (bits + 1)) (hb : Meets b e (bits + 1)) :
    Meets (a * e + b * d) (d * e) bits := by
  refine ⟨Nat.mul_pos ha.1 hb.1, ?_⟩
  have h1 := Nat.mul_le_mul_right e ha.2
  have h2 := Nat.mul_le_mul_right d hb.2
  simp only [Nat.pow_succ] at h1 h2
  have h1' : (a * e * 2 ^ bits) * 2 ≤ d * e := by
    simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h1
  have h2' : (b * d * 2 ^ bits) * 2 ≤ d * e := by
    simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h2
  rw [Nat.add_mul]
  omega

/-- Conditional cubic-query template C*q^3/2^n, with C=2^c and q=2^qBits.
This is NOT a formalization of a quantum collision theorem. -/
theorem cubic_budget (c qBits n bits : Nat)
    (h : c + 3 * qBits + bits ≤ n) :
    Meets (2 ^ c * (2 ^ qBits) ^ 3) (2 ^ n) bits := by
  refine ⟨Nat.pow_pos (by decide), ?_⟩
  rw [← Nat.pow_mul, ← Nat.pow_add, ← Nat.pow_add]
  apply Nat.pow_le_pow_right (by decide)
  omega

/-- An abstract reduction multiplier 2^lossBits applied to base error 2^-base.
The actual multi-round Fiat–Shamir loss must be proved separately. -/
theorem reduction_budget (lossBits base bits : Nat) (h : lossBits + bits ≤ base) :
    Meets (2 ^ lossBits) (2 ^ base) bits := by
  refine ⟨Nat.pow_pos (by decide), ?_⟩
  rw [← Nat.pow_add]
  exact Nat.pow_le_pow_right (by decide) h

/-- A reduction that loses a factor 2^lossBits consumes that many bits from
an already established inner bound. -/
theorem meets_amplify {n d bits lossBits : Nat}
    (h : Meets n d (bits + lossBits)) :
    Meets (2 ^ lossBits * n) d bits := by
  refine ⟨h.1, ?_⟩
  have hh := h.2
  rw [Nat.pow_add] at hh
  simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hh

private theorem scaled_sum (ns : List Nat) (scale : Nat) :
    ns.sum * scale = (ns.map (fun n => n * scale)).sum := by
  induction ns with
  | nil => simp
  | cons n ns ih => simp [Nat.add_mul, ih]

private theorem sum_bound (ns : List Nat) (bound : Nat)
    (h : ∀ n ∈ ns, n ≤ bound) : ns.sum ≤ ns.length * bound := by
  induction ns with
  | nil => simp
  | cons n ns ih =>
    have hn := h n (by simp)
    have ht := ih (fun m hm => h m (by simp [hm]))
    simp only [List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- At most 2^slack error terms, each bounded at bits+slack on a common
denominator, meet the total bits budget. No independence is assumed.
The probability union/reduction bound that supplies these terms is external. -/
theorem meets_sum {ns : List Nat} {d bits slack : Nat}
    (hd : 0 < d) (hlen : ns.length ≤ 2 ^ slack)
    (h : ∀ n ∈ ns, Meets n d (bits + slack)) : Meets ns.sum d bits := by
  refine ⟨hd, ?_⟩
  have hs : ns.sum * 2 ^ (bits + slack) ≤ ns.length * d := by
    rw [scaled_sum]
    have hb := sum_bound (ns.map (fun n => n * 2 ^ (bits + slack))) d (by
      intro m hm
      obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hm
      exact (h n hn).2)
    simpa using hb
  have ht := Nat.le_trans hs (Nat.mul_le_mul_right d hlen)
  rw [Nat.pow_add, ← Nat.mul_assoc, Nat.mul_comm (2 ^ slack) d] at ht
  exact Nat.le_of_mul_le_mul_right ht (Nat.pow_pos (by decide))

/-- A coefficient-free template at q=2^128 and n=512 uses the ENTIRE
2^-128 budget. There is no remaining allowance for other errors. -/
theorem cubic_512_at_128 :
    (2 ^ 128 : Nat) ^ 3 * 2 ^ 128 = 2 ^ 512 := by
  rw [← Nat.pow_mul, ← Nat.pow_add]

/-- At q=2^64, n=384, the same template meets 2^-192. -/
theorem cubic_384_at_64 : Meets ((2 ^ 64) ^ 3) (2 ^ 384) 192 := by
  constructor <;> decide

/-- 384 output bits do not give failure ≤2^-128 at 2^128 queries under
the cubic template, even with coefficient one. -/
theorem cubic_384_not_128_at_128 :
    ¬ Meets ((2 ^ 128) ^ 3) (2 ^ 384) 128 := by
  unfold Meets
  decide

/-- Repeating the same 128-bit bound twice cannot preserve that budget. -/
theorem two_full_budgets_fail : ¬ Meets 2 (2 ^ 128) 128 := by
  unfold Meets
  decide

end HashRecursion
