import ZkFormal.Algebra.Fp

/-! Kernel-checked constants for the executable X^12-31 candidate.
These discharge base-field nonresidue and Frobenius-constant obligations.
They do not yet prove irreducibility of X^12-31 or refine the Rust arithmetic. -/
namespace NearCompression
open Lean.Grind ZkFormal.Algebra

theorem ext12_degree_divides : 12 * ((P - 1) / 12) = P - 1 := by decide

theorem ext12_nonresidue_nonzero : (31 : Fp) ≠ 0 := by decide +kernel

theorem ext12_nonresidue_half : (31 : Fp) ^ ((P - 1) / 2) = -1 := by
  decide +kernel

theorem ext12_nonresidue_third_ne_one : (31 : Fp) ^ ((P - 1) / 3) ≠ 1 := by
  decide +kernel

theorem ext12_nonresidue_nonsquare (x : Fp) : x * x ≠ 31 := by
  intro h
  have hx : x ≠ 0 := by intro hz; rw [hz] at h; exact absurd h (by decide +kernel)
  have he : (31 : Fp) ^ ((P - 1) / 2) = 1 := by
    rw [← h, ← pow_two_mul, show 2 * ((P - 1) / 2) = P - 1 by decide,
      Fp.pow_card_sub_one hx]
  exact Fp.neg_one_ne_one (ext12_nonresidue_half ▸ he)

theorem ext12_nonresidue_noncube (x : Fp) : x ^ 3 ≠ 31 := by
  intro h
  have hx : x ≠ 0 := by intro hz; rw [hz] at h; exact absurd h (by decide +kernel)
  apply ext12_nonresidue_third_ne_one
  rw [← h, ← pow_mul_eq, show 3 * ((P - 1) / 3) = P - 1 by decide,
    Fp.pow_card_sub_one hx]

theorem ext12_frobenius_constant : (31 : Fp) ^ ((P - 1) / 12) = 782862608 := by
  decide +kernel

theorem ext12_root29_coefficient : (31 : Fp) ^ 3 = 29791 := by decide +kernel
theorem ext12_root28_coefficient : (31 : Fp) ^ 7 = 1340157138 := by decide +kernel

end NearCompression
