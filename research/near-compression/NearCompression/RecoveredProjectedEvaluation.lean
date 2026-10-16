import NearCompression.ProjectedSourceRecovery
namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

/-- Exact sparse storage at every index, including trailing zero coefficients. -/
theorem sparse_lift_polynomial_coefficient (k n i : Nat) (cs : List K)
    (shape : cs.length≤2^n) :
    (sparseLiftPolynomial k n cs).coeff i=
      if 2^k∣i then cs.getD (i/2^k) 0 else 0 := by
  by_cases bound : i<2^(k+n)
  · have read : (sparseLiftPolynomial k n cs).coeff i=sparseLowLift k (fun j=>cs.getD j 0) i := by
      simp [sparseLiftPolynomial,coefficientPolynomial,Poly.coeff,List.getD,bound]
    rw [read]
    have decomp : 2^k*(i/2^k)+i%2^k=i := Nat.div_add_mod i (2^k)
    have h := sparse_lift_block k (fun j=>cs.getD j 0) (i/2^k) (i%2^k) (Nat.mod_lt _ (Nat.two_pow_pos _))
    rw [decomp] at h
    rw [h]
    simp only [Nat.dvd_iff_mod_eq_zero]
  · have high : cs.length≤i/2^k := by
      have prod : 2^k*2^n≤i := by rw [←Nat.pow_add];omega
      have div : 2^n≤i/2^k := (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).mpr (by simpa [Nat.mul_comm] using prod)
      omega
    have zero : (sparseLiftPolynomial k n cs).coeff i=0 := by
      apply Poly.getD_ge_length
      simp only [sparseLiftPolynomial,coefficientPolynomial,List.length_map,List.length_range]
      omega
    rw [zero,Poly.getD_ge_length cs _ high]
    split <;> rfl

/-- The recovered polynomial reproduces the original common-domain candidate
under the actual sparse coefficient storage used by the prover. -/
theorem recovered_projected_sparse_storage (k n : Nat) (p : Poly K)
    (degree : p.DegLt (2^k*2^n))
    (sparse : ∀i,¬2^k∣i → p.coeff i=0) (i : Nat) :
    p.coeff i=(sparseLiftPolynomial k n (recoverProjectedPolynomial (2^k) (2^n) p).coeffs).coeff i := by
  rw [sparse_lift_polynomial_coefficient k n i _ (by simp [recoverProjectedPolynomial])]
  exact recovered_projected_coefficients (2^k) (2^n) (Nat.two_pow_pos _) p degree sparse i

/-- Evaluation identity for the recovered original-degree witness, at every
field point. No honest-source premise or nonzero-point restriction. -/
theorem recovered_projected_evaluation (k n : Nat) (p : Poly K)
    (degree : p.DegLt (2^k*2^n))
    (sparse : ∀i,¬2^k∣i → p.coeff i=0) (x : K) :
    p.eval x=(recoverProjectedPolynomial (2^k) (2^n) p).eval (x^(2^k)) := by
  let q := sparseLiftPolynomial k n (recoverProjectedPolynomial (2^k) (2^n) p).coeffs
  have zero : (p - q).IsZero := by
    intro i
    rw [Poly.coeff_sub,recovered_projected_sparse_storage k n p degree sparse i]
    grind
  have eq := Poly.eval_of_isZero zero x
  rw [Poly.eval_sub] at eq
  have same : p.eval x=q.eval x := by grind
  rw [same]
  exact sparse_lift_polynomial_eval k n _ (by simp [recoverProjectedPolynomial]) x
end NearCompression
