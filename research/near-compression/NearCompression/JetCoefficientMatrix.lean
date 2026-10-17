import NearCompression.SyntheticJetLinear

namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

/-- The formal monomial X^n, with a canonical coefficient list. -/
def jetMonomial (n : Nat) : Poly K :=
  Poly.mk ((List.range (n+1)).map (fun i=>if i=n then (1:K) else 0))

theorem jet_monomial_coefficient (n i : Nat) : (jetMonomial n : Poly K).coeff i=if i=n then 1 else 0 := by
  by_cases hi : i<n+1
  · simp [jetMonomial,Poly.coeff,List.getD,hi]
  · have different : i≠n := by omega
    simp [jetMonomial,Poly.coeff,List.getD,hi,different]

private def combination (indices : List Nat) (values : Nat→K) : Poly K :=
  match indices with
  | [] => Poly.zero
  | n::rest => Poly.smul (values n) (jetMonomial n)+combination rest values

private theorem combination_coeff (indices : List Nat) (values : Nat→K) (i : Nat) :
    (combination indices values).coeff i=kernelDot indices (fun n=>if i=n then 1 else 0) values := by
  induction indices with
  | nil => simp [combination,Poly.zero,Poly.coeff,kernelDot]
  | cons n rest ih =>
    simp only [combination,Poly.coeff_add,Poly.coeff_smul,jet_monomial_coefficient,kernelDot,ih]
    grind

private theorem dot_delta (indices : List Nat) (distinct : indices.Nodup) (values : Nat→K) (i : Nat) :
    kernelDot indices (fun n=>if i=n then 1 else 0) values=if i∈indices then values i else 0 := by
  induction indices with
  | nil => simp [kernelDot]
  | cons n rest ih =>
    have nd:=List.nodup_cons.mp distinct
    rw [kernelDot,ih nd.2]
    by_cases same : i=n
    · subst n;simp only [ite_true,nd.1,ite_false,List.mem_cons_self];grind
    · by_cases member : i∈rest <;> simp [same,member] <;> grind

private theorem combination_reconstruct (p : Poly K) :
    PolynomialCoeffEq (combination (List.range p.coeffs.length) p.coeff) p := by
  intro i
  rw [combination_coeff,dot_delta _ List.nodup_range]
  by_cases inside : i<p.coeffs.length
  · simp [List.mem_range,inside]
  · have zero:=Poly.degLt_length p i (by omega)
    simp [List.mem_range,inside,zero]

private theorem combination_jet (indices : List Nat) (values : Nat→K) (a : K) (r : Nat) :
    syntheticJet (combination indices values) a r=
      kernelDot indices (fun n=>syntheticJet (jetMonomial n) a r) values := by
  induction indices with
  | nil =>
    change syntheticJet Poly.zero a r=0
    have h:=synthetic_jet_sum ([] : List (Poly K)) a r
    exact h
  | cons n rest ih =>
    simp only [combination,synthetic_jet_add,synthetic_jet_scale,kernelDot,ih]
    grind

/-- A concrete matrix row computes the r-th jet of ANY coefficient vector.
Entries are jets of monomials; no linearity or matrix-correctness premise. -/
theorem synthetic_jet_coefficient_matrix (p : Poly K) (a : K) (r : Nat) :
    syntheticJet p a r=kernelDot (List.range p.coeffs.length)
      (fun n=>syntheticJet (jetMonomial n) a r) p.coeff := by
  rw [←synthetic_jet_congr _ p (combination_reconstruct p) a r]
  exact combination_jet _ _ a r

/-- Direct row-vector form used for canonically encoded interpolation rows. -/
theorem synthetic_jet_vector_matrix (n : Nat) (values : Nat→K) (a : K) (r : Nat) :
    syntheticJet (Poly.mk ((List.range n).map values)) a r=
      kernelDot (List.range n) (fun i=>syntheticJet (jetMonomial i) a r) values := by
  rw [synthetic_jet_coefficient_matrix]
  simp only [List.length_map,List.length_range]
  have equal : ∀ indices : List Nat,(∀ i∈indices,i<n)→
      kernelDot indices (fun i=>syntheticJet (jetMonomial i) a r)
        (Poly.mk ((List.range n).map values)).coeff=
      kernelDot indices (fun i=>syntheticJet (jetMonomial i) a r) values := by
    intro indices
    induction indices with
    | nil => intro h;rfl
    | cons i rest ih =>
      intro bounds
      have hi:=bounds i (by simp)
      have head : (Poly.mk ((List.range n).map values)).coeff i=values i := by
        simp [Poly.coeff,List.getD,hi]
      have tail:=ih (fun j hj=>bounds j (by simp [hj]))
      simp only [kernelDot,head,tail]
  exact equal _ (fun i hi=>List.mem_range.mp hi)
end NearCompression
