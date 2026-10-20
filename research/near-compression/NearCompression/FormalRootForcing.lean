import NearCompression.FormalTranslation
import NearCompression.CurveRootPreservation

namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

/-- Mixed multiplicity transfers to the substituted polynomial at ANY center;
no finite evaluation domain or polynomial storage-length bound is needed. -/
theorem formal_substitution_at_center (rows : List (Poly K)) (curve : Poly K)
    (a : K) (m : Nat)
    (mixed : BivariateOrder (bivariateTranslate rows a (curve.eval a)) m) :
    ∀ i<m,syntheticJet (bivariateSubstitute rows curve) a i=0 := by
  have through : (centeredCurve curve a).coeff 0=0 := by
    rw [centeredCurve,Poly.coeff_sub,polynomial_translate_coeff]
    change curve.eval a-(Poly.C (curve.eval a)).coeff 0=0
    simp only [Poly.C,Poly.coeff,List.getD,List.getElem?_cons_zero,Option.getD_some]
    grind
  have order:=bivariate_substitution_order m (bivariateTranslate rows a (curve.eval a))
    (centeredCurve curve a) through mixed
  intro i hi
  rw [←polynomial_translate_coeff,bivariate_translation_substitution]
  exact order i hi

/-- Weighted root forcing over every field, with no separation guard. -/
theorem formal_weighted_multiplicity_zero (rows : List (Poly K)) (curve : Poly K)
    (k D : Nat) (curveDegree : curve.DegLt (k+1))
    (weighted : BivariateWeightedDegree rows k D)
    (centers : List K) (distinct : centers.Nodup) (multiplicity : K→Nat)
    (total : D≤(centers.map multiplicity).sum)
    (mixed : ∀ a∈centers,BivariateOrder (bivariateTranslate rows a (curve.eval a)) (multiplicity a)) :
    (bivariateSubstitute rows curve).IsZero := by
  have jets : ∀ a∈centers,∀ i<multiplicity a,syntheticJet (bivariateSubstitute rows curve) a i=0 := by
    intro a ha
    exact formal_substitution_at_center rows curve a (multiplicity a) (mixed a ha)
  apply Classical.byContradiction
  intro nonzero
  have bound:=synthetic_multipoint_bound centers distinct multiplicity D
    (bivariateSubstitute rows curve) (bivariate_substitution_degree rows curve k D curveDegree weighted) nonzero jets
  omega

/-- Trivariate interpolation agreement-to-root step without any field-size guard. -/
theorem formal_specialization_root_forcing
    (sources : List (K×K×K)) (m k DX height DZ : Nat)
    (values : (Nat×Nat×Nat)→K)
    (identities : ∀ source∈sources,∀ r s,r+s<m→
      (trivariateJetPolynomial (gsTrivariateMonomials k DX height DZ) values r s
        source.1 source.2.1 source.2.2).IsZero)
    (z : K) (curve : Poly K) (curveDegree : curve.DegLt (k+1))
    (support : List K) (distinct : support.Nodup)
    (agreement : ∀ x∈support,∃ u v,(x,u,v)∈sources ∧ curve.eval x=u+z*v)
    (enough : DX≤(support.map (fun _=>m)).sum) :
    (bivariateSubstitute (gsSpecialization k DX height DZ values z) curve).IsZero := by
  apply formal_weighted_multiplicity_zero _ curve k DX curveDegree
    (gs_specialization_degree k DX height DZ values z) support distinct (fun _=>m) enough
  intro x hx
  obtain ⟨u,v,member,equal⟩:=agreement x hx
  rw [equal]
  exact gs_specialization_constraints k DX height DZ values sources m identities z (x,u,v) member

/-- Every pairwise formally distinct eligible candidate list at a nonzero
specialization has length≤height-1. Nonzero specialization is essential;
this does not bound the full MCA exception set. -/
theorem formal_specialization_candidate_count
    (sources : List (K×K×K)) (m k DX height DZ : Nat)
    (values : (Nat×Nat×Nat)→K)
    (identities : ∀ source∈sources,∀ r s,r+s<m→
      (trivariateJetPolynomial (gsTrivariateMonomials k DX height DZ) values r s
        source.1 source.2.1 source.2.2).IsZero)
    (z : K)
    (nonzero : ∃ i j,((gsSpecialization k DX height DZ values z).getD j Poly.zero).coeff i≠0)
    (curves : List (Poly K))
    (distinct : curves.Pairwise (fun f g=>¬PolynomialCoeffEq g f))
    (degrees : ∀ curve∈curves,curve.DegLt (k+1))
    (eligible : ∀ curve∈curves,∃ support : List K,support.Nodup ∧
      (∀ x∈support,∃ u v,(x,u,v)∈sources ∧ curve.eval x=u+z*v) ∧
      DX≤(support.map (fun _=>m)).sum) :
    curves.length≤height-1 := by
  have roots : ∀ curve∈curves,
      (bivariateSubstitute (gsSpecialization k DX height DZ values z) curve).IsZero := by
    intro curve member
    obtain ⟨support,nd,agreement,enough⟩:=eligible curve member
    exact formal_specialization_root_forcing sources m k DX height DZ values identities z
      curve (degrees curve member) support nd agreement enough
  have bound:=bivariate_curve_root_count curves distinct (gsSpecialization k DX height DZ values z) nonzero roots
  simpa only [gsSpecialization,gsEncode,List.length_map,List.length_range] using bound
end NearCompression
