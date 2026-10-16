import NearCompression.TrivariateSpecialization

namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

/-- Enough agreement on distinct source abscissae forces a formal root.
The translation/substitution separation premise remains explicit. -/
theorem gs_specialization_root_forcing
    (sources : List (K×K×K)) (m k DX height DZ : Nat)
    (values : (Nat×Nat×Nat)→K)
    (identities : ∀ source∈sources,∀ r s,r+s<m→
      (trivariateJetPolynomial (gsTrivariateMonomials k DX height DZ) values r s
        source.1 source.2.1 source.2.2).IsZero)
    (z : K) (curve : Poly K) (curveDegree : curve.DegLt (k+1))
    (support : List K) (distinct : support.Nodup)
    (agreement : ∀ x∈support,∃ u v,(x,u,v)∈sources ∧ curve.eval x=u+z*v)
    (enough : DX≤(support.map (fun _=>m)).sum)
    (sample : List K) (sampleDistinct : sample.Nodup)
    (separation : ∀ a∈support,
      max (polynomialTranslate (bivariateSubstitute
        (gsSpecialization k DX height DZ values z) curve) a).coeffs.length
        (bivariateSubstitute (bivariateTranslate
          (gsSpecialization k DX height DZ values z) a (curve.eval a))
          (centeredCurve curve a)).coeffs.length≤sample.length) :
    (bivariateSubstitute (gsSpecialization k DX height DZ values z) curve).IsZero := by
  apply bivariate_weighted_multiplicity_zero _ curve k DX curveDegree
    (gs_specialization_degree k DX height DZ values z) support distinct (fun _=>m)
    enough sample sampleDistinct separation
  intro x hx
  obtain ⟨u,v,member,equal⟩:=agreement x hx
  rw [equal]
  exact gs_specialization_constraints k DX height DZ values sources m identities z (x,u,v) member

/-- One vector works for all Z. The exception count bounds ONLY total
annihilation; useful-factor/Hensel analysis is still required. -/
theorem gs_interpolation_specialization_certificate
    (sources : List (K×K×K)) (m k DX height DZ : Nat)
    (dimension : sources.length*((List.range m).map (fun s=>(m-s)*(DZ-s))).sum<
      ((List.range height).map (fun j=>(DX-k*j)*(DZ-j))).sum) :
    ∃ values : (Nat×Nat×Nat)→K,
      (∃ index∈gsTrivariateMonomials k DX height DZ,values index≠0) ∧
      (∀ source∈sources,∀ r s,r+s<m→
        (trivariateJetPolynomial (gsTrivariateMonomials k DX height DZ) values r s
          source.1 source.2.1 source.2.2).IsZero) ∧
      (∀ z,BivariateWeightedDegree (gsSpecialization k DX height DZ values z) k DX ∧
        ∀ source∈sources,BivariateOrder (bivariateTranslate
          (gsSpecialization k DX height DZ values z) source.1 (source.2.1+z*source.2.2)) m) ∧
      (∀ sample : List K,sample.Nodup→
        count sample (fun z=>∀ i j,
          ((gsSpecialization k DX height DZ values z).getD j Poly.zero).coeff i=0)≤DZ-1) := by
  obtain ⟨values,nonzero,identities⟩:=gs_trivariate_interpolant_exists sources m k DX height DZ dimension
  refine ⟨values,nonzero,identities,?_,?_⟩
  · intro z
    exact ⟨gs_specialization_degree k DX height DZ values z,
      gs_specialization_constraints k DX height DZ values sources m identities z⟩
  · intro sample distinct
    exact gs_zero_specialization_count k DX height DZ values nonzero sample distinct
end NearCompression
