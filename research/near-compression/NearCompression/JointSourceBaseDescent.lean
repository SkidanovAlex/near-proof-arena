import NearCompression.ProjectedRSDomain
import NearCompression.BaseFieldPolynomialDescent
import NearCompression.FixedJointSourceRepresentative
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security

/-- Source leaves carry base-field scalars; extension-field weighting happens
only after this embedding. This type does not itself authenticate a Merkle root. -/
def fp8TypedSourceOracles (sources : List (Fp8 → Fp)) : List (Fp8 → Fp8) :=
  sources.map (fun source => fun x => Fp8.ofBase (source x))

/-- Universal joint agreement supplies enough scalar agreement for base-field
descent of each lane of the SAME representative tuple. -/
theorem fp8_joint_representative_base (layout : GKRJointLayout) (metadata : List GKRSourceLane)
    (valid : ∀ lane∈metadata,lane.WellFormed layout) (geometry : CanonicalLaneSelectors layout metadata)
    (domain : List Fp8) (distinct : domain.Nodup) (basePoints : ∀ x∈domain,Fp8.IsBase x)
    (D T : Nat) (threshold : T≤domain.length) (enough : D≤T)
    (sources : List (Fp8 → Fp8)) (polys : List (Poly Fp8))
    (sourceShape : sources.length=metadata.length)
    (baseValues : ∀ i,∀ hi : i<sources.length,∀ x∈domain,Fp8.IsBase (sources[i] x))
    (representative : JointBetaRepresentative domain (fun _ => 1) (heterogeneousJointDimension layout) D T
      (metadata.map (heterogeneousJointBeta layout)) sources polys)
    (i : Nat) (hi : i<metadata.length) :
    ∀ j,Fp8.IsBase ((polys[i]'(by have shape:=representative.1;omega)).coeff j) := by
  have polyShape : polys.length=metadata.length := representative.1.trans sourceShape
  have radius := joint_representative_lane_radius layout metadata valid geometry domain D T sources polys
    sourceShape polyShape representative i hi
  have partition := finite_rs_agreement_partition domain sources[i] polys[i].eval
  apply fp8_polynomial_base_descent domain distinct sources[i] basePoints
    (baseValues i (by omega)) polys[i] D (representative.2.1 _ (List.getElem_mem _))
  omega

/-- Typed source functions discharge full-domain base-valuedness algebraically.
Relating these functions to adversarial committed bytes remains the source
oracle authentication/refinement obligation. -/
theorem fp8_typed_joint_recovered_base (layout : GKRJointLayout) (metadata : List GKRSourceLane)
    (valid : ∀ lane∈metadata,lane.WellFormed layout) (geometry : CanonicalLaneSelectors layout metadata)
    (domain : List Fp8) (distinct : domain.Nodup) (basePoints : ∀ x∈domain,Fp8.IsBase x)
    (D T : Nat) (threshold : T≤domain.length) (enough : D≤T)
    (sources : List (Fp8 → Fp)) (polys : List (Poly Fp8))
    (sourceShape : sources.length=metadata.length)
    (representative : JointBetaRepresentative domain (fun _ => 1) (heterogeneousJointDimension layout) D T
      (metadata.map (heterogeneousJointBeta layout)) (fp8TypedSourceOracles sources) polys)
    (i : Nat) (hi : i<metadata.length) (offset row : Nat) :
    Fp8.IsBase (recoveredColumnValues layout.commonLog metadata[i] offset
      (polys[i]'(by have shape:=representative.1; simp only [fp8TypedSourceOracles,List.length_map] at shape;omega)) row) := by
  have shape : (fp8TypedSourceOracles sources).length=metadata.length := by
    simpa only [fp8TypedSourceOracles,List.length_map] using sourceShape
  have baseValues : ∀ j,∀ hj : j<(fp8TypedSourceOracles sources).length,
      ∀ x∈domain,Fp8.IsBase ((fp8TypedSourceOracles sources)[j] x) := by
    intro j hj x hx
    have hj' : j<sources.length := by simpa only [fp8TypedSourceOracles,List.length_map] using hj
    apply (Fp8.isBase_iff _).mpr
    refine ⟨sources[j] x,?_⟩
    exact congrArg (fun f => f x) (List.getElem_map (fun source : Fp8 → Fp => fun y => Fp8.ofBase (source y)) (l:=sources) (i:=j))
  have polyShape : polys.length=metadata.length := representative.1.trans shape
  exact fp8_recovered_column_base layout.commonLog metadata[i] offset polys[i]
    (fp8_joint_representative_base layout metadata valid geometry domain distinct basePoints D T threshold enough
      (fp8TypedSourceOracles sources) polys shape baseValues representative i hi) row

/-- The native multiplicative source domain uses a base-field root. Every
point therefore satisfies the descent theorem's domain condition. -/
theorem fp8_natural_domain_base (omega : Fp) (N : Nat) :
    ∀ x∈naturalRSDomain (Fp8.ofBase omega) N,Fp8.IsBase x := by
  have powers : ∀ i : Nat,(Fp8.ofBase omega)^i=Fp8.ofBase (omega^i) := by
    intro i
    induction i with
    | zero => rfl
    | succ i ih => rw [Semiring.pow_succ,Semiring.pow_succ,ih,Fp8.ofBase_mul]
  intro x hx
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
  exact (Fp8.isBase_iff _).mpr ⟨omega^i,powers i⟩

end NearCompression
