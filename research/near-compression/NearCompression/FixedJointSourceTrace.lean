import NearCompression.FixedDecodedSourceTrace
namespace NearCompression
open Lean.Grind ZkFormal.Air ZkFormal.Algebra

/-- Joint PCS representatives supply the scalar degrees and proximity used
to construct a fixed base source trace. Source lanes stay tied to the same
typed oracle across eligible auxiliary choices; other lanes may change. -/
theorem fixed_joint_representative_source_trace {A : Type}
    (layout : GKRJointLayout) (metadata : List GKRSourceLane)
    (valid : ∀ lane∈metadata,lane.WellFormed layout) (geometry : CanonicalLaneSelectors layout metadata)
    (domain : List Fp8) (distinct : domain.Nodup) (basePoints : ∀ x∈domain,Fp8.IsBase x)
    (D T : Nat) (separation : 2*(domain.length-T)+D≤domain.length)
    (rowLogs sourceWidth : Nat → Nat) (indices offsets : Nat → Nat → Nat)
    (indexBound : ∀ t column,column<sourceWidth t → indices t column<metadata.length)
    (sourceOracles : Nat → Nat → Fp8 → Fp)
    (sources : A → List (Fp8 → Fp8)) (polys : A → List (Poly Fp8))
    (decoded : A → Trace Fp8) (eligible : A → Prop)
    (sourceShape : ∀ a,eligible a → (sources a).length=metadata.length)
    (representative : ∀ a,eligible a →
      JointBetaRepresentative domain (fun _=>1) (heterogeneousJointDimension layout) D T
        (metadata.map (heterogeneousJointBeta layout)) (sources a) (polys a))
    (fixedOracle : ∀ a,eligible a → ∀ t column,column<sourceWidth t →
      (sources a).getD (indices t column) (fun _ => 0)=(fun x => Fp8.ofBase (sourceOracles t column x)))
    (logs : ∀ a,eligible a → (decoded a).log=rowLogs)
    (provenance : ∀ a,eligible a → ∀ t row column,∀ hc : column<sourceWidth t,
      (decoded a).cell t row column=
        recoveredColumnValues layout.commonLog (metadata[indices t column]'(indexBound t column hc))
          (offsets t column) ((polys a).getD (indices t column) Poly.zero) row) :
    ∃ source : Trace Fp,source.log=rowLogs ∧
      ∀ a,eligible a → (decoded a).log=source.log ∧
        ∀ t row column,column<sourceWidth t →
          (decoded a).cell t row column=Fp8.ofBase (source.cell t row column) := by
  let lanes := fun t column => metadata.getD (indices t column) ⟨0,0,0,0,0,0,0⟩
  let candidates := fun a t column => (polys a).getD (indices t column) Poly.zero
  apply fixed_decoded_base_source_trace domain distinct basePoints D (domain.length-T) (by omega)
    layout.commonLog rowLogs sourceWidth lanes offsets sourceOracles candidates decoded eligible logs
  · intro a ha t column hc
    have rep := representative a ha
    have shape : (polys a).length=metadata.length := rep.1.trans (sourceShape a ha)
    have bound : indices t column<(polys a).length := by rw [shape];exact indexBound t column hc
    have degree := rep.2.1 (polys a)[indices t column] (List.getElem_mem _)
    simpa only [candidates,List.getD,List.getElem?_eq_getElem bound,Option.getD_some] using degree
  · intro a ha t column hc
    have rep := representative a ha
    have shape : (polys a).length=metadata.length := rep.1.trans (sourceShape a ha)
    have pb : indices t column<(polys a).length := by rw [shape];exact indexBound t column hc
    have sb : indices t column<(sources a).length := by rw [sourceShape a ha];exact indexBound t column hc
    have radius := joint_representative_lane_radius layout metadata valid geometry domain D T (sources a) (polys a)
      (sourceShape a ha) shape rep (indices t column) (indexBound t column hc)
    have fixed := fixedOracle a ha t column hc
    simp only [List.getD,List.getElem?_eq_getElem sb,Option.getD_some] at fixed
    rw [fixed] at radius
    simpa only [candidates,List.getD,List.getElem?_eq_getElem pb,Option.getD_some] using radius
  · intro a ha t row column hc
    have h := provenance a ha t row column hc
    simpa only [lanes,candidates,List.getD,List.getElem?_eq_getElem (indexBound t column hc),Option.getD_some] using h

end NearCompression
