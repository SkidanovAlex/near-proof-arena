import NearCompression.SourceAcrossAuxiliary
import NearCompression.DecodedAdaptiveBus
namespace NearCompression
open Lean.Grind ZkFormal.Air ZkFormal.Algebra

/-- Assemble a single base source trace from decoded polynomial provenance.
All eligible auxiliary choices share it. Domain/source typing, scalar
proximity and fixed row geometry are explicit; no commitment extraction is
claimed. The source exists even if no auxiliary choice has a representative. -/
theorem fixed_decoded_base_source_trace {A : Type}
    (domain : List Fp8) (distinct : domain.Nodup) (basePoints : ∀ x∈domain,Fp8.IsBase x)
    (D radius : Nat) (separation : radius+radius+D≤domain.length)
    (C : Nat) (rowLogs sourceWidth : Nat → Nat)
    (lanes : Nat → Nat → GKRSourceLane) (offsets : Nat → Nat → Nat)
    (sources : Nat → Nat → Fp8 → Fp)
    (candidates : A → Nat → Nat → Poly Fp8) (decoded : A → Trace Fp8) (eligible : A → Prop)
    (logs : ∀ a,eligible a → (decoded a).log=rowLogs)
    (degree : ∀ a,eligible a → ∀ t column,column<sourceWidth t → (candidates a t column).DegLt D)
    (close : ∀ a,eligible a → ∀ t column,column<sourceWidth t →
      finiteRSMismatches domain (fun x => Fp8.ofBase (sources t column x)) (candidates a t column).eval≤radius)
    (provenance : ∀ a,eligible a → ∀ t row column,column<sourceWidth t →
      (decoded a).cell t row column=
        recoveredColumnValues C (lanes t column) (offsets t column) (candidates a t column) row) :
    ∃ source : Trace Fp,source.log=rowLogs ∧
      ∀ a,eligible a → (decoded a).log=source.log ∧
        ∀ t row column,column<sourceWidth t →
          (decoded a).cell t row column=Fp8.ofBase (source.cell t row column) := by
  classical
  by_cases any : ∃ a,eligible a
  · obtain ⟨anchor,ha⟩ := any
    refine ⟨decodedBaseTrace (decoded anchor),logs anchor ha,?_⟩
    intro a he
    refine ⟨(logs a he).trans (logs anchor ha).symm,?_⟩
    intro t row column hc
    have zero := finite_rs_unique_candidate domain distinct (fun x => Fp8.ofBase (sources t column x))
      (candidates a t column) (candidates anchor t column) D radius radius
      (degree a he t column hc) (degree anchor ha t column hc)
      (close a he t column hc) (close anchor ha t column hc) separation
    have same := recovered_column_coefficient_congr C (lanes t column) (offsets t column)
      (candidates a t column) (candidates anchor t column) (by
        intro i
        have h := zero i
        rw [Poly.coeff_sub] at h
        grind)
    have coeffBase : ∀ i,Fp8.IsBase ((candidates anchor t column).coeff i) := by
      apply fp8_polynomial_base_descent domain distinct (fun x => Fp8.ofBase (sources t column x)) basePoints
        (fun x _ => (Fp8.isBase_iff _).mpr ⟨sources t column x,rfl⟩)
        (candidates anchor t column) D (degree anchor ha t column hc)
      have partition := finite_rs_agreement_partition domain (fun x => Fp8.ofBase (sources t column x))
        (candidates anchor t column).eval
      have proximity := close anchor ha t column hc
      omega
    have cellBase : Fp8.IsBase ((decoded anchor).cell t row column) := by
      rw [provenance anchor ha t row column hc]
      exact fp8_recovered_column_base C (lanes t column) (offsets t column) (candidates anchor t column) coeffBase row
    rw [provenance a he t row column hc,congrFun same row,←provenance anchor ha t row column hc]
    exact (decoded_base_trace_cell (decoded anchor) t row column cellBase).symm
  · refine ⟨⟨rowLogs,fun _ _ _ => 0⟩,rfl,?_⟩
    intro a ha
    exact False.elim (any ⟨a,ha⟩)

/-- Once the preceding construction supplies fixed cells, every later
residual-valid decoded witness feeds the bus acceptance predicate on that
same source trace. Auxiliary choices remain inside the quantifier. -/
theorem fixed_source_decoded_bus_family {A : Type}
    (air : ZkFormal.V2.AirP) (source : Trace Fp) (sourceWidth : Nat → Nat)
    (decoded : A → Trace Fp8) (eligible : A → Prop)
    (binding : ∀ a,eligible a → (decoded a).log=source.log ∧
      ∀ t row column,column<sourceWidth t → (decoded a).cell t row column=Fp8.ofBase (source.cell t row column))
    (pubValues : List Fp) (alpha gamma : A → Fp8) (finals : A → Nat → Nat → Fp8)
    (holds : ∀ a,eligible a → busExt8TablesResidualsZero (decodedBaseTrace (decoded a)) sourceWidth
      pubValues (alpha a) (gamma a) (finals a) air.tables 0)
    (equal : ∀ a,eligible a →
      busExt8ClaimedSideProduct air (decodedBaseTrace (decoded a)) sourceWidth pubValues (alpha a) (gamma a) (finals a) true=
      busExt8ClaimedSideProduct air (decodedBaseTrace (decoded a)) sourceWidth pubValues (alpha a) (gamma a) (finals a) false) :
    ∀ a,eligible a → busAdaptiveAuxiliaryAccept air source sourceWidth pubValues (alpha a) (gamma a) := by
  intro a ha
  exact decoded_bus_implies_adaptive_accept air source sourceWidth (decoded a) (binding a ha).1
    (binding a ha).2 pubValues (alpha a) (gamma a) (finals a) (holds a ha) (equal a ha)

end NearCompression
