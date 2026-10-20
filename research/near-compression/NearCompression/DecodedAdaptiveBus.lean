import NearCompression.DecodedBaseTrace
import NearCompression.PreparedLiteralAdaptiveBus
namespace NearCompression
open Lean.Grind ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ArenaCore.Security

/-- A later decoded coordinate trace with fixed source columns projects to
exactly an allowed auxiliary attachment to that source trace. Auxiliary
coordinates may vary freely with the bus challenges. -/
theorem decoded_base_trace_attached (source : Trace Fp) (sourceWidth : Nat → Nat)
    (decoded : Trace Fp8) (logs : decoded.log=source.log)
    (fixed : ∀ t row column,column<sourceWidth t →
      decoded.cell t row column=Fp8.ofBase (source.cell t row column)) :
    decodedBaseTrace decoded=busAttachAuxiliary source sourceWidth
      (fun t row column => (decoded.cell t row column).c0) := by
  cases source with
  | mk sourceLog sourceCell =>
    cases decoded with
    | mk decodedLog decodedCell =>
      simp only at logs fixed
      cases logs
      unfold decodedBaseTrace busAttachAuxiliary
      congr 1
      funext t row column
      by_cases live : column<sourceWidth t
      · simp only [live,ite_true,fixed t row column live,Fp8.ofBase]
      · simp only [live,ite_false]

/-- A fixed source expression has the same lifted value in every decoded
auxiliary attachment. Thus a source violation cannot disappear when earlier
bus challenges change the auxiliary columns. -/
theorem fixed_source_decoded_expression (source : Trace Fp) (sourceWidth : Nat → Nat)
    (decoded : Trace Fp8) (logs : decoded.log=source.log)
    (fixed : ∀ t row column,column<sourceWidth t →
      decoded.cell t row column=Fp8.ofBase (source.cell t row column))
    (t row : Nat) (pub : List Fp) (e : Expr) (bound : e.colBound≤sourceWidth t) :
    e.eval decoded t row (pub.map Fp8.ofBase)=Fp8.ofBase (e.eval source t row pub) := by
  have base : ∀ r column,column<sourceWidth t → Fp8.IsBase (decoded.cell t r column) := by
    intro r column hc
    rw [fixed t r column hc]
    exact (Fp8.isBase_iff _).mpr ⟨source.cell t r column,rfl⟩
  rw [decoded_base_trace_source_eval decoded t row (sourceWidth t) pub base e bound,
    decoded_base_trace_attached source sourceWidth decoded logs fixed,
    bus_attached_source_eval source sourceWidth _ t row pub e bound]

/-- Transport one prechallenge nonzero source residual to each later decoded
witness. Only columns referenced by that residual must be source columns. -/
theorem fixed_source_decoded_nonzero (source : Trace Fp) (sourceWidth : Nat → Nat)
    (decoded : Trace Fp8) (logs : decoded.log=source.log)
    (fixed : ∀ t row column,column<sourceWidth t →
      decoded.cell t row column=Fp8.ofBase (source.cell t row column))
    (t row : Nat) (pub : List Fp) (e : Expr) (bound : e.colBound≤sourceWidth t)
    (wrong : e.eval source t row pub≠0) :
    e.eval decoded t row (pub.map Fp8.ofBase)≠0 := by
  rw [fixed_source_decoded_expression source sourceWidth decoded logs fixed t row pub e bound]
  intro zero
  exact wrong (Fp8.ofBase_inj zero)

/-- Residual validity on reconstructed coordinates of the decoded trace
implies the existing adaptive-auxiliary bus event for the same fixed source.
This does not infer residual validity from a PCS opening alone. -/
theorem decoded_bus_implies_adaptive_accept (air : AirP) (source : Trace Fp) (sourceWidth : Nat → Nat)
    (decoded : Trace Fp8) (logs : decoded.log=source.log)
    (fixed : ∀ t row column,column<sourceWidth t →
      decoded.cell t row column=Fp8.ofBase (source.cell t row column))
    (pubValues : List Fp) (alpha gamma : Fp8) (finals : Nat → Nat → Fp8)
    (holds : busExt8TablesResidualsZero (decodedBaseTrace decoded) sourceWidth
      pubValues alpha gamma finals air.tables 0)
    (equal : busExt8ClaimedSideProduct air (decodedBaseTrace decoded) sourceWidth pubValues alpha gamma finals true=
      busExt8ClaimedSideProduct air (decodedBaseTrace decoded) sourceWidth pubValues alpha gamma finals false) :
    busAdaptiveAuxiliaryAccept air source sourceWidth pubValues alpha gamma := by
  have same := decoded_base_trace_attached source sourceWidth decoded logs fixed
  rw [same] at holds equal
  exact ⟨(fun t row column => (decoded.cell t row column).c0),finals,holds,equal⟩

/-- Adversarial decoded coordinates/finals can be selected separately after
each bus challenge pair. Fixed source cells prevent that adaptivity from
changing the source-side bus fingerprint event or its ideal error bound. -/
theorem decoded_adaptive_bus_error_bound (air : AirP) (source : Trace Fp) (sourceWidth : Nat → Nat)
    (pubValues : List Fp) (width : Nat)
    (sourceBounds : ∀ table∈air.tables,∀ i∈table.interactions,i.bus<P-1 ∧ i.msg.length+1≤width)
    (publicBounds : ∀ record∈pubMsgs air pubValues,record.1<P-1 ∧ record.2.2.length+1≤width)
    (unbalanced : ¬∀ b m,busCount air.toAir source pubValues b true m+pubCount air pubValues b true m=
      busCount air.toAir source pubValues b false m+pubCount air pubValues b false m)
    (sample : List Fp8) (distinct : sample.Nodup) (accept : Fp8 → Fp8 → Prop)
    (decodedWitness : ∀ alpha∈sample,∀ gamma∈sample,accept alpha gamma →
      ∃ decoded : Trace Fp8,∃ finals : Nat → Nat → Fp8,
        decoded.log=source.log ∧
        (∀ t row column,column<sourceWidth t → decoded.cell t row column=Fp8.ofBase (source.cell t row column)) ∧
        busExt8TablesResidualsZero (decodedBaseTrace decoded) sourceWidth pubValues alpha gamma finals air.tables 0 ∧
        busExt8ClaimedSideProduct air (decodedBaseTrace decoded) sourceWidth pubValues alpha gamma finals true=
          busExt8ClaimedSideProduct air (decodedBaseTrace decoded) sourceWidth pubValues alpha gamma finals false) :
    count (sample.flatMap (fun alpha => sample.map (fun gamma => (alpha,gamma))))
      (fun pair => accept pair.1 pair.2)≤busTraceErrorBudget air source pubValues width*sample.length := by
  apply Nat.le_trans (count_mono_mem _ ?_)
    (bus_adaptive_auxiliary_fp8_bound air source sourceWidth pubValues width sourceBounds publicBounds unbalanced sample distinct)
  intro pair member accepted
  simp only [List.mem_flatMap,List.mem_map] at member
  obtain ⟨alpha,ha,gamma,hg,rfl⟩ := member
  obtain ⟨decoded,finals,logs,fixed,holds,equal⟩ := decodedWitness alpha ha gamma hg accepted
  exact decoded_bus_implies_adaptive_accept air source sourceWidth decoded logs fixed pubValues alpha gamma finals holds equal

end NearCompression
