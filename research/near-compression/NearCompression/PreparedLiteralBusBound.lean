import NearCompression.BusTraceMass
import NearCompression.PreparedLiteral

namespace NearCompression
open Lean.Grind ZkFormal.Air ZkFormal.V2 ZkFormal.Algebra ArenaCore.Security ZkFormal.Udr

/-- Literal descriptors use buses0..3 and at most27 payload fields. -/
theorem prepared_literal_bus_source_shape (count : Nat) :
    ∀ table∈(preparedLiteralAir count).tables,∀ i∈table.interactions,
      i.bus<P-1 ∧ i.msg.length+1≤28 := by
  change ∀ table∈(preparedLiteralAir 0).tables,∀ i∈table.interactions,_
  decide

private theorem record_length (seg : PubSeg) (pub : List Fp) (j : Nat) :
    (seg.record pub j).length=seg.messageWidth := by
  unfold PubSeg.record PubSeg.messageWidth
  cases seg.indexBase <;> simp <;> omega

/-- Public boundaries and CODE records have the same static tag/width limits
for any public vector, not only well-formed or honest witness headers. -/
theorem prepared_literal_bus_public_shape (count : Nat) (pub : List Fp) :
    ∀ record∈pubMsgs (preparedLiteralAir count) pub,
      record.1<P-1 ∧ record.2.2.length+1≤28 := by
  have segments : ∀ seg∈(preparedLiteralAir count).pubSegs,seg.bus<P-1 ∧ seg.messageWidth+1≤28 := by
    change ∀ seg∈(preparedLiteralAir 0).pubSegs,_
    decide
  intro record member
  unfold pubMsgs at member
  obtain ⟨seg,hs,hm⟩:=List.mem_flatMap.mp member
  obtain ⟨message,hmessage,rfl⟩:=List.mem_map.mp hm
  unfold PubSeg.msgs at hmessage
  obtain ⟨j,_,rfl⟩:=List.mem_map.mp hmessage
  have bounds:=segments seg hs
  simpa only [record_length] using bounds

/-- Literal slice bus soundness for one fixed trace. Descriptor/public shape,
support coverage and natural multiplicity bounds are all discharged. -/
theorem prepared_literal_bus_joint_bound (count : Nat) (tr : Trace Fp) (pub : List Fp)
    (unbalanced : ¬∀ b m,busCount (preparedLiteralAir count).toAir tr pub b true m+
      pubCount (preparedLiteralAir count) pub b true m=
      busCount (preparedLiteralAir count).toAir tr pub b false m+pubCount (preparedLiteralAir count) pub b false m)
    (sample : List Fp8) (distinct : sample.Nodup) :
    let encode := busEncodeMessage Fp8.ofBase (fun b=>((b+1:Nat):Fp8))
    let send := (busTraceMessages (preparedLiteralAir count) tr pub true).map encode
    let receive := (busTraceMessages (preparedLiteralAir count) tr pub false).map encode
    ArenaCore.Security.count (sample.flatMap (fun a=>sample.map (fun g=>(a,g))))
      (fun pair=>((send.map (fp pair.1)).map (pair.2 - ·)).prod =
                  ((receive.map (fp pair.1)).map (pair.2 - ·)).prod) ≤
      busTraceErrorBudget (preparedLiteralAir count) tr pub 28*sample.length := by
  exact bus_trace_budget_fp8_bound (preparedLiteralAir count) tr pub 28
    (prepared_literal_bus_source_shape count) (prepared_literal_bus_public_shape count pub)
    unbalanced sample distinct

end NearCompression
