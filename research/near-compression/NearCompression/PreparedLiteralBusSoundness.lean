import NearCompression.PreparedLiteralBusBound
import NearCompression.PreparedExecFinalRow

namespace NearCompression
open Lean.Grind ZkFormal.Air ZkFormal.V2 ZkFormal.Algebra ZkFormal.Near
open ArenaCore.Security ZkFormal.Udr NearSpecV3.Wasm

noncomputable def preparedLiteralBusAccept (codeCount : Nat) (tr : Trace Fp) (pub : List Fp)
    (alpha gamma : Fp8) : Prop :=
  let encode := busEncodeMessage Fp8.ofBase (fun b=>((b+1:Nat):Fp8))
  let side := fun s=>(busTraceMessages (preparedLiteralAir codeCount) tr pub s).map encode
  (((side true).map (fp alpha)).map (gamma - ·)).prod =
    (((side false).map (fp alpha)).map (gamma - ·)).prod

/-- A false published outcome for actual runCall can pass the ideal bus check
only within the derived budget, provided the same fixed trace satisfies all
local constraints. Local/PCS/source extraction and QROM are not proved here. -/
theorem prepared_literal_wrong_output_bus_bound (codeCount : Nat) (tr : Trace Fp) (pub : List Fp)
    (locals : ∀ t (ht : t<(preparedLiteralAir codeCount).tables.length),
      TableLocal (preparedLiteralAir codeCount).tables[t] tr t pub)
    (fits : pubFit (preparedLiteralAir codeCount) pub=true)
    (cfg : NearCfg) (code : ByteArray) (method : String) (ctx : CallCtx)
    (blockLevel full : Bool) (eligible : PreparedRunCallEligible)
    (accepted : preparedLiteralRunCallCheck cfg code method ctx pub blockLevel=some eligible)
    (fuel : Nat) (enoughFuel : tr.height 0≤fuel)
    (wrong : ¬∃ final error,runCall cfg code method ctx fuel blockLevel full none=.done final error ∧
      PreparedExecPublishedOutput pub final error)
    (sample : List Fp8) (distinct : sample.Nodup) :
    count (sample.flatMap (fun a=>sample.map (fun g=>(a,g))))
      (fun pair=>preparedLiteralBusAccept codeCount tr pub pair.1 pair.2) ≤
      busTraceErrorBudget (preparedLiteralAir codeCount) tr pub 28*sample.length := by
  have unbalanced : ¬∀ b m,busCount (preparedLiteralAir codeCount).toAir tr pub b true m+
      pubCount (preparedLiteralAir codeCount) pub b true m=
      busCount (preparedLiteralAir codeCount).toAir tr pub b false m+pubCount (preparedLiteralAir codeCount) pub b false m := by
    intro balance
    have holds : HoldsP (preparedLiteralAir codeCount) pub tr := {
      logBound:=fun t ht=>⟨(locals t ht).log_ge,(locals t ht).log_le⟩
      constr:=fun t ht=>(locals t ht).constr
      bits:=fun t ht=>(locals t ht).bits
      pubFit:=fits
      balance:=balance}
    obtain ⟨w,actual,published⟩:=prepared_literal_public_run_call codeCount tr pub holds cfg code method ctx
      blockLevel full eligible accepted fuel enoughFuel
    exact wrong ⟨w.final,w.error,actual,published⟩
  simpa only [preparedLiteralBusAccept] using
    prepared_literal_bus_joint_bound codeCount tr pub unbalanced sample distinct

end NearCompression
