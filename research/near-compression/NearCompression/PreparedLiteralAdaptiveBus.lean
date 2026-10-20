import NearCompression.BusAdaptiveAuxiliary
import NearCompression.PreparedLiteralBusSoundness

namespace NearCompression
open Lean.Grind ZkFormal.Air ZkFormal.V2 ZkFormal.Algebra ZkFormal.Near
open ArenaCore.Security ZkFormal.Udr NearSpecV3.Wasm

/-- Wrong actual Wasm output cannot gain ideal bus acceptance probability by
choosing auxiliary coordinates/finals after the challenges. Source local
validity and preparation are still explicit; cryptographic extraction and
Fiat-Shamir/quantum reductions are not supplied by this theorem. -/
theorem prepared_literal_wrong_output_adaptive_bus_bound (codeCount : Nat) (sourceWidth : Nat→Nat) (tr : Trace Fp) (pub : List Fp)
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
      (fun pair=>busAdaptiveAuxiliaryAccept (preparedLiteralAir codeCount) tr sourceWidth pub pair.1 pair.2) ≤
      busTraceErrorBudget (preparedLiteralAir codeCount) tr pub 28*sample.length := by
  have sub := count_mono_mem (sample.flatMap (fun a=>sample.map (fun g=>(a,g))))
    (E:=fun pair=>busAdaptiveAuxiliaryAccept (preparedLiteralAir codeCount) tr sourceWidth pub pair.1 pair.2)
    (F:=fun pair=>preparedLiteralBusAccept codeCount tr pub pair.1 pair.2) (by
      intro pair _ h
      have fixedSource:=bus_adaptive_auxiliary_implies_source (preparedLiteralAir codeCount) tr sourceWidth pub pair.1 pair.2 h
      simpa only [preparedLiteralBusAccept,bus_expanded_global_product,busGlobalSideProduct] using fixedSource)
  exact Nat.le_trans sub (prepared_literal_wrong_output_bus_bound codeCount tr pub locals fits
    cfg code method ctx blockLevel full eligible accepted fuel enoughFuel wrong sample distinct)

end NearCompression
