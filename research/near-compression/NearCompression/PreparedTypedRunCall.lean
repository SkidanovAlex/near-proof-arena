import NearCompression.PreparedTypedRunCallCheck
import NearCompression.PreparedTypedRun
import NearCompression.PreparedTypedEntry

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 NearSpecV3.Wasm

/-- Actual callEntry from real setup and public entry-gas checking. No
initial state relation or initial gas equality is supplied by the caller. -/
theorem prepared_typed_call_entry_indexed (codeCount count : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedTypedLiteralAir codeCount count) pub tr)
    (cfg : NearCfg) (bytes : ByteArray) (method : String) (ctx : CallCtx) (blockLevel : Bool)
    (eligible : PreparedRunCallEligible)
    (accepted : preparedTypedSetupCheck count cfg bytes method ctx pub blockLevel=some eligible)
    (entryCheck : preparedExecEntryCheck eligible.setup.program eligible.setup.methodIndex eligible.func eligible.setup.host pub=true)
    (fuel : Nat) (enoughFuel : tr.height 0≤fuel) :
    ∃ witness:PreparedTypedTerminalWitness cfg eligible.setup.program tr eligible.func count (preparedControlRootLabel eligible.func),
      witness.frame.fn=eligible.setup.methodIndex-eligible.setup.program.m.imports.size ∧
      callEntry cfg eligible.setup.program fuel eligible.setup.host eligible.setup.methodIndex=.ok (witness.final,witness.error) := by
  obtain ⟨entry,state,context,active,_⟩:=prepared_typed_setup_enter codeCount count tr pub holds
    cfg bytes method ctx blockLevel eligible accepted entryCheck
  obtain ⟨witness,_,indexEq,executed⟩:=prepared_typed_execution_run_indexed codeCount count tr pub holds cfg bytes method ctx blockLevel eligible accepted
    fuel 0 (preparedWasmEntryState eligible.setup.program eligible.setup.methodIndex eligible.func eligible.setup.host)
    (preparedWasmEntryFrame eligible.setup.program eligible.setup.methodIndex eligible.func) 0
    (preparedControlRootLabel eligible.func) (Nat.two_pow_pos _) (by simpa using enoughFuel) active state rfl context
  refine ⟨witness,indexEq,?_⟩
  change (match (match enter eligible.setup.program (preparedWasmHostReset eligible.setup.host) eligible.setup.methodIndex with
    | .cont s=>run cfg eligible.setup.program fuel s | r=>r) with
    | .fin s=>(sync s).map (·,none)
    | .abort s e=>(sync s).map (·,some e)
    | .unmodeled why=>.error why
    | .cont _=>.error "cont")=_
  simp only [entry]
  rw [executed]
  unfold PreparedTypedTerminalWitness.result
  cases err:witness.error <;> simp only [witness.synced,Except.map]


theorem prepared_typed_call_entry (codeCount count : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedTypedLiteralAir codeCount count) pub tr)
    (cfg : NearCfg) (bytes : ByteArray) (method : String) (ctx : CallCtx) (blockLevel : Bool)
    (eligible : PreparedRunCallEligible)
    (accepted : preparedTypedSetupCheck count cfg bytes method ctx pub blockLevel=some eligible)
    (entryCheck : preparedExecEntryCheck eligible.setup.program eligible.setup.methodIndex eligible.func eligible.setup.host pub=true)
    (fuel : Nat) (enoughFuel : tr.height 0≤fuel) :
    ∃ witness:PreparedTypedTerminalWitness cfg eligible.setup.program tr eligible.func count (preparedControlRootLabel eligible.func),
      callEntry cfg eligible.setup.program fuel eligible.setup.host eligible.setup.methodIndex=.ok (witness.final,witness.error) := by
  obtain ⟨w,_,called⟩:=prepared_typed_call_entry_indexed codeCount count tr pub holds cfg bytes method ctx blockLevel eligible accepted entryCheck fuel enoughFuel
  exact ⟨w,called⟩

/-- Literal AIR plus executable setup/CODE/header checks proves an actual
outer runCall outcome. This does not yet identify its final state with every
published output field; terminal padding/output decoding is a separate layer. -/
theorem prepared_typed_run_call_indexed (codeCount count : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedTypedLiteralAir codeCount count) pub tr)
    (cfg : NearCfg) (code : ByteArray) (method : String) (ctx : CallCtx)
    (blockLevel full : Bool) (eligible : PreparedRunCallEligible)
    (accepted : preparedTypedRunCallCheck count cfg code method ctx pub blockLevel=some eligible)
    (fuel : Nat) (enoughFuel : tr.height 0≤fuel) :
    ∃ witness:PreparedTypedTerminalWitness cfg eligible.setup.program tr eligible.func count (preparedControlRootLabel eligible.func),
      witness.frame.fn=eligible.setup.methodIndex-eligible.setup.program.m.imports.size ∧
      runCall cfg code method ctx fuel blockLevel full none=.done witness.final witness.error := by
  obtain ⟨codeCheck,entry⟩:=prepared_typed_run_call_checked count cfg code method ctx pub blockLevel eligible accepted
  obtain ⟨setup,fetch,checked⟩:=prepared_typed_setup_checked count cfg code method ctx pub blockLevel eligible codeCheck
  obtain ⟨witness,indexEq,body⟩:=prepared_typed_call_entry_indexed codeCount count tr pub holds cfg code method ctx blockLevel eligible codeCheck entry fuel enoughFuel
  exact ⟨witness,indexEq,prepared_run_call_setup_sound cfg code method ctx blockLevel full eligible.setup setup
    fuel witness.final witness.error body⟩

theorem prepared_typed_run_call (codeCount count : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedTypedLiteralAir codeCount count) pub tr)
    (cfg : NearCfg) (code : ByteArray) (method : String) (ctx : CallCtx)
    (blockLevel full : Bool) (eligible : PreparedRunCallEligible)
    (accepted : preparedTypedRunCallCheck count cfg code method ctx pub blockLevel=some eligible)
    (fuel : Nat) (enoughFuel : tr.height 0≤fuel) :
    ∃ witness:PreparedTypedTerminalWitness cfg eligible.setup.program tr eligible.func count (preparedControlRootLabel eligible.func),
      runCall cfg code method ctx fuel blockLevel full none=.done witness.final witness.error := by
  obtain ⟨w,_,called⟩:=prepared_typed_run_call_indexed codeCount count tr pub holds cfg code method ctx blockLevel full eligible accepted fuel enoughFuel
  exact ⟨w,called⟩

end NearCompression
