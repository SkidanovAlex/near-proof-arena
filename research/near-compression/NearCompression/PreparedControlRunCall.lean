import NearCompression.PreparedControlEntry

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 NearSpecV3.Wasm

/-- Verifier-side eligibility for the real bytecode/setup path and public
CODE/entry header. Preparation is computed here; it is not a PREP AIR proof. -/
def preparedControlRunCallCheck (cfg : NearCfg) (code : ByteArray) (method : String)
    (ctx : CallCtx) (pub : List Fp) (blockLevel : Bool := true) : Option PreparedRunCallEligible := do
  let eligible ← preparedControlSetupCheck cfg code method ctx pub blockLevel
  if preparedExecEntryCheck eligible.setup.program eligible.setup.methodIndex eligible.func eligible.setup.host pub
    then some eligible else none

theorem prepared_control_run_call_checked (cfg : NearCfg) (code : ByteArray) (method : String)
    (ctx : CallCtx) (pub : List Fp) (blockLevel : Bool) (eligible : PreparedRunCallEligible)
    (accepted : preparedControlRunCallCheck cfg code method ctx pub blockLevel=some eligible) :
    preparedControlSetupCheck cfg code method ctx pub blockLevel=some eligible ∧
    preparedExecEntryCheck eligible.setup.program eligible.setup.methodIndex eligible.func eligible.setup.host pub=true := by
  unfold preparedControlRunCallCheck at accepted
  obtain ⟨found,checked,rest⟩:=Option.bind_eq_some_iff.mp accepted
  split at rest
  · rename_i entry
    cases rest
    exact ⟨checked,entry⟩
  · cases rest

/-- Literal AIR plus executable setup/CODE/header checks proves an actual
outer runCall outcome. This does not yet identify its final state with every
published output field; terminal padding/output decoding is a separate layer. -/
theorem prepared_control_run_call (count : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedControlLiteralAir count) pub tr)
    (cfg : NearCfg) (code : ByteArray) (method : String) (ctx : CallCtx)
    (blockLevel full : Bool) (eligible : PreparedRunCallEligible)
    (accepted : preparedControlRunCallCheck cfg code method ctx pub blockLevel=some eligible)
    (fuel : Nat) (enoughFuel : tr.height 0≤fuel) :
    ∃ witness:PreparedControlTerminalWitness cfg eligible.setup.program tr eligible.func (preparedControlRootLabel eligible.func),
      runCall cfg code method ctx fuel blockLevel full none=.done witness.final witness.error := by
  obtain ⟨codeCheck,entry⟩:=prepared_control_run_call_checked cfg code method ctx pub blockLevel eligible accepted
  obtain ⟨setup,fetch,checked⟩:=prepared_control_setup_checked cfg code method ctx pub blockLevel eligible codeCheck
  obtain ⟨witness,body⟩:=prepared_control_call_entry count tr pub holds cfg code method ctx blockLevel eligible codeCheck entry fuel enoughFuel
  exact ⟨witness,prepared_run_call_setup_sound cfg code method ctx blockLevel full eligible.setup setup
    fuel witness.final witness.error body⟩

end NearCompression
