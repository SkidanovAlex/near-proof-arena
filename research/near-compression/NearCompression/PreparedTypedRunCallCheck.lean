import NearCompression.PreparedTypedEntry
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 NearSpecV3.Wasm
/-- Verifier-side eligibility for the real bytecode/setup path and public
CODE/entry header. Preparation is computed here; it is not a PREP AIR proof. -/
def preparedTypedRunCallCheck (count : Nat) (cfg : NearCfg) (code : ByteArray) (method : String)
    (ctx : CallCtx) (pub : List Fp) (blockLevel : Bool := true) : Option PreparedRunCallEligible := do
  let eligible ← preparedTypedSetupCheck count cfg code method ctx pub blockLevel
  if preparedExecEntryCheck eligible.setup.program eligible.setup.methodIndex eligible.func eligible.setup.host pub
    then some eligible else none

theorem prepared_typed_run_call_checked (count : Nat) (cfg : NearCfg) (code : ByteArray) (method : String)
    (ctx : CallCtx) (pub : List Fp) (blockLevel : Bool) (eligible : PreparedRunCallEligible)
    (accepted : preparedTypedRunCallCheck count cfg code method ctx pub blockLevel=some eligible) :
    preparedTypedSetupCheck count cfg code method ctx pub blockLevel=some eligible ∧
    preparedExecEntryCheck eligible.setup.program eligible.setup.methodIndex eligible.func eligible.setup.host pub=true := by
  unfold preparedTypedRunCallCheck at accepted
  obtain ⟨found,checked,rest⟩:=Option.bind_eq_some_iff.mp accepted
  split at rest
  · rename_i entry
    cases rest
    exact ⟨checked,entry⟩
  · cases rest


end NearCompression
