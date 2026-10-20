import NearCompression.PreparedControlProvenance

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 NearSpecV3.Wasm

/-- Actual preparation, linking/loading and method resolution followed by
control CODE validation. The caller supplies bytes, not an arbitrary PFunc. -/
def preparedControlSetupCheck (cfg : NearCfg) (code : ByteArray) (method : String) (ctx : CallCtx)
    (pub : List Fp) (blockLevel : Bool := true) : Option PreparedRunCallEligible := do
  let setup ← preparedRunCallSetup cfg code method ctx blockLevel
  let fn:=setup.methodIndex-setup.program.m.imports.size
  let pf ← setup.program.funcs[fn]?
  if preparedControlCodeCheck pf fn pub then some ⟨setup,pf⟩ else none

theorem prepared_control_setup_checked (cfg : NearCfg) (code : ByteArray) (method : String)
    (ctx : CallCtx) (pub : List Fp) (blockLevel : Bool) (eligible : PreparedRunCallEligible)
    (accepted : preparedControlSetupCheck cfg code method ctx pub blockLevel=some eligible) :
    preparedRunCallSetup cfg code method ctx blockLevel=some eligible.setup ∧
    eligible.setup.program.funcs[eligible.setup.methodIndex-eligible.setup.program.m.imports.size]?=some eligible.func ∧
    preparedControlCodeCheck eligible.func (eligible.setup.methodIndex-eligible.setup.program.m.imports.size) pub=true := by
  unfold preparedControlSetupCheck at accepted
  obtain ⟨setup,setupEq,rest⟩:=Option.bind_eq_some_iff.mp accepted
  obtain ⟨pf,fetch,rest⟩:=Option.bind_eq_some_iff.mp rest
  split at rest
  · rename_i checked
    cases rest
    exact ⟨setupEq,fetch,checked⟩
  · cases rest

/-- The source-selected function supplies every actual instruction, charge and
prepared block target for a literal control AIR fetch. Execution refinement
and initial/final state binding are separate obligations. -/
theorem prepared_control_setup_fetch (count : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedControlLiteralAir count) pub tr)
    (cfg : NearCfg) (code : ByteArray) (method : String) (ctx : CallCtx) (blockLevel : Bool)
    (eligible : PreparedRunCallEligible)
    (accepted : preparedControlSetupCheck cfg code method ctx pub blockLevel=some eligible)
    (r : Nat) (hr : r<tr.height 0) :
    preparedRunCallSetup cfg code method ctx blockLevel=some eligible.setup ∧
    eligible.setup.program.funcs[eligible.setup.methodIndex-eligible.setup.program.m.imports.size]?=some eligible.func ∧
    (let pc:=preparedCodeExecPC (tr.cell 0 r)
    pc<eligible.func.code.size ∧ ∃ op fee amount target,
      eligible.func.code[pc]?=some op.instr ∧ eligible.func.gas[pc]?=some fee ∧
      PreparedWasmCharge eligible.func pc amount ∧ amount<u64Bound ∧ target<4294967296 ∧
      (op=PreparedControlInstruction.block → ∃ e,eligible.func.endOf[pc]?=some e ∧ target=e+1) ∧
      ∀ field,field<29 → (preparedControlBusFetch.msgVal tr 0 r pub).getD field 0=
        preparedControlField (eligible.setup.methodIndex-eligible.setup.program.m.imports.size)
          pc op fee amount target field) := by
  obtain ⟨setup,fetch,checked⟩:=prepared_control_setup_checked cfg code method ctx pub blockLevel eligible accepted
  exact ⟨setup,fetch,prepared_control_authenticated_fetch count tr pub holds eligible.func _ checked r hr⟩

end NearCompression
