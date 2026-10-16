import NearCompression.PreparedTypedTerminalWitness
import NearCompression.PreparedTypedPaddedExit
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2 NearSpecV3.Wasm

/-- Public terminal status and AIR gas snapshot. On exhaustion this records
pretrap fast gas, not the synchronized abort state's accounting fields. -/
def PreparedTypedWitnessPublished {cfg p tr pf count root}
    (pub : List Fp) (w : PreparedTypedTerminalWitness cfg p tr pf count root) : Prop :=
  pub.getD 68 0=1 ∧ pub.getD 69 0=(if w.error.isSome then 1 else 0) ∧
  preparedTypedPublicGas pub true=
    if preparedExecWord64 (tr.cell 0 w.row) 502≤w.before.gas.g
    then w.before.gas.g-preparedExecWord64 (tr.cell 0 w.row) 502 else w.before.gas.g

theorem prepared_typed_witness_published (codeCount count : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedTypedLiteralAir codeCount count) pub tr)
    (counts : preparedExecBoundaryCountsCheck pub=true)
    (cfg : NearCfg) (p : Prepared) (pf : PFunc) (root : Label)
    (w : PreparedTypedTerminalWitness cfg p tr pf count root) : PreparedTypedWitnessPublished pub w := by
  have localH:=prepared_typed_exec_local codeCount count tr pub holds
  have output:=prepared_typed_done_public_exit codeCount count w.state.countBound tr pub holds counts
    (w.row+1) w.nonlast w.done
  refine ⟨output.1,output.2.1.trans w.failed,?_⟩
  rw [output.2.2]
  by_cases enough:preparedExecWord64 (tr.cell 0 w.row) 502≤w.before.gas.g
  · rw [ite_eq_left enough]
    have rowEnough : preparedExecWord64 (tr.cell 0 w.row) 502≤preparedExecWord64 (tr.cell 0 w.row) 299 := by
      rw [←w.state.gas];exact enough
    have gas:=prepared_control_gas_success _ tr 0 w.row pub (prepared_typed_gas_source count w.state.countBound)
      localH w.nonlast w.active rowEnough
    exact gas.2.trans (by rw [←w.state.gas])
  · rw [ite_eq_right enough]
    have rowInsufficient : preparedExecWord64 (tr.cell 0 w.row) 299<preparedExecWord64 (tr.cell 0 w.row) 502 := by
      rw [←w.state.gas];omega
    have gas:=prepared_control_gas_exhaustion _ tr 0 w.row pub (prepared_typed_gas_source count w.state.countBound)
      localH w.nonlast rowInsufficient
    exact gas.2.trans w.state.gas.symm
end NearCompression
