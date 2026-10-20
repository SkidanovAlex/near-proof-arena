import NearCompression.PreparedTypedPadding
import NearCompression.PreparedTypedBoundary
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2

/-- The public exit exposes the final row's actual status bits. -/
theorem prepared_typed_exit_flags (codeCount count : Nat) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedTypedLiteralAir codeCount count) pub tr)
    (counts : preparedExecBoundaryCountsCheck pub=true) :
    tr.cell 0 (tr.height 0-1) 41=pub.getD 68 0 ∧
    tr.cell 0 (tr.height 0-1) 42=pub.getD 69 0 := by
  have positive : 0<tr.height 0:=Nat.two_pow_pos _
  have balanced:=holds
  rw [prepared_typed_bus_literal_air] at balanced
  have message:=prepared_typed_boundary_bound _ _ _ codeCount tr pub balanced counts true
    (tr.height 0-1) (by omega) (by simp only [ite_true];omega)
  constructor
  · exact congrArg (fun xs : List Fp=>xs.getD 5 0) message
  · exact congrArg (fun xs : List Fp=>xs.getD 6 0) message

/-- Any reached DONE row has the same gas and failure flag as the public
exit, regardless of how much padding follows. No extra interpreter steps or
assumed final-row equality are needed. -/
theorem prepared_typed_done_public_exit (codeCount count : Nat) (hc : count≤4)
    (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedTypedLiteralAir codeCount count) pub tr)
    (counts : preparedExecBoundaryCountsCheck pub=true)
    (r : Nat) (live : r<tr.height 0) (done : tr.cell 0 r 41=1) :
    pub.getD 68 0=1 ∧ pub.getD 69 0=tr.cell 0 r 42 ∧
    preparedTypedPublicGas pub true=preparedExecWord64 (tr.cell 0 r) 299 := by
  have positive : 0<tr.height 0:=Nat.two_pow_pos _
  have suffix:=prepared_typed_padding_suffix count hc tr 0 pub
    (prepared_typed_exec_local codeCount count tr pub holds) r (tr.height 0-1-r) (by omega) done
  have index : r+(tr.height 0-1-r)=tr.height 0-1:=by omega
  rw [index] at suffix
  have flags:=prepared_typed_exit_flags codeCount count tr pub holds counts
  have gas:=prepared_typed_boundary_gas codeCount count tr pub holds counts true (tr.height 0-1)
    (by omega) (by simp only [ite_true];omega)
  exact ⟨flags.1.symm.trans (suffix.done.trans done),flags.2.symm.trans suffix.failed,
    gas.symm.trans suffix.gas⟩
end NearCompression
