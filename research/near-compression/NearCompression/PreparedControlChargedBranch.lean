import NearCompression.PreparedControlUntaken
import NearCompression.PreparedControlGas
import NearCompression.PreparedControlSequential

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpecV3.Wasm

/-- Successful taken branch projection, deriving the gas-success flag from
natural affordability. This is a local AIR theorem; label provenance and
instruction/interpreter state matching are separate obligations. -/
theorem prepared_control_charged_taken (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal preparedControlLiteralExecTable tr t pub)
    (nonlast : r+1<tr.height t) (active : tr.cell t r 41=0)
    (enough : preparedExecWord64 (tr.cell t r) 502≤preparedExecWord64 (tr.cell t r) 299)
    (branch : tr.cell t r 606=1) (nonzero : tr.cell t r 681=1) :
    preparedExecWord64 (tr.cell t (r+1)) 299=
      preparedExecWord64 (tr.cell t r) 299-preparedExecWord64 (tr.cell t r) 502 ∧
    preparedCodeExecPC (tr.cell t (r+1))=preparedControlSavedTarget (tr.cell t r) ∧
    tr.cell t (r+1) 41=0 ∧ tr.cell t (r+1) 42=0 ∧
    tr.cell t (r+1) 639=0 ∧
    (∀ i,i<9 → tr.cell t (r+1) (640+i)=0) ∧
    preparedControlSavedTarget (tr.cell t (r+1))=0 ∧
    ∃ height,height<9 ∧
      (∀ i,i<9 → tr.cell t r (640+i)=if i=height then 1 else 0) ∧
      (∀ i,i<9 → tr.cell t (r+1) (32+i)=if i=height then 1 else 0) ∧
      ∀ slot,slot<8 → preparedExecStackWord (tr.cell t (r+1)) slot=
        if slot<height then preparedExecStackWord (tr.cell t r) slot else 0 := by
  obtain ⟨charged,gas⟩:=prepared_control_gas_success _ tr t r pub
    prepared_control_literal_gas_source localH nonlast active enough
  have ops:=prepared_control_branch_opcode tr t r pub localH (by omega) branch
  have status:=prepared_control_continue_status tr t r pub localH nonlast active charged
    (by rw [ops.1 3 (by decide)];grind)
  have label:=prepared_control_taken_label tr t r pub localH nonlast active charged branch nonzero
  exact ⟨gas,prepared_control_taken_pc tr t r pub localH nonlast active charged branch nonzero,
    status.2.1,status.2.2,label.1,label.2.1,label.2.2,
    prepared_control_taken_stack_projection tr t r pub localH nonlast active charged branch nonzero⟩

/-- Untaken control and gas compose without a caller-supplied success flag.
Stack-pop semantics are intentionally not part of this projection. -/
theorem prepared_control_charged_untaken (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal preparedControlLiteralExecTable tr t pub)
    (nonlast : r+1<tr.height t) (active : tr.cell t r 41=0)
    (enough : preparedExecWord64 (tr.cell t r) 502≤preparedExecWord64 (tr.cell t r) 299)
    (branch : tr.cell t r 606=1) (zero : tr.cell t r 681=0) :
    preparedExecWord64 (tr.cell t (r+1)) 299=
      preparedExecWord64 (tr.cell t r) 299-preparedExecWord64 (tr.cell t r) 502 ∧
    preparedCodeExecPC (tr.cell t (r+1))=preparedCodeExecPC (tr.cell t r)+1 ∧
    tr.cell t (r+1) 41=0 ∧ tr.cell t (r+1) 42=0 ∧
    tr.cell t (r+1) 639=tr.cell t r 639 ∧
    (∀ i,i<9 → tr.cell t (r+1) (640+i)=tr.cell t r (640+i)) ∧
    preparedControlSavedTarget (tr.cell t (r+1))=preparedControlSavedTarget (tr.cell t r) := by
  obtain ⟨charged,gas⟩:=prepared_control_gas_success _ tr t r pub
    prepared_control_literal_gas_source localH nonlast active enough
  exact ⟨gas,prepared_control_untaken_pc_label tr t r pub localH nonlast active charged branch zero⟩

/-- Affordable false br_if consumes exactly its zero-valued condition and
clears the popped slot; gas success and nonempty stack are derived. -/
theorem prepared_control_charged_untaken_stack (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal preparedControlLiteralExecTable tr t pub)
    (nonlast : r+1<tr.height t) (active : tr.cell t r 41=0)
    (enough : preparedExecWord64 (tr.cell t r) 502≤preparedExecWord64 (tr.cell t r) 299)
    (branch : tr.cell t r 606=1) (zero : tr.cell t r 681=0) :
    preparedExecWord64 (tr.cell t (r+1)) 299=
      preparedExecWord64 (tr.cell t r) 299-preparedExecWord64 (tr.cell t r) 502 ∧
    ∃ sp,0<sp ∧ sp<9 ∧
      (∀ i,i<9 → tr.cell t r (32+i)=if i=sp then 1 else 0) ∧
      (∀ i,i<9 → tr.cell t (r+1) (32+i)=if i=sp-1 then 1 else 0) ∧
      preparedExecStackWord (tr.cell t r) (sp-1)=0 ∧
      ∀ slot,slot<8 → preparedExecStackWord (tr.cell t (r+1)) slot=
        if slot+1=sp then 0 else preparedExecStackWord (tr.cell t r) slot := by
  obtain ⟨charged,gas⟩:=prepared_control_gas_success _ tr t r pub
    prepared_control_literal_gas_source localH nonlast active enough
  exact ⟨gas,prepared_control_untaken_stack_projection tr t r pub localH nonlast active charged branch zero⟩

end NearCompression
