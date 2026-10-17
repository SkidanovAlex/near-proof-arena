import NearCompression.PreparedCodeProvenance

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

def preparedExecPCAdvance : Expr :=
  .mul (.mul (.add (.const 1) (.neg (.col 41 false)))
    (.add (.const 1) (.neg (.col 430 false))))
    (.add (.const 1) (.neg (.col 469 false)))
def preparedExecPCStepLow : Expr :=
  .mul .isTransition
    (.add (.add (preparedCodeBits 0) preparedExecPCAdvance)
      (.neg (.add (preparedCodeBits 0 true) (.mul (.const 65536) (.col 465 false)))))
def preparedExecPCStepHigh : Expr :=
  .mul .isTransition
    (.add (preparedCodeBits 16 true) (.neg (.add (preparedCodeBits 16) (.col 465 false))))
structure PreparedExecPCSource (table : Table) : Prop where
  boolean : ∀ i,i<605 → preparedGasBoolean i∈table.constraints
  low : preparedExecPCStepLow∈table.constraints
  high : preparedExecPCStepHigh∈table.constraints

theorem prepared_exec_boolean (table : Table) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (source : PreparedExecPCSource table) (localH : TableLocal table tr t pub)
    (r : Nat) (hr : r<tr.height t) (i : Nat) (hi : i<605) : (tr.cell t r i).toNat≤1 := by
  have h:=localH.constr r hr _ (source.boolean i hi)
  change tr.cell t r i*(tr.cell t r i+ -(1:Fp))+ -(0:Fp)=0 at h
  apply instruction_add_boolean_bound
  grind

theorem prepared_exec_limb_bound (table : Table) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (source : PreparedExecPCSource table) (localH : TableLocal table tr t pub)
    (r : Nat) (hr : r<tr.height t) (base : Nat) (fits : base+16≤605) :
    (preparedCodeLimb (tr.cell t r) base).toNat<65536 := by
  exact instruction_bit_expr_bound _ 16 base (by decide) (fun k hk=>
    prepared_exec_boolean table tr t pub source localH r hr _ (by omega))

/-- Exact natural numeric-PC transition, including the no-wrap high limb.
The step is zero for end/exhaustion/padding and one for successful non-end. -/
theorem prepared_exec_pc_transition (table : Table) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (source : PreparedExecPCSource table) (localH : TableLocal table tr t pub)
    (r : Nat) (next : r+1<tr.height t) (step : Nat) (stepBound : step≤1)
    (advance : preparedExecPCAdvance.eval tr t r pub=Fp.ofNat step) :
    preparedCodeExecPC (tr.cell t (r+1))=preparedCodeExecPC (tr.cell t r)+step := by
  have notLast : ¬r+1=tr.height t:=by omega
  have low:=localH.constr r (by omega) _ source.low
  have high:=localH.constr r (by omega) _ source.high
  change (if r+1=tr.height t then (0:Fp) else 1)*
    ((preparedCodeBits 0).eval tr t r pub+preparedExecPCAdvance.eval tr t r pub+
      -((preparedCodeBits 0 true).eval tr t r pub+65536*tr.cell t r 465))=0 at low
  change (if r+1=tr.height t then (0:Fp) else 1)*
    ((preparedCodeBits 16 true).eval tr t r pub+
      -((preparedCodeBits 16).eval tr t r pub+tr.cell t r 465))=0 at high
  rw [if_neg notLast,advance] at low
  rw [if_neg notLast] at high
  rw [prepared_code_bits_eval,prepared_code_bits_eval] at low high
  simp only [Bool.false_eq_true,ite_false,ite_true,Nat.mod_eq_of_lt next] at low high
  have lo : preparedCodeLimb (tr.cell t r) 0+Fp.ofNat step+0=
      preparedCodeLimb (tr.cell t (r+1)) 0+65536*tr.cell t r 465 := by grind
  have hi : preparedCodeLimb (tr.cell t r) 16+(0:Fp)+tr.cell t r 465=
      preparedCodeLimb (tr.cell t (r+1)) 16+65536*(0:Fp) := by grind
  have carry:=prepared_exec_boolean table tr t pub source localH r (by omega) 465 (by decide)
  have sn : (Fp.ofNat step).toNat=step := by
    rw [Fp.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by unfold P;omega)
  have l:=instruction_add_limb_sound _ (Fp.ofNat step) 0 _ _
    (prepared_exec_limb_bound table tr t pub source localH r (by omega) 0 (by decide))
    (by rw [sn];omega) (by decide)
    (prepared_exec_limb_bound table tr t pub source localH (r+1) next 0 (by decide)) carry lo
  have h:=instruction_add_limb_sound _ 0 _ _ 0
    (prepared_exec_limb_bound table tr t pub source localH r (by omega) 16 (by decide)) (by decide)
    carry (prepared_exec_limb_bound table tr t pub source localH (r+1) next 16 (by decide)) (by decide) hi
  change (preparedCodeLimb (tr.cell t r) 0).toNat+(Fp.ofNat step).toNat+0=
    (preparedCodeLimb (tr.cell t (r+1)) 0).toNat+65536*(tr.cell t r 465).toNat at l
  change (preparedCodeLimb (tr.cell t r) 16).toNat+0+(tr.cell t r 465).toNat=
    (preparedCodeLimb (tr.cell t (r+1)) 16).toNat+65536*0 at h
  rw [sn] at l
  unfold preparedCodeExecPC
  omega

end NearCompression
