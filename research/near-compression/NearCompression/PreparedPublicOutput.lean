import NearCompression.PreparedPublicBoundary
import NearCompression.PreparedWasmFinalRow

namespace NearCompression
open ZkFormal.Algebra ZkFormal.Air ZkFormal.V2 NearSpecV3.Wasm

def preparedPublicStackWord (pub : List Fp) (slot : Nat) : Nat :=
  (pub.getD (40+2*slot) 0).toNat+65536*(pub.getD (41+2*slot) 0).toNat

def preparedPublicStack (pub : List Fp) : Nat → Array Val
  | 0 => #[]
  | n+1 => (preparedPublicStack pub n).push (.i32 (UInt32.ofNat (preparedPublicStackWord pub n)))

/-- Public output is a bounded stack snapshot, fast gas and terminal status.
The PC field is authenticated terminal metadata, not a live returned frame. -/
def PreparedPublishedOutput (pub : List Fp) (final : St) (error : Option String) : Prop :=
  pub.getD 34 0=1 ∧ pub.getD 35 0=(if error.isSome then 1 else 0) ∧
  final.gas.g=preparedPublicGas pub true ∧ (pub.getD 33 0).toNat<9 ∧
  final.stack=preparedPublicStack pub (pub.getD 33 0).toNat

theorem prepared_boundary_sp_field (tr : Trace Fp) (pub : List Fp) (r : Nat) :
    ((preparedBoundaryInteraction true).msgVal tr 0 r pub).getD 1 0=
      (preparedSPIndexPython false).evalWith
        (preparedRowEnv (tr.cell 0 r) (tr.cell 0 r) (fun i=>pub.getD i 0) 0 0) := rfl

theorem prepared_boundary_stack_field (tr : Trace Fp) (pub : List Fp) (r slot limb : Nat)
    (hs : slot<8) (hl : limb<2) :
    ((preparedBoundaryInteraction true).msgVal tr 0 r pub).getD (8+2*slot+limb) 0=
      preparedGasLimb (tr.cell 0 r) pub (27+32*slot) limb := by
  have slots : slot=0 ∨ slot=1 ∨ slot=2 ∨ slot=3 ∨ slot=4 ∨ slot=5 ∨ slot=6 ∨ slot=7 := by omega
  have limbs : limb=0 ∨ limb=1 := by omega
  rcases slots with h|h|h|h|h|h|h|h <;> subst slot <;> rcases limbs with h|h <;> subst limb <;> rfl

theorem prepared_public_stack_field (pub : List Fp) (slot limb : Nat) (hs : slot<8) (hl : limb<2) :
    (preparedPublicBoundary pub true).getD (8+2*slot+limb) 0=pub.getD (40+2*slot+limb) 0 := by
  have slots : slot=0 ∨ slot=1 ∨ slot=2 ∨ slot=3 ∨ slot=4 ∨ slot=5 ∨ slot=6 ∨ slot=7 := by omega
  have limbs : limb=0 ∨ limb=1 := by omega
  rcases slots with h|h|h|h|h|h|h|h <;> subst slot <;> rcases limbs with h|h <;> subst limb <;> rfl

theorem prepared_boundary_stack_word (constraints : List Expr) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedBoundaryAir constraints) pub tr) (counts : preparedBoundaryCountsCheck pub=true)
    (r : Nat) (hr : r<tr.height 0) (endpoint : r+1=tr.height 0) (slot : Nat) (hs : slot<8) :
    preparedStackWord (tr.cell 0 r) slot=preparedPublicStackWord pub slot := by
  have message:=prepared_boundary_message_bound constraints tr pub holds counts true r hr endpoint
  have limb (i : Nat) (hi : i<2) :
      preparedGasLimb (tr.cell 0 r) pub (27+32*slot) i=pub.getD (40+2*slot+i) 0 := by
    have h:=congrArg (fun msg:List Fp=>msg.getD (8+2*slot+i) 0) message
    simpa only [prepared_boundary_stack_field tr pub r slot i hs hi,prepared_public_stack_field pub slot i hs hi] using h
  have low:=limb 0 (by decide)
  have high:=limb 1 (by decide)
  simp only [preparedGasLimb,prepared_gas_bits_horner,Nat.mul_zero,Nat.add_zero,Nat.mul_one] at low high
  simp only [preparedStackWord,low,high,preparedPublicStackWord,Nat.add_right_comm 40 _ 1]

theorem prepared_public_stack_decode (row : Nat → Fp) (pub : List Fp) (sp : Nat) (bound : sp<9)
    (words : ∀ slot,slot<8 → preparedStackWord row slot=preparedPublicStackWord pub slot) :
    preparedWasmStack row sp=preparedPublicStack pub sp := by
  induction sp with
  | zero => rfl
  | succ sp ih =>
    simp only [preparedWasmStack,preparedPublicStack,ih (by omega),words sp (by omega)]

/-- The actual public receive segment binds the final interpreter's live stack,
fast gas, and success/failure status, after terminal padding propagation. -/
theorem prepared_final_row_published (constraints : List Expr) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedBoundaryAir constraints) pub tr) (counts : preparedBoundaryCountsCheck pub=true)
    (r : Nat) (hr : r<tr.height 0) (endpoint : r+1=tr.height 0)
    (final : St) (error : Option String) (binding : PreparedWasmFinalRow (tr.cell 0 r) pub final error) :
    PreparedPublishedOutput pub final error := by
  rcases binding with ⟨done,failed,gas,sp,bound,selected,stack⟩
  have flags:=prepared_boundary_status_bound constraints tr pub holds counts true r hr endpoint
  have gasEq:=prepared_boundary_gas_bound constraints tr pub holds counts true r hr endpoint
  have message:=prepared_boundary_message_bound constraints tr pub holds counts true r hr endpoint
  have spField:=congrArg (fun msg:List Fp=>msg.getD 1 0) message
  rw [prepared_boundary_sp_field,prepared_sp_index_selected _ _ _ false sp bound selected] at spField
  have pubSP : Fp.ofNat sp=pub.getD 33 0 := spField
  have spNat : (pub.getD 33 0).toNat=sp := by
    rw [←pubSP,Fp.toNat_ofNat,Nat.mod_eq_of_lt (show sp<ZkFormal.Algebra.P by unfold ZkFormal.Algebra.P;omega)]
  refine ⟨flags.1.symm.trans done,flags.2.symm.trans failed,gas.trans gasEq,?_,?_⟩
  · rw [spNat];exact bound
  · rw [spNat,stack]
    exact prepared_public_stack_decode _ pub sp bound (fun slot hs=>prepared_boundary_stack_word constraints tr pub holds counts r hr endpoint slot hs)

theorem prepared_boundary_local (constraints : List Expr) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedBoundaryAir constraints) pub tr) :
    ZkFormal.Near.TableLocal (preparedBoundaryTable constraints) tr 0 pub := by
  refine ⟨(holds.logBound 0 (by change 0<1;decide)).1,(holds.logBound 0 (by change 0<1;decide)).2,?_,?_⟩
  · intro r hr e he;exact holds.constr 0 (by change 0<1;decide) r hr e he
  · intro r hr i hi b hb;exact holds.bits 0 (by change 0<1;decide) r hr i hi b hb

/-- Public-statement comparison against the actual host/prologue context. -/
def preparedPublicEntryCheck (pub : List Fp) (host : St) (pf : PFunc) : Bool :=
  preparedBoundaryCountsCheck pub && decide (preparedPublicGas pub false=host.gas.remaining-pf.prologueGas)

/-- Whole checked callEntry with authenticated public input/output buses.
The certificate, initial row gas binding, and terminal-to-last-row output
binding are all derived. Outer preparation/loading remains explicit context. -/
theorem prepared_wasm_public_call_entry (constraints : List Expr) (tr : Trace Fp) (pub : List Fp)
    (source : PreparedWasmSource (preparedBoundaryTable constraints))
    (holds : HoldsP (preparedBoundaryAir constraints) pub tr)
    (lastMember : preparedLastDonePython∈constraints)
    (firstPC : preparedFirstEqPython 0 1∈constraints)
    (firstSP : preparedFirstEqPython 16 1∈constraints)
    (firstActive : preparedFirstEqPython 25 0∈constraints)
    (cfg : NearCfg) (p : Prepared) (fi : Nat) (pf : PFunc) (host : St)
    (checked : preparedCodeTerminatedCheck pf pub=true)
    (statement : preparedPublicEntryCheck pub host pf=true)
    (fetch : p.funcs[fi-p.m.imports.size]?=some pf)
    (stackBudget : pf.stackCharge≤host.stackRem)
    (feeBound : pf.prologueGas<u64Bound) (enough : pf.prologueGas≤host.gas.remaining)
    (promises : host.gas.promises=0) (limit : host.gas.limit=host.gas.prepaid)
    (spent : host.gas.burnt≤host.gas.prepaid) (prepaid : host.gas.prepaid≤maxGasBurnt)
    (extra : Nat) :
    ∃ n final error,n≤pf.code.size ∧
      PreparedWasmExecution p tr 0 pub 0 (preparedWasmEntryState p fi pf host) n final error ∧
      callEntry cfg p (pf.code.size+extra) host fi=.ok (final,error) ∧ PreparedPublishedOutput pub final error := by
  have localH:=prepared_boundary_local constraints tr pub holds
  have positive : 0<tr.height 0 := by unfold Trace.height;exact Nat.two_pow_pos _
  have claims:=statement
  simp only [preparedPublicEntryCheck,Bool.and_eq_true] at claims
  have counts:=claims.1
  have initial:=prepared_boundary_initial_gas constraints tr pub holds counts positive host pf
    (of_decide_eq_true claims.2)
  obtain ⟨n,final,error,count,execution,actual⟩:=prepared_wasm_air_call_entry
    (preparedBoundaryTable constraints) tr 0 pub source localH lastMember firstPC firstSP firstActive
    positive cfg p fi pf host checked fetch stackBudget feeBound enough promises limit spent prepaid initial extra
  have shape:=prepared_code_terminated_shape pf pub checked
  have bounds:=prepared_code_public_limb_bounds pf pub shape.1
  let air : PreparedWasmAir (preparedBoundaryTable constraints) tr 0 pub:=⟨source,localH,bounds.1,bounds.2⟩
  have binding:=prepared_execution_last_row _ tr 0 pub air p execution
  exact ⟨n,final,error,count,execution,actual,prepared_final_row_published constraints tr pub holds counts
    (tr.height 0-1) (by omega) (by omega) final error binding⟩

end NearCompression
