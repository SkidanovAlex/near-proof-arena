import NearCompression.PreparedLocalsStep
import NearCompression.PreparedControlSetup
namespace NearCompression
open ZkFormal.Algebra NearSpecV3.Wasm

inductive PreparedTypedInstruction where
  | control (op : PreparedControlInstruction)
  | local (op : PreparedLocalOp) (index : Nat)
  | constant64 (value : UInt64)
  | add64 | eqz64
  deriving DecidableEq

def PreparedTypedInstruction.instr : PreparedTypedInstruction→Instr
  | .control op=>op.instr | .local op i=>op.instr i
  | .constant64 value=>.i64Const value | .add64=>.num 0x7c | .eqz64=>.num 0x50

def PreparedTypedInstruction.tag : PreparedTypedInstruction→Nat
  | .control op=>op.tag
  | .local .get _=>6 | .local .set _=>7 | .local .tee _=>8
  | .constant64 _=>9 | .add64=>10 | .eqz64=>11

def PreparedTypedInstruction.immediate : PreparedTypedInstruction→Nat
  | .control op=>op.immediate | .local _ i=>i
  | .constant64 value=>value.toNat | .add64 | .eqz64=>0

def preparedTypedInspect (count : Nat) : Instr→Option PreparedTypedInstruction
  | .localGet i=>if i<count then some (.local .get i) else none
  | .localSet i=>if i<count then some (.local .set i) else none
  | .localTee i=>if i<count then some (.local .tee i) else none
  | .i64Const value=>some (.constant64 value)
  | .num 0x7c=>some .add64
  | .num 0x50=>some .eqz64
  | ins=>(preparedControlInspect ins).map .control

theorem prepared_typed_inspect (count : Nat) (ins : Instr) (op : PreparedTypedInstruction)
    (accepted : preparedTypedInspect count ins=some op) :
    ins=op.instr ∧ (∀kind index,op=.local kind index → index<count) := by
  unfold preparedTypedInspect at accepted
  split at accepted
  · split at accepted
    · cases accepted;exact ⟨rfl,by intro k i eq;cases eq;assumption⟩
    · cases accepted
  · split at accepted
    · cases accepted;exact ⟨rfl,by intro k i eq;cases eq;assumption⟩
    · cases accepted
  · split at accepted
    · cases accepted;exact ⟨rfl,by intro k i eq;cases eq;assumption⟩
    · cases accepted
  · cases accepted;exact ⟨rfl,by intro k i eq;cases eq⟩
  · cases accepted;exact ⟨rfl,by intro k i eq;cases eq⟩
  · cases accepted;exact ⟨rfl,by intro k i eq;cases eq⟩
  · obtain ⟨old,h,eq⟩:=Option.map_eq_some_iff.mp accepted
    cases eq
    exact ⟨prepared_control_inspect _ _ h,by intro k i eq;cases eq⟩

def preparedTypedField (fn pc : Nat) (op : PreparedTypedInstruction)
    (fee : Option (IK × Fee)) (amount target field : Nat) : Fp :=
  if field<2 then Fp.ofNat ((fn/65536^field)%65536)
  else if field<4 then Fp.ofNat ((pc/65536^(field-2))%65536)
  else if field<8 then if field-4=op.tag then 1 else 0
  else if field<10 then Fp.ofNat ((op.immediate/65536^(field-8))%65536)
  else if field<14 then Fp.ofNat ((amount/65536^(field-10))%65536)
  else if field=14 then if fee.isSome then 1 else 0
  else if field<21 then match fee with
    | none=>0 | some (kind,_)=>if field-15=preparedCodeKind kind then 1 else 0
  else if field<25 then 0
  else if field<27 then if field-21=op.tag then 1 else 0
  else if field<29 then Fp.ofNat ((target/65536^(field-27))%65536)
  else if field<32 then if field-23=op.tag then 1 else 0
  else if field<34 then Fp.ofNat ((op.immediate/65536^(field-30))%65536)
  else if field-25=op.tag then 1 else 0

def preparedTypedTarget (pf : PFunc) (pc : Nat) : PreparedTypedInstruction→Option Nat
  | .control op=>preparedControlTarget pf pc op | .local _ _ | .constant64 _ | .add64 | .eqz64=>some 0

theorem prepared_typed_target_checked (pf : PFunc) (pc : Nat) (op : PreparedTypedInstruction)
    (target : Nat) (accepted : preparedTypedTarget pf pc op=some target) :
    target<4294967296 ∧ (op=.control .block → ∃e,pf.endOf[pc]?=some e ∧ target=e+1) := by
  cases op with
  | control old =>
    have result:=prepared_control_target_checked pf pc old target accepted
    exact ⟨result.1,by intro eq;cases eq;exact result.2 rfl⟩
  | «local» kind index => cases accepted;exact ⟨by decide,by intro eq;cases eq⟩
  | constant64 value => cases accepted;exact ⟨by decide,by intro eq;cases eq⟩
  | add64 | eqz64 => cases accepted;exact ⟨by decide,by intro eq;cases eq⟩

def preparedTypedCodeEntryCheck (pf : PFunc) (fn : Nat) (pub : List Fp) (pc : Nat) : Bool :=
  match pf.code[pc]?,pf.gas[pc]? with
  | some ins,some fee=>match preparedTypedInspect pf.locals.size ins,preparedInspectFee fee with
    | some op,some amount=>match preparedTypedTarget pf pc op with
      | some target=>(List.range 37).all (fun field=>decide
        (pub.getD (118+37*pc+field) 0=preparedTypedField fn pc op fee amount target field))
      | none=>false
    | _,_=>false
  | _,_=>false

/-- The AIR parameter is checked against actual prepared locals, with no
parameters and mixed i32/i64 local types and authenticated public type header. Header and CODE lengths stay exact. -/
def preparedTypedCodeCheck (localCount : Nat) (pf : PFunc) (fn : Nat) (pub : List Fp) : Bool :=
  decide (fn=0 ∧ localCount≤4 ∧ pf.locals.size=localCount ∧ pf.type.params.isEmpty ∧
    pf.type.results.isEmpty ∧ (∀ty∈pf.locals.toList,ty=VT.i32 ∨ ty=VT.i64) ∧
    0<pf.code.size ∧ pf.code.size<4294967296 ∧ pf.gas.size=pf.code.size ∧
    pub.length=118+37*pf.code.size ∧ preparedCodePublicSegment.count pub=pf.code.size ∧
    (∀i∈List.range 4,pub.getD (114+i) 0=if pf.locals[i]?=some VT.i64 then 1 else 0)) &&
  (List.range pf.code.size).all (preparedTypedCodeEntryCheck pf fn pub)

theorem prepared_typed_code_shape (count : Nat) (pf : PFunc) (fn : Nat) (pub : List Fp)
    (accepted : preparedTypedCodeCheck count pf fn pub=true) :
    fn=0 ∧ count≤4 ∧ pf.locals.size=count ∧ pf.type.params.isEmpty ∧
    pf.type.results.isEmpty ∧ (∀ty∈pf.locals.toList,ty=VT.i32 ∨ ty=VT.i64) ∧
    0<pf.code.size ∧ pf.code.size<4294967296 ∧ pf.gas.size=pf.code.size ∧
    pub.length=118+37*pf.code.size ∧ preparedCodePublicSegment.count pub=pf.code.size ∧
    (∀i∈List.range 4,pub.getD (114+i) 0=if pf.locals[i]?=some VT.i64 then 1 else 0) := by
  simp only [preparedTypedCodeCheck,Bool.and_eq_true] at accepted
  exact of_decide_eq_true accepted.1

theorem prepared_typed_code_entry (count : Nat) (pf : PFunc) (fn : Nat) (pub : List Fp)
    (accepted : preparedTypedCodeCheck count pf fn pub=true) (pc : Nat) (live : pc<pf.code.size) :
    preparedTypedCodeEntryCheck pf fn pub pc=true := by
  simp only [preparedTypedCodeCheck,Bool.and_eq_true] at accepted
  exact List.all_eq_true.mp accepted.2 pc (List.mem_range.mpr live)

theorem prepared_typed_entry_checked (pf : PFunc) (fn : Nat) (pub : List Fp) (pc : Nat)
    (accepted : preparedTypedCodeEntryCheck pf fn pub pc=true) :
    ∃op fee amount target,pf.code[pc]?=some op.instr ∧ pf.gas[pc]?=some fee ∧
      PreparedWasmCharge pf pc amount ∧ amount<u64Bound ∧
      (∀kind index,op=PreparedTypedInstruction.local kind index → index<pf.locals.size) ∧
      preparedTypedTarget pf pc op=some target ∧
      ∀field,field<37 → pub.getD (118+37*pc+field) 0=preparedTypedField fn pc op fee amount target field := by
  unfold preparedTypedCodeEntryCheck at accepted
  split at accepted
  · rename_i ins fee code gas
    split at accepted
    · rename_i op amount decoded feeDecoded
      split at accepted
      · rename_i target targetDecoded
        have feeSound:=prepared_inspect_fee fee amount feeDecoded
        have inspected:=prepared_typed_inspect pf.locals.size ins op decoded
        refine ⟨op,fee,amount,target,?_,gas,?_,feeSound.1,inspected.2,targetDecoded,?_⟩
        · rw [code,inspected.1]
        · rcases feeSound.2 with ⟨none,zero⟩|⟨k,f,someFee,linear,cost⟩
          · exact Or.inl ⟨by rw [gas,none],zero⟩
          · exact Or.inr ⟨k,f,by rw [gas,someFee],linear,cost⟩
        · intro field bound
          exact of_decide_eq_true (List.all_eq_true.mp accepted field (List.mem_range.mpr bound))
      · cases accepted
    · cases accepted
  · cases accepted

/-- Uses actual prepare/link/load/resolve, never a caller-supplied PFunc. -/
def preparedTypedSetupCheck (count : Nat) (cfg : NearCfg) (bytes : ByteArray) (method : String)
    (ctx : CallCtx) (pub : List Fp) (blockLevel : Bool := true) : Option PreparedRunCallEligible := do
  let setup ← preparedRunCallSetup cfg bytes method ctx blockLevel
  let fn:=setup.methodIndex-setup.program.m.imports.size
  let pf ← setup.program.funcs[fn]?
  if preparedTypedCodeCheck count pf fn pub then some ⟨setup,pf⟩ else none

theorem prepared_typed_setup_checked (count : Nat) (cfg : NearCfg) (bytes : ByteArray)
    (method : String) (ctx : CallCtx) (pub : List Fp) (blockLevel : Bool)
    (eligible : PreparedRunCallEligible)
    (accepted : preparedTypedSetupCheck count cfg bytes method ctx pub blockLevel=some eligible) :
    preparedRunCallSetup cfg bytes method ctx blockLevel=some eligible.setup ∧
    eligible.setup.program.funcs[eligible.setup.methodIndex-eligible.setup.program.m.imports.size]?=some eligible.func ∧
    preparedTypedCodeCheck count eligible.func (eligible.setup.methodIndex-eligible.setup.program.m.imports.size) pub=true := by
  unfold preparedTypedSetupCheck at accepted
  obtain ⟨setup,setupEq,rest⟩:=Option.bind_eq_some_iff.mp accepted
  obtain ⟨pf,fetch,rest⟩:=Option.bind_eq_some_iff.mp rest
  split at rest
  · rename_i checked
    cases rest
    exact ⟨setupEq,fetch,checked⟩
  · cases rest
/-- Public local type tags are derived from the actual prepared function,
including zero tags for unused slots; an unused type is not freely chosen. -/
theorem prepared_typed_local_type (count : Nat) (pf : PFunc) (fn : Nat) (pub : List Fp)
    (accepted : preparedTypedCodeCheck count pf fn pub=true) (i : Nat) (hi : i<4) :
    pub.getD (114+i) 0=if pf.locals[i]?=some VT.i64 then 1 else 0 := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,types⟩:=prepared_typed_code_shape count pf fn pub accepted
  exact types i (List.mem_range.mpr hi)

end NearCompression
