import NearCompression.PreparedLocalsStep
import NearCompression.PreparedControlSetup
namespace NearCompression
open ZkFormal.Algebra NearSpecV3.Wasm

inductive PreparedLocalsInstruction where
  | control (op : PreparedControlInstruction)
  | local (op : PreparedLocalOp) (index : Nat)
  deriving DecidableEq

def PreparedLocalsInstruction.instr : PreparedLocalsInstruction→Instr
  | .control op=>op.instr | .local op i=>op.instr i

def PreparedLocalsInstruction.tag : PreparedLocalsInstruction→Nat
  | .control op=>op.tag
  | .local .get _=>6 | .local .set _=>7 | .local .tee _=>8

def PreparedLocalsInstruction.immediate : PreparedLocalsInstruction→Nat
  | .control op=>op.immediate | .local _ i=>i

def preparedLocalsInspect (count : Nat) : Instr→Option PreparedLocalsInstruction
  | .localGet i=>if i<count then some (.local .get i) else none
  | .localSet i=>if i<count then some (.local .set i) else none
  | .localTee i=>if i<count then some (.local .tee i) else none
  | ins=>(preparedControlInspect ins).map .control

theorem prepared_locals_inspect (count : Nat) (ins : Instr) (op : PreparedLocalsInstruction)
    (accepted : preparedLocalsInspect count ins=some op) :
    ins=op.instr ∧ (∀kind index,op=.local kind index → index<count) := by
  unfold preparedLocalsInspect at accepted
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
  · obtain ⟨old,h,eq⟩:=Option.map_eq_some_iff.mp accepted
    cases eq
    exact ⟨prepared_control_inspect _ _ h,by intro k i eq;cases eq⟩

def preparedLocalsField (fn pc : Nat) (op : PreparedLocalsInstruction)
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
  else if field-23=op.tag then 1 else 0

def preparedLocalsTarget (pf : PFunc) (pc : Nat) : PreparedLocalsInstruction→Option Nat
  | .control op=>preparedControlTarget pf pc op | .local _ _=>some 0

theorem prepared_locals_target_checked (pf : PFunc) (pc : Nat) (op : PreparedLocalsInstruction)
    (target : Nat) (accepted : preparedLocalsTarget pf pc op=some target) :
    target<4294967296 ∧ (op=.control .block → ∃e,pf.endOf[pc]?=some e ∧ target=e+1) := by
  cases op with
  | control old =>
    have result:=prepared_control_target_checked pf pc old target accepted
    exact ⟨result.1,by intro eq;cases eq;exact result.2 rfl⟩
  | «local» kind index => cases accepted;exact ⟨by decide,by intro eq;cases eq⟩

def preparedLocalsCodeEntryCheck (pf : PFunc) (fn : Nat) (pub : List Fp) (pc : Nat) : Bool :=
  match pf.code[pc]?,pf.gas[pc]? with
  | some ins,some fee=>match preparedLocalsInspect pf.locals.size ins,preparedInspectFee fee with
    | some op,some amount=>match preparedLocalsTarget pf pc op with
      | some target=>(List.range 32).all (fun field=>decide
        (pub.getD (66+32*pc+field) 0=preparedLocalsField fn pc op fee amount target field))
      | none=>false
    | _,_=>false
  | _,_=>false

/-- The AIR parameter is checked against actual prepared locals, with no
parameters and only i32 local types. Header and CODE lengths stay exact. -/
def preparedLocalsCodeCheck (localCount : Nat) (pf : PFunc) (fn : Nat) (pub : List Fp) : Bool :=
  decide (fn=0 ∧ localCount≤4 ∧ pf.locals.size=localCount ∧ pf.type.params.isEmpty ∧
    pf.type.results.isEmpty ∧ (∀ty∈pf.locals.toList,ty=VT.i32) ∧
    0<pf.code.size ∧ pf.code.size<4294967296 ∧ pf.gas.size=pf.code.size ∧
    pub.length=66+32*pf.code.size ∧ preparedCodePublicSegment.count pub=pf.code.size) &&
  (List.range pf.code.size).all (preparedLocalsCodeEntryCheck pf fn pub)

theorem prepared_locals_code_shape (count : Nat) (pf : PFunc) (fn : Nat) (pub : List Fp)
    (accepted : preparedLocalsCodeCheck count pf fn pub=true) :
    fn=0 ∧ count≤4 ∧ pf.locals.size=count ∧ pf.type.params.isEmpty ∧
    pf.type.results.isEmpty ∧ (∀ty∈pf.locals.toList,ty=VT.i32) ∧
    0<pf.code.size ∧ pf.code.size<4294967296 ∧ pf.gas.size=pf.code.size ∧
    pub.length=66+32*pf.code.size ∧ preparedCodePublicSegment.count pub=pf.code.size := by
  simp only [preparedLocalsCodeCheck,Bool.and_eq_true] at accepted
  exact of_decide_eq_true accepted.1

theorem prepared_locals_code_entry (count : Nat) (pf : PFunc) (fn : Nat) (pub : List Fp)
    (accepted : preparedLocalsCodeCheck count pf fn pub=true) (pc : Nat) (live : pc<pf.code.size) :
    preparedLocalsCodeEntryCheck pf fn pub pc=true := by
  simp only [preparedLocalsCodeCheck,Bool.and_eq_true] at accepted
  exact List.all_eq_true.mp accepted.2 pc (List.mem_range.mpr live)

theorem prepared_locals_entry_checked (pf : PFunc) (fn : Nat) (pub : List Fp) (pc : Nat)
    (accepted : preparedLocalsCodeEntryCheck pf fn pub pc=true) :
    ∃op fee amount target,pf.code[pc]?=some op.instr ∧ pf.gas[pc]?=some fee ∧
      PreparedWasmCharge pf pc amount ∧ amount<u64Bound ∧
      (∀kind index,op=PreparedLocalsInstruction.local kind index → index<pf.locals.size) ∧
      preparedLocalsTarget pf pc op=some target ∧
      ∀field,field<32 → pub.getD (66+32*pc+field) 0=preparedLocalsField fn pc op fee amount target field := by
  unfold preparedLocalsCodeEntryCheck at accepted
  split at accepted
  · rename_i ins fee code gas
    split at accepted
    · rename_i op amount decoded feeDecoded
      split at accepted
      · rename_i target targetDecoded
        have feeSound:=prepared_inspect_fee fee amount feeDecoded
        have inspected:=prepared_locals_inspect pf.locals.size ins op decoded
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
def preparedLocalsSetupCheck (count : Nat) (cfg : NearCfg) (bytes : ByteArray) (method : String)
    (ctx : CallCtx) (pub : List Fp) (blockLevel : Bool := true) : Option PreparedRunCallEligible := do
  let setup ← preparedRunCallSetup cfg bytes method ctx blockLevel
  let fn:=setup.methodIndex-setup.program.m.imports.size
  let pf ← setup.program.funcs[fn]?
  if preparedLocalsCodeCheck count pf fn pub then some ⟨setup,pf⟩ else none

theorem prepared_locals_setup_checked (count : Nat) (cfg : NearCfg) (bytes : ByteArray)
    (method : String) (ctx : CallCtx) (pub : List Fp) (blockLevel : Bool)
    (eligible : PreparedRunCallEligible)
    (accepted : preparedLocalsSetupCheck count cfg bytes method ctx pub blockLevel=some eligible) :
    preparedRunCallSetup cfg bytes method ctx blockLevel=some eligible.setup ∧
    eligible.setup.program.funcs[eligible.setup.methodIndex-eligible.setup.program.m.imports.size]?=some eligible.func ∧
    preparedLocalsCodeCheck count eligible.func (eligible.setup.methodIndex-eligible.setup.program.m.imports.size) pub=true := by
  unfold preparedLocalsSetupCheck at accepted
  obtain ⟨setup,setupEq,rest⟩:=Option.bind_eq_some_iff.mp accepted
  obtain ⟨pf,fetch,rest⟩:=Option.bind_eq_some_iff.mp rest
  split at rest
  · rename_i checked
    cases rest
    exact ⟨setupEq,fetch,checked⟩
  · cases rest
end NearCompression
