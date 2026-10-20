import NearCompression.PreparedExecFinalRow

namespace NearCompression
open ZkFormal.Algebra NearSpecV3.Wasm

/-- The new slice adds only a void block and depth-zero conditional branch.
Other labels, loops, result arities and local-variable operations are rejected. -/
inductive PreparedControlInstruction where
  | legacy (op : PreparedPublicInstruction)
  | block
  | brIf
  deriving DecidableEq

def PreparedControlInstruction.instr : PreparedControlInstruction → Instr
  | .legacy op=>op.instr
  | .block=>.block none
  | .brIf=>.brIf 0

def PreparedControlInstruction.tag : PreparedControlInstruction → Nat
  | .legacy op=>op.tag
  | .block=>4
  | .brIf=>5

def PreparedControlInstruction.immediate : PreparedControlInstruction → Nat
  | .legacy op=>op.immediate
  | _=>0

def preparedControlInspect (ins : Instr) : Option PreparedControlInstruction :=
  match ins with
  | .block none=>some .block
  | .brIf 0=>some .brIf
  | other=>(preparedInspectInstruction other).map .legacy

theorem prepared_control_inspect (ins : Instr) (op : PreparedControlInstruction)
    (accepted : preparedControlInspect ins=some op) : ins=op.instr := by
  unfold preparedControlInspect at accepted
  split at accepted
  · cases accepted;rfl
  · cases accepted;rfl
  · obtain ⟨old,h,eq⟩:=Option.map_eq_some_iff.mp accepted
    cases eq
    exact (prepared_inspect_instruction _ old h).symm

/-- Twenty-nine canonical fields retain the original first25 positions,
append block/br_if tags and the actual prepared block-end target limbs. -/
def preparedControlField (fn pc : Nat) (op : PreparedControlInstruction)
    (fee : Option (IK × Fee)) (amount target field : Nat) : Fp :=
  if field<2 then Fp.ofNat ((fn/65536^field)%65536)
  else if field<4 then Fp.ofNat ((pc/65536^(field-2))%65536)
  else if field<8 then if field-4=op.tag then 1 else 0
  else if field<10 then Fp.ofNat ((op.immediate/65536^(field-8))%65536)
  else if field<14 then Fp.ofNat ((amount/65536^(field-10))%65536)
  else if field=14 then if fee.isSome then 1 else 0
  else if field<21 then match fee with
    | none=>0
    | some (kind,_)=>if field-15=preparedCodeKind kind then 1 else 0
  else if field<25 then 0
  else if field<27 then if field-21=op.tag then 1 else 0
  else Fp.ofNat ((target/65536^(field-27))%65536)

def preparedControlTarget (pf : PFunc) (pc : Nat) (op : PreparedControlInstruction) : Option Nat :=
  match op with
  | .block=>do
    let e←pf.endOf[pc]?
    if e+1<4294967296 then some (e+1) else none
  | _=>some 0

def preparedControlEntryCheck (pf : PFunc) (fn : Nat) (pub : List Fp) (pc : Nat) : Bool :=
  match pf.code[pc]?,pf.gas[pc]? with
  | some ins,some fee=>match preparedControlInspect ins,preparedInspectFee fee with
    | some op,some amount=>match preparedControlTarget pf pc op with
      | some target=>(List.range 29).all (fun field=>decide
          (pub.getD (66+29*pc+field) 0=preparedControlField fn pc op fee amount target field))
      | none=>false
    | _,_=>false
  | _,_=>false

def preparedControlCodeCheck (pf : PFunc) (fn : Nat) (pub : List Fp) : Bool :=
  decide (fn<4294967296 ∧ 0<pf.code.size ∧ pf.code.size<4294967296 ∧
    pf.gas.size=pf.code.size ∧ pub.length=66+29*pf.code.size ∧
    preparedCodePublicSegment.count pub=pf.code.size) &&
  (List.range pf.code.size).all (preparedControlEntryCheck pf fn pub)

theorem prepared_control_target_checked (pf : PFunc) (pc : Nat) (op : PreparedControlInstruction)
    (target : Nat) (accepted : preparedControlTarget pf pc op=some target) :
    target<4294967296 ∧ (op=.block → ∃ e,pf.endOf[pc]?=some e ∧ target=e+1) := by
  cases op with
  | legacy old => cases accepted;exact ⟨by decide,by intro h;cases h⟩
  | brIf => cases accepted;exact ⟨by decide,by intro h;cases h⟩
  | block =>
    unfold preparedControlTarget at accepted
    obtain ⟨e,h,rest⟩:=Option.bind_eq_some_iff.mp accepted
    split at rest
    · rename_i bounded
      cases rest
      exact ⟨bounded,fun _=>⟨e,h,rfl⟩⟩
    · cases rest

theorem prepared_control_entry_checked (pf : PFunc) (fn : Nat) (pub : List Fp) (pc : Nat)
    (accepted : preparedControlEntryCheck pf fn pub pc=true) :
    ∃ op fee amount target,pf.code[pc]?=some op.instr ∧ pf.gas[pc]?=some fee ∧
      PreparedWasmCharge pf pc amount ∧ amount<u64Bound ∧ target<4294967296 ∧
      (op=.block → ∃ e,pf.endOf[pc]?=some e ∧ target=e+1) ∧
      ∀ field,field<29 → pub.getD (66+29*pc+field) 0=preparedControlField fn pc op fee amount target field := by
  unfold preparedControlEntryCheck at accepted
  split at accepted
  · rename_i ins fee code gas
    split at accepted
    · rename_i op amount decoded feeDecoded
      split at accepted
      · rename_i target targetDecoded
        have feeSound:=prepared_inspect_fee fee amount feeDecoded
        have targetSound:=prepared_control_target_checked pf pc op target targetDecoded
        refine ⟨op,fee,amount,target,?_,gas,?_,feeSound.1,targetSound.1,targetSound.2,?_⟩
        · rw [code,prepared_control_inspect ins op decoded]
        · rcases feeSound.2 with ⟨none,zero⟩|⟨k,f,someFee,linear,cost⟩
          · exact Or.inl ⟨by rw [gas,none],zero⟩
          · exact Or.inr ⟨k,f,by rw [gas,someFee],linear,cost⟩
        · intro field bound
          exact of_decide_eq_true (List.all_eq_true.mp accepted field (List.mem_range.mpr bound))
      · cases accepted
    · cases accepted
  · cases accepted

/-- Real prepared step opens a void block at the actual operand-stack height,
using endOf metadata rather than a prover-chosen destination. -/
theorem prepared_control_step_block (cfg : NearCfg) (p : Prepared) (s : St)
    (f : Frame) (fs : List Frame) (pf : PFunc) (amount e : Nat)
    (frames : s.frames=f::fs) (func : p.funcs[f.fn]?=some pf)
    (code : pf.code[f.pc]?=some (.block none)) (target : pf.endOf[f.pc]?=some e)
    (charge : PreparedWasmCharge pf f.pc amount) (bounded : amount<u64Bound) (enough : amount≤s.gas.g) :
    step cfg p s=.cont (setFrame {s with gas:={s.gas with g:=s.gas.g-amount}}
      {f with pc:=f.pc+1,labels:={target:=e+1,arity:=0,height:=s.stack.size,isLoop:=false}::f.labels}) := by
  rw [prepared_wasm_step_charge cfg p s f fs pf (.block none) amount frames func code charge bounded enough]
  simp only [exec,target,btResults,Array.size_empty]

/-- Depth-zero conditional branch on a concrete i32 condition. A taken
branch keeps exactly the saved values and removes the block label; a false
condition only pops its operand. This is an actual step theorem, not an AIR
soundness theorem for the new control constraints. -/
theorem prepared_control_step_br_if (cfg : NearCfg) (p : Prepared) (s : St)
    (f : Frame) (fs : List Frame) (pf : PFunc) (amount : Nat)
    (values : Array Val) (condition : UInt32) (target height : Nat) (rest : Label)
    (frames : s.frames=f::fs) (func : p.funcs[f.fn]?=some pf)
    (code : pf.code[f.pc]?=some (.brIf 0))
    (labels : f.labels=[{target:=target,arity:=0,height:=height,isLoop:=false},rest])
    (stack : s.stack=values.push (.i32 condition))
    (charge : PreparedWasmCharge pf f.pc amount) (bounded : amount<u64Bound) (enough : amount≤s.gas.g) :
    step cfg p s=.cont (setFrame
      {s with
        stack:=(if condition.toNat=0 then values else values.extract 0 height)
        gas:={s.gas with g:=s.gas.g-amount}}
      {f with
        pc:=(if condition.toNat=0 then f.pc+1 else target)
        labels:=if condition.toNat=0 then f.labels else [rest]}) := by
  rw [prepared_wasm_step_charge cfg p s f fs pf (.brIf 0) amount frames func code charge bounded enough]
  simp only [exec,popN,popV,stack,Array.back?_push,Option.getD_some,Array.pop_push]
  by_cases zero : condition.toNat=0
  · simp only [zero,ne_eq,not_true_eq_false,ite_false,ite_true]
  · simp [zero,doBr,labels]


theorem prepared_control_code_checked (pf : PFunc) (fn : Nat) (pub : List Fp)
    (accepted : preparedControlCodeCheck pf fn pub=true) (pc : Nat) (live : pc<pf.code.size) :
    ∃ op fee amount target,pf.code[pc]?=some op.instr ∧ pf.gas[pc]?=some fee ∧
      PreparedWasmCharge pf pc amount ∧ amount<u64Bound ∧ target<4294967296 ∧
      (op=.block → ∃ e,pf.endOf[pc]?=some e ∧ target=e+1) ∧
      ∀ field,field<29 → pub.getD (66+29*pc+field) 0=preparedControlField fn pc op fee amount target field := by
  simp only [preparedControlCodeCheck,Bool.and_eq_true] at accepted
  exact prepared_control_entry_checked pf fn pub pc
    (List.all_eq_true.mp accepted.2 pc (List.mem_range.mpr live))

/-- Nested end removes only its block label and continues execution; it must
not set the function-return flag used by the earlier straight-line slice. -/
theorem prepared_control_step_nested_end (cfg : NearCfg) (p : Prepared) (s : St)
    (f : Frame) (fs : List Frame) (pf : PFunc) (amount : Nat) (lab rest : Label)
    (frames : s.frames=f::fs) (func : p.funcs[f.fn]?=some pf)
    (code : pf.code[f.pc]?=some .end_) (labels : f.labels=[lab,rest])
    (charge : PreparedWasmCharge pf f.pc amount) (bounded : amount<u64Bound) (enough : amount≤s.gas.g) :
    step cfg p s=.cont (setFrame {s with gas:={s.gas with g:=s.gas.g-amount}}
      {f with pc:=f.pc+1,labels:=[rest]}) := by
  rw [prepared_wasm_step_charge cfg p s f fs pf .end_ amount frames func code charge bounded enough]
  simp only [exec,labels]

end NearCompression
