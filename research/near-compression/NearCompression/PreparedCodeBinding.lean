import NearCompression.PreparedWasmExecution

namespace NearCompression
open ZkFormal.Algebra ZkFormal.Air NearSpecV3.Wasm

inductive PreparedPublicInstruction where
  | constant (value : UInt32)
  | add | drop | end_
  deriving DecidableEq, Repr

def PreparedPublicInstruction.instr : PreparedPublicInstruction → Instr
  | .constant v => .i32Const v
  | .add => .num 0x6A
  | .drop => .drop
  | .end_ => .end_
def PreparedPublicInstruction.tag : PreparedPublicInstruction → Nat
  | .constant _ => 0 | .add => 1 | .drop => 2 | .end_ => 3
def PreparedPublicInstruction.immediate : PreparedPublicInstruction → Nat
  | .constant v => v.toNat | _ => 0

def preparedInspectInstruction : Instr → Option PreparedPublicInstruction
  | .i32Const v => some (.constant v)
  | .num op => if op=0x6A then some .add else none
  | .drop => some .drop
  | .end_ => some .end_
  | _ => none

def preparedInspectFee : Option (IK × Fee) → Option Nat
  | none => some 0
  | some (k,fee) => if k≠IK.linear ∧ fee.l=0 ∧ fee.c<u64Bound then some fee.c else none

/-- Ten public fields in the frozen CODE schema, constructed from inspected
actual instructions and actual prepared range-charge metadata. -/
def PreparedPublicInstruction.field (op : PreparedPublicInstruction) (amount field : Nat) : Fp :=
  if field<4 then (if field=op.tag then 1 else 0)
  else if field<6 then Fp.ofNat ((op.immediate/65536^(field-4))%65536)
  else Fp.ofNat ((amount/65536^(field-6))%65536)

def preparedCodeEntryCheck (pf : PFunc) (pub : List Fp) (pc : Nat) : Bool :=
  match pf.code[pc]?,pf.gas[pc]? with
  | some ins,some fee =>
    match preparedInspectInstruction ins,preparedInspectFee fee with
    | some op,some amount => (List.range 10).all (fun field=>decide (pub.getD (56+10*pc+field) 0=op.field amount field))
    | _,_ => false
  | _,_ => false

/-- Also checks the existing synthetic-end padding convention. These padded
records are never claimed to be real executable instructions. -/
def preparedCodePublicCheck (pf : PFunc) (pub : List Fp) : Bool :=
  decide (0<pf.code.size ∧ pf.code.size≤16 ∧ pf.gas.size=pf.code.size ∧ pub.length=216) &&
  (List.range 16).all (fun pc=>if pc<pf.code.size then preparedCodeEntryCheck pf pub pc
    else (List.range 10).all (fun field=>decide (pub.getD (56+10*pc+field) 0=(PreparedPublicInstruction.end_).field 0 field)))

theorem prepared_inspect_instruction (ins : Instr) (op : PreparedPublicInstruction)
    (accepted : preparedInspectInstruction ins=some op) : op.instr=ins := by
  cases ins <;> simp only [preparedInspectInstruction] at accepted
  all_goals try contradiction
  all_goals try (cases accepted;rfl)
  split at accepted
  · rename_i eq
    cases accepted
    simp only [PreparedPublicInstruction.instr,eq]
  · contradiction

theorem prepared_inspect_fee (fee : Option (IK × Fee)) (amount : Nat)
    (accepted : preparedInspectFee fee=some amount) :
    amount<u64Bound ∧ (fee=none ∧ amount=0 ∨ ∃ k f,fee=some (k,f) ∧ f.l=0 ∧ f.c=amount) := by
  cases fee with
  | none => cases accepted;exact ⟨by decide,Or.inl ⟨rfl,rfl⟩⟩
  | some pair =>
    rcases pair with ⟨k,f⟩
    simp only [preparedInspectFee] at accepted
    split at accepted
    · rename_i valid
      cases accepted
      exact ⟨valid.2.2,Or.inr ⟨k,f,rfl,valid.2.1,rfl⟩⟩
    · contradiction

theorem prepared_code_entry_checked (pf : PFunc) (pub : List Fp) (pc : Nat)
    (accepted : preparedCodeEntryCheck pf pub pc=true) :
    ∃ (op : PreparedPublicInstruction) (amount : Nat),pf.code[pc]?=some op.instr ∧ amount<u64Bound ∧ PreparedWasmCharge pf pc amount ∧
      ∀ field,field<10 → pub.getD (56+10*pc+field) 0=op.field amount field := by
  unfold preparedCodeEntryCheck at accepted
  split at accepted
  · rename_i ins fee code gas
    split at accepted
    · rename_i op amount decoded feeDecoded
      have fields:=List.all_eq_true.mp accepted
      have feeSound:=prepared_inspect_fee fee amount feeDecoded
      refine ⟨op,amount,?_,feeSound.1,?_,?_⟩
      · rw [prepared_inspect_instruction ins op decoded];exact code
      · rcases feeSound.2 with ⟨none,zero⟩ | ⟨k,f,someFee,linear,cost⟩
        · exact Or.inl ⟨by rw [gas,none],zero⟩
        · exact Or.inr ⟨k,f,by rw [gas,someFee],linear,cost⟩
      · intro field bound
        exact of_decide_eq_true (fields field (List.mem_range.mpr bound))
    · contradiction
  · contradiction

theorem prepared_code_public_checked (pf : PFunc) (pub : List Fp)
    (accepted : preparedCodePublicCheck pf pub=true) (pc : Nat) (live : pc<pf.code.size) :
    ∃ (op : PreparedPublicInstruction) (amount : Nat),pf.code[pc]?=some op.instr ∧ amount<u64Bound ∧ PreparedWasmCharge pf pc amount ∧
      ∀ field,field<10 → pub.getD (56+10*pc+field) 0=op.field amount field := by
  simp only [preparedCodePublicCheck,Bool.and_eq_true] at accepted
  have both:=accepted
  have shape:=of_decide_eq_true both.1
  have entry:=(List.all_eq_true.mp both.2) pc (List.mem_range.mpr (Nat.lt_of_lt_of_le live shape.2.1))
  simp only [live,ite_true] at entry
  exact prepared_code_entry_checked pf pub pc entry

theorem prepared_code_digit_nat (word power : Nat) :
    (Fp.ofNat ((word/65536^power)%65536)).toNat=(word/65536^power)%65536 := by
  rw [Fp.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have small:=Nat.mod_lt (word/65536^power) (by decide : 0<65536)
  unfold ZkFormal.Algebra.P
  omega

theorem prepared_code_digits64 (word : Nat) (bound : word<u64Bound) :
    preparedGasWord (fun i=>(word/65536^i)%65536)=word := by
  simp only [preparedGasWord,Nat.reducePow,Nat.div_one]
  unfold u64Bound at bound
  omega

theorem prepared_code_digits32 (word : Nat) (bound : word<4294967296) :
    word%65536+65536*((word/65536)%65536)=word := by omega

/-- The one-hot AIR fetch reconstructs the genuine prepared fee without a
64-bit-to-field alias: each public limb is separately canonical. -/
theorem prepared_code_selected_fee (pf : PFunc) (pub : List Fp)
    (accepted : preparedCodePublicCheck pf pub=true) (pc : Nat) (live : pc<pf.code.size)
    (hpc : pc<16) (row next : Nat → Fp)
    (selected : ∀ i,i<16 → row i=if i=pc then 1 else 0) :
    ∃ op : PreparedPublicInstruction,pf.code[pc]?=some op.instr ∧
      PreparedWasmCharge pf pc (preparedFeeValue row pub) ∧
      (∀ tag,tag<4 → (preparedFetchPython tag).evalWith
        (preparedRowEnv row next (fun i=>pub.getD i 0) 0 0)=if tag=op.tag then 1 else 0) ∧
      preparedImmediateWord row next (fun i=>pub.getD i 0)=op.immediate := by
  obtain ⟨op,amount,code,bound,charge,fields⟩:=prepared_code_public_checked pf pub accepted pc live
  have fetch (field : Nat) (hf : field<10) :
      (preparedFetchPython field).evalWith (preparedRowEnv row next (fun i=>pub.getD i 0) 0 0)=op.field amount field := by
    rw [prepared_fetch_python_eval,prepared_fetch_selected row next _ 0 0 pc hpc selected,fields field hf]
  have limb (i : Nat) (hi : i<4) :
      (preparedGasFee row pub i).toNat=(amount/65536^i)%65536 := by
    unfold preparedGasFee
    rw [prepared_gas_fetch_source row next pub 0 0,fetch (6+i) (by omega)]
    simp only [PreparedPublicInstruction.field,ite_eq_right (by omega : ¬6+i<4),
      ite_eq_right (by omega : ¬6+i<6),Nat.add_sub_cancel_left,prepared_code_digit_nat]
  have fee : preparedFeeValue row pub=amount := by
    unfold preparedFeeValue preparedGasWord
    dsimp only
    rw [limb 0 (by decide),limb 1 (by decide),limb 2 (by decide),limb 3 (by decide)]
    exact prepared_code_digits64 amount bound
  refine ⟨op,code,?_,?_,?_⟩
  · rw [fee];exact charge
  · intro tag ht
    rw [fetch tag (by omega)]
    simp only [PreparedPublicInstruction.field,ht,ite_true]
  · unfold preparedImmediateWord
    rw [fetch 4 (by decide),fetch 5 (by decide)]
    simp only [PreparedPublicInstruction.field,Nat.reduceLT,ite_false,ite_true,
      Nat.reduceSub,Nat.reducePow,Nat.div_one]
    have lo:=prepared_code_digit_nat op.immediate 0
    have hi:=prepared_code_digit_nat op.immediate 1
    simp only [Nat.reducePow,Nat.div_one] at lo hi
    rw [lo,hi]
    apply prepared_code_digits32
    cases op with
    | constant v => exact v.toNat_lt
    | add => decide
    | drop => decide
    | end_ => decide

theorem prepared_code_field_bound (op : PreparedPublicInstruction) (amount field : Nat)
    (low : 4≤field) (high : field<10) : (op.field amount field).toNat<65536 := by
  unfold PreparedPublicInstruction.field
  simp only [ite_eq_right (by omega : ¬field<4)]
  split <;> rw [prepared_code_digit_nat] <;> exact Nat.mod_lt _ (by decide)

/-- Checking all real and padded CODE entries discharges the canonical public
limb assumptions used by the instruction AIR soundness theorems. -/
theorem prepared_code_public_limb_bounds (pf : PFunc) (pub : List Fp)
    (accepted : preparedCodePublicCheck pf pub=true) :
    (∀ pc,pc<16 → ∀ limb,limb<4 → (pub.getD (56+10*pc+(6+limb)) 0).toNat<65536) ∧
    (∀ pc,pc<16 → ∀ limb,limb<2 → (pub.getD (56+10*pc+(4+limb)) 0).toNat<65536) := by
  have fields (pc field : Nat) (hp : pc<16) (lo : 4≤field) (hi : field<10) :
      (pub.getD (56+10*pc+field) 0).toNat<65536 := by
    by_cases live : pc<pf.code.size
    · obtain ⟨op,amount,_,_,_,eq⟩:=prepared_code_public_checked pf pub accepted pc live
      rw [eq field hi]
      exact prepared_code_field_bound op amount field lo hi
    · have check:=accepted
      simp only [preparedCodePublicCheck,Bool.and_eq_true] at check
      have padding:=(List.all_eq_true.mp check.2) pc (List.mem_range.mpr hp)
      simp only [live,ite_false] at padding
      have eq:=of_decide_eq_true ((List.all_eq_true.mp padding) field (List.mem_range.mpr hi))
      rw [eq]
      exact prepared_code_field_bound .end_ 0 field lo hi
  constructor
  · intro pc hp limb hl
    exact fields pc (6+limb) hp (by omega) (by omega)
  · intro pc hp limb hl
    exact fields pc (4+limb) hp (by omega) (by omega)

/-- Executable public encoder. Unsupported real entries are rejected by the
checker; the caller supplies exactly the existing 56 boundary/header fields. -/
def preparedCodePublicBuild (pf : PFunc) (header : List Fp) : Option (List Fp) :=
  let records := (List.range 16).flatMap (fun pc =>
    let decoded := do
      let ins ← pf.code[pc]?
      let fee ← pf.gas[pc]?
      let op ← preparedInspectInstruction ins
      let amount ← preparedInspectFee fee
      pure (op,amount)
    let pair := decoded.getD (.end_,0)
    (List.range 10).map (fun field=>pair.1.field pair.2 field))
  let pub := header++records
  if header.length=56 ∧ preparedCodePublicCheck pf pub=true then some pub else none

theorem prepared_code_public_build_checked (pf : PFunc) (header pub : List Fp)
    (built : preparedCodePublicBuild pf header=some pub) : preparedCodePublicCheck pf pub=true := by
  unfold preparedCodePublicBuild at built
  dsimp only at built
  split at built
  · rename_i valid
    cases built
    exact valid.2
  · contradiction

end NearCompression
