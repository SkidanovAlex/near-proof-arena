import NearCompression.PreparedCodeBus
import NearCompression.PreparedRunCall

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 NearSpecV3.Wasm

def preparedCodeKind : IK → Nat
  | .pure=>0 | .unreach=>1 | .pre=>2 | .post=>3 | .between=>4 | .linear=>5

/-- Canonical25-field descriptor: function/PC limbs, opcode one-hot, immediate,
constant fee, charge presence/kind, and zero linear-fee limbs. -/
def preparedVariableField (fn pc : Nat) (op : PreparedPublicInstruction)
    (fee : Option (IK × Fee)) (amount field : Nat) : Fp :=
  if field<2 then Fp.ofNat ((fn/65536^field)%65536)
  else if field<4 then Fp.ofNat ((pc/65536^(field-2))%65536)
  else if field<8 then if field-4=op.tag then 1 else 0
  else if field<10 then Fp.ofNat ((op.immediate/65536^(field-8))%65536)
  else if field<14 then Fp.ofNat ((amount/65536^(field-10))%65536)
  else if field=14 then if fee.isSome then 1 else 0
  else if field<21 then match fee with
    | none=>0
    | some (kind,_)=>if field-15=preparedCodeKind kind then 1 else 0
  else 0

def preparedCodeVariableEntryCheck (pf : PFunc) (fn : Nat) (pub : List Fp) (pc : Nat) : Bool :=
  match pf.code[pc]?,pf.gas[pc]? with
  | some ins,some fee =>
    match preparedInspectInstruction ins,preparedInspectFee fee with
    | some op,some amount => (List.range 25).all (fun field=>
      decide (pub.getD (66+25*pc+field) 0=preparedVariableField fn pc op fee amount field))
    | _,_=>false
  | _,_=>false

def preparedCodeVariableCheck (pf : PFunc) (fn : Nat) (pub : List Fp) : Bool :=
  decide (fn<4294967296 ∧ 0<pf.code.size ∧ pf.code.size<4294967296 ∧
    pf.gas.size=pf.code.size ∧ pub.length=66+25*pf.code.size ∧
    preparedCodePublicSegment.count pub=pf.code.size) &&
  (List.range pf.code.size).all (preparedCodeVariableEntryCheck pf fn pub)

theorem prepared_code_variable_entry_checked (pf : PFunc) (fn : Nat) (pub : List Fp) (pc : Nat)
    (accepted : preparedCodeVariableEntryCheck pf fn pub pc=true) :
    ∃ (op : PreparedPublicInstruction) (fee : Option (IK × Fee)) (amount : Nat),
      pf.code[pc]?=some op.instr ∧ pf.gas[pc]?=some fee ∧ preparedInspectFee fee=some amount ∧
      amount<u64Bound ∧ PreparedWasmCharge pf pc amount ∧
      ∀ field,field<25 → pub.getD (66+25*pc+field) 0=preparedVariableField fn pc op fee amount field := by
  unfold preparedCodeVariableEntryCheck at accepted
  split at accepted
  · rename_i ins fee code gas
    split at accepted
    · rename_i op amount decoded feeDecoded
      have fields:=List.all_eq_true.mp accepted
      have feeSound:=prepared_inspect_fee fee amount feeDecoded
      refine ⟨op,fee,amount,?_,gas,feeDecoded,feeSound.1,?_,?_⟩
      · rw [prepared_inspect_instruction ins op decoded];exact code
      · rcases feeSound.2 with ⟨none,zero⟩|⟨k,f,someFee,linear,cost⟩
        · exact Or.inl ⟨by rw [gas,none],zero⟩
        · exact Or.inr ⟨k,f,by rw [gas,someFee],linear,cost⟩
      · intro field bound
        exact of_decide_eq_true (fields field (List.mem_range.mpr bound))
    · cases accepted
  · cases accepted

theorem prepared_code_variable_checked (pf : PFunc) (fn : Nat) (pub : List Fp)
    (accepted : preparedCodeVariableCheck pf fn pub=true) (pc : Nat) (live : pc<pf.code.size) :
    ∃ (op : PreparedPublicInstruction) (fee : Option (IK × Fee)) (amount : Nat),
      pf.code[pc]?=some op.instr ∧ pf.gas[pc]?=some fee ∧ preparedInspectFee fee=some amount ∧
      amount<u64Bound ∧ PreparedWasmCharge pf pc amount ∧
      ∀ field,field<25 → pub.getD (66+25*pc+field) 0=preparedVariableField fn pc op fee amount field := by
  simp only [preparedCodeVariableCheck,Bool.and_eq_true] at accepted
  exact prepared_code_variable_entry_checked pf fn pub pc
    ((List.all_eq_true.mp accepted.2) pc (List.mem_range.mpr live))

theorem prepared_code_public_record_field (pub : List Fp) (pc field : Nat) (hf : field<25) :
    (preparedCodePublicSegment.record pub pc).getD field 0=pub.getD (66+25*pc+field) 0 := by
  simp only [PubSeg.record,preparedCodePublicSegment,List.map_nil,List.nil_append,PubSeg.startOffset,
    List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range hf,Option.map_some,Option.getD_some]
  rw [Nat.mul_comm pc 25]

/-- The public record's two canonical PC limbs identify its exact index. -/
theorem prepared_code_variable_record_pc (pf : PFunc) (fn : Nat) (pub : List Fp)
    (accepted : preparedCodeVariableCheck pf fn pub=true) (pc : Nat) (live : pc<pf.code.size) :
    ((preparedCodePublicSegment.record pub pc).getD 2 0).toNat+
      65536*((preparedCodePublicSegment.record pub pc).getD 3 0).toNat=pc := by
  obtain ⟨op,fee,amount,_,_,_,_,_,fields⟩:=prepared_code_variable_checked pf fn pub accepted pc live
  rw [prepared_code_public_record_field pub pc 2 (by decide),prepared_code_public_record_field pub pc 3 (by decide),
    fields 2 (by decide),fields 3 (by decide)]
  simp only [preparedVariableField,Nat.reduceLT,ite_false,ite_true,Nat.reduceSub,prepared_code_digit_nat,
    Nat.reducePow,Nat.div_one]
  have shape:=accepted
  simp only [preparedCodeVariableCheck,Bool.and_eq_true,decide_eq_true_eq] at shape
  have d0:=prepared_code_digit_nat pc 0
  have d1:=prepared_code_digit_nat pc 1
  simp only [Nat.reducePow,Nat.div_one] at d0 d1
  rw [d0,d1]
  exact prepared_code_digits32 pc (by omega)

/-- Canonical public records remove the existential public index: it is exactly
EXEC's numeric PC, which is now proved live in the actual prepared function. -/
theorem prepared_code_variable_fetch (ec cc boundary : List Expr) (count : Nat)
    (tr : Trace Fp) (pub : List Fp) (holds : HoldsP (preparedCodeBusAir ec cc boundary count) pub tr)
    (source : PreparedCodeOrderSource (preparedCodeDataTable cc))
    (inactive : ∀ i,i<25 → preparedCodeInactive (172+i)∈cc)
    (pf : PFunc) (fn : Nat) (checked : preparedCodeVariableCheck pf fn pub=true)
    (r : Nat) (hr : r<tr.height 0) :
    let pc:=preparedCodeExecPC (tr.cell 0 r)
    pc<pf.code.size ∧ ∃ (op : PreparedPublicInstruction) (fee : Option (IK × Fee)) (amount : Nat),
      pf.code[pc]?=some op.instr ∧ pf.gas[pc]?=some fee ∧ preparedInspectFee fee=some amount ∧
      amount<u64Bound ∧ PreparedWasmCharge pf pc amount ∧
      ∀ field,field<25 → (preparedCodeFetch.msgVal tr 0 r pub).getD field 0=
        preparedVariableField fn pc op fee amount field := by
  obtain ⟨_,_,_,⟨j,hj,published⟩,_⟩:=prepared_code_fetch_at_pc ec cc boundary count tr pub holds source inactive r hr
  have shape:=checked
  simp only [preparedCodeVariableCheck,Bool.and_eq_true,decide_eq_true_eq] at shape
  have live : j<pf.code.size:=by rw [shape.1.2.2.2.2.2] at hj;exact hj
  have canonical:=prepared_code_variable_record_pc pf fn pub checked j live
  have lo:=congrArg (fun xs:List Fp=>xs.getD 2 0) published
  have hi:=congrArg (fun xs:List Fp=>xs.getD 3 0) published
  change _=(preparedCodeBits 0).eval tr 0 r pub at lo
  change _=(preparedCodeBits 16).eval tr 0 r pub at hi
  rw [prepared_code_bits_eval] at lo hi
  have index : j=preparedCodeExecPC (tr.cell 0 r) := by
    rw [lo,hi] at canonical
    exact canonical.symm
  subst j
  refine ⟨live,?_⟩
  obtain ⟨op,fee,amount,code,gas,inspect,bound,charge,fields⟩:=prepared_code_variable_checked pf fn pub checked _ live
  refine ⟨op,fee,amount,code,gas,inspect,bound,charge,?_⟩
  intro field hf
  rw [←published,prepared_code_public_record_field pub _ field hf,fields field hf]

/-- A header-preserving executable encoder; the final check rejects unsupported
instructions/charges and noncanonical code count/length. -/
def preparedCodeVariableBuild (pf : PFunc) (fn : Nat) (header : List Fp) : Option (List Fp) :=
  let records := (List.range pf.code.size).flatMap fun pc=>
    let decoded := do
      let ins ← pf.code[pc]?
      let fee ← pf.gas[pc]?
      let op ← preparedInspectInstruction ins
      let amount ← preparedInspectFee fee
      pure (op,fee,amount)
    let (op,fee,amount):=decoded.getD (.end_,none,0)
    (List.range 25).map (preparedVariableField fn pc op fee amount)
  let pub:=header++records
  if header.length=66 ∧ preparedCodeVariableCheck pf fn pub=true then some pub else none

theorem prepared_code_variable_build_checked (pf : PFunc) (fn : Nat) (header pub : List Fp)
    (built : preparedCodeVariableBuild pf fn header=some pub) : preparedCodeVariableCheck pf fn pub=true := by
  unfold preparedCodeVariableBuild at built
  dsimp only at built
  split at built
  · rename_i valid
    cases built
    exact valid.2
  · cases built

/-- Real preparation/loading/resolution followed by actual resolved-function
lookup and variable-length public CODE checking. No supplied PFunc is accepted. -/
def preparedCodePreparedCheck (cfg : NearCfg) (code : ByteArray) (method : String) (ctx : CallCtx)
    (pub : List Fp) (blockLevel : Bool := true) : Option PreparedRunCallEligible := do
  let setup ← preparedRunCallSetup cfg code method ctx blockLevel
  let fn:=setup.methodIndex-setup.program.m.imports.size
  let pf ← setup.program.funcs[fn]?
  if preparedCodeVariableCheck pf fn pub then some ⟨setup,pf⟩ else none

theorem prepared_code_prepared_checked (cfg : NearCfg) (code : ByteArray) (method : String)
    (ctx : CallCtx) (pub : List Fp) (blockLevel : Bool) (eligible : PreparedRunCallEligible)
    (accepted : preparedCodePreparedCheck cfg code method ctx pub blockLevel=some eligible) :
    preparedRunCallSetup cfg code method ctx blockLevel=some eligible.setup ∧
    eligible.setup.program.funcs[eligible.setup.methodIndex-eligible.setup.program.m.imports.size]?=some eligible.func ∧
    preparedCodeVariableCheck eligible.func (eligible.setup.methodIndex-eligible.setup.program.m.imports.size) pub=true := by
  unfold preparedCodePreparedCheck at accepted
  obtain ⟨setup,setupEq,rest⟩:=Option.bind_eq_some_iff.mp accepted
  obtain ⟨pf,fetch,rest⟩:=Option.bind_eq_some_iff.mp rest
  split at rest
  · rename_i checked
    cases rest
    exact ⟨setupEq,fetch,checked⟩
  · cases rest

/-- Public CODE is now linked to the function actually obtained by the real
outer setup. This is fetch provenance, not yet the new EXEC table's full-step refinement. -/
theorem prepared_code_prepared_fetch (ec cc boundary : List Expr) (count : Nat)
    (tr : Trace Fp) (pub : List Fp) (holds : HoldsP (preparedCodeBusAir ec cc boundary count) pub tr)
    (source : PreparedCodeOrderSource (preparedCodeDataTable cc))
    (inactive : ∀ i,i<25 → preparedCodeInactive (172+i)∈cc)
    (cfg : NearCfg) (code : ByteArray) (method : String) (ctx : CallCtx) (blockLevel : Bool)
    (eligible : PreparedRunCallEligible)
    (accepted : preparedCodePreparedCheck cfg code method ctx pub blockLevel=some eligible)
    (r : Nat) (hr : r<tr.height 0) :
    preparedRunCallSetup cfg code method ctx blockLevel=some eligible.setup ∧
    eligible.setup.program.funcs[eligible.setup.methodIndex-eligible.setup.program.m.imports.size]?=some eligible.func ∧
    (let pc:=preparedCodeExecPC (tr.cell 0 r)
    pc<eligible.func.code.size ∧ ∃ (op : PreparedPublicInstruction) (fee : Option (IK × Fee)) (amount : Nat),
      eligible.func.code[pc]?=some op.instr ∧ eligible.func.gas[pc]?=some fee ∧
      preparedInspectFee fee=some amount ∧ amount<u64Bound ∧ PreparedWasmCharge eligible.func pc amount ∧
      ∀ field,field<25 → (preparedCodeFetch.msgVal tr 0 r pub).getD field 0=
        preparedVariableField (eligible.setup.methodIndex-eligible.setup.program.m.imports.size) pc op fee amount field) := by
  obtain ⟨setup,fetch,checked⟩:=prepared_code_prepared_checked cfg code method ctx pub blockLevel eligible accepted
  exact ⟨setup,fetch,prepared_code_variable_fetch ec cc boundary count tr pub holds source inactive
    eligible.func _ checked r hr⟩

end NearCompression
