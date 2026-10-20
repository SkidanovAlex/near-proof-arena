import NearCompression.PreparedTypedValue
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra NearSpecV3.Wasm

/-- Actual right-to-left operand popping; the type is i64, not merely a Nat. -/
theorem prepared_typed_pop_i64 (s : St) (value : UInt64) :
    popN (pushV s (.i64 value))=(value.toNat,s) := by
  simp [popN,popV,pushV]

/-- Range-enforced four-limb addition determines the exact typed interpreter
successor. Whole EXEC fetch, stack selection and gas wiring are separate. -/
theorem prepared_typed_exec_add64 (row : Nat→Fp) (h : instructionAdd64Holds row)
    (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (pf : PFunc) :
    exec cfg p (pushV (pushV s (.i64 (UInt64.ofNat (instructionAdd64Word row 0))))
      (.i64 (UInt64.ofNat (instructionAdd64Word row 4)))) f pf (.num 0x7C)=
      .cont (setFrame (pushI64 s (instructionAdd64Word row 8)) {f with pc:=f.pc+1}) := by
  have a:=sha512_word_limb_bound row 0 (by intro i hi;exact instruction_add64_ranges row h _ (by omega))
  have b:=sha512_word_limb_bound row 4 (by intro i hi;exact instruction_add64_ranges row h _ (by omega))
  have arithmetic:=instruction_add64_binop row h
  have numeric : execNum (pushV (pushV s (.i64 (UInt64.ofNat (instructionAdd64Word row 0))))
      (.i64 (UInt64.ofNat (instructionAdd64Word row 4)))) 0x7C=
      .ok (pushI64 s (instructionAdd64Word row 8)) := by
    simp [execNum,prepared_typed_pop_i64,UInt64.toNat_ofNat,Nat.mod_eq_of_lt a,Nat.mod_eq_of_lt b,
      arithmetic,pure,Except.pure]
  simp only [exec,numeric]

/-- eqz consumes i64 and produces i32. The limb-sum inverse gadget is sound
because its sum is below the field modulus, even for values divisible by P. -/
theorem prepared_typed_exec_eqz64 (row : Nat→Fp) (h : preparedTypedEqzHolds row)
    (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (pf : PFunc) :
    exec cfg p (pushV s (.i64 (UInt64.ofNat (instructionAdd64Word row 0)))) f pf (.num 0x50)=
      .cont (setFrame (pushI32 s (row 13).toNat) {f with pc:=f.pc+1}) := by
  have bound:=prepared_typed_word_bound row h
  have result:=prepared_typed_eqz row h
  have numeric : execNum (pushV s (.i64 (UInt64.ofNat (instructionAdd64Word row 0)))) 0x50=
      .ok (pushI32 s (row 13).toNat) := by
    rw [result]
    by_cases zero : instructionAdd64Word row 0=0
    all_goals simp [execNum,prepared_typed_pop_i64,UInt64.toNat_ofNat,Nat.mod_eq_of_lt bound,Num.b2,zero,pure,Except.pure]
    all_goals rfl
  simp only [exec,numeric]

theorem prepared_typed_exec_const64 (cfg : NearCfg) (p : Prepared) (s : St)
    (f : Frame) (pf : PFunc) (value : UInt64) :
    exec cfg p s f pf (.i64Const value)=
      .cont (setFrame (pushV s (.i64 value)) {f with pc:=f.pc+1}) := rfl

/-- Reuses actual prepared charge semantics, with no invented per-opcode fee. -/
theorem prepared_typed_step_charge (cfg : NearCfg) (p : Prepared) (s : St)
    (f : Frame) (fs : List Frame) (pf : PFunc) (op : Instr) (amount : Nat)
    (frames : s.frames=f::fs) (func : p.funcs[f.fn]?=some pf) (code : pf.code[f.pc]?=some op)
    (metadata : PreparedWasmCharge pf f.pc amount) (bounded : amount<u64Bound) (enough : amount≤s.gas.g) :
    step cfg p s=exec cfg p {s with gas:={s.gas with g:=s.gas.g-amount}} f pf op :=
  prepared_wasm_step_charge cfg p s f fs pf op amount frames func code metadata bounded enough

end NearCompression
