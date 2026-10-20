import NearCompression.PreparedControlState

namespace NearCompression
open ZkFormal.Algebra NearSpecV3.Wasm

/-- Versioned local-variable slice. The new AIR authenticates these indices
in CODE; its source-membership/refinement layer remains separate. -/
inductive PreparedLocalOp where
  | get | set | tee
  deriving DecidableEq

def PreparedLocalOp.instr (op : PreparedLocalOp) (index : Nat) : Instr :=
  match op with | .get=>.localGet index | .set=>.localSet index | .tee=>.localTee index

def preparedLocalsWord (row : Nat→Fp) (index : Nat) : Nat :=
  (preparedCodeLimb row (686+32*index)).toNat+
    65536*(preparedCodeLimb row (702+32*index)).toNat

def preparedLocalsArray (row : Nat→Fp) (count : Nat) : Array Val :=
  ((List.range count).map (fun i=>Val.i32 (UInt32.ofNat (preparedLocalsWord row i)))).toArray

/-- Extends the existing real control-state relation; count must be checked
against actual prepared local types/count at setup, not inferred from rows. -/
def PreparedLocalsState (row : Nat→Fp) (s : St) (f : Frame)
    (fs : List Frame) (sp count : Nat) (root : Label) : Prop :=
  PreparedControlState row s f fs sp root ∧ count≤4 ∧ f.locals=preparedLocalsArray row count

theorem prepared_locals_lookup (row : Nat→Fp) (count index : Nat) (hi : index<count) :
    (preparedLocalsArray row count)[index]?=
      some (.i32 (UInt32.ofNat (preparedLocalsWord row index))) := by
  simp [preparedLocalsArray,hi]

/-- Actual interpreter get; nondefault lookup is an explicit future
CODE/index-range discharge point. Gas and other state fields are preserved. -/
theorem prepared_locals_exec_get (cfg : NearCfg) (p : Prepared) (s : St)
    (f : Frame) (pf : PFunc) (index : Nat) (value : Val)
    (lookup : f.locals[index]?=some value) :
    exec cfg p s f pf (.localGet index)=
      .cont (setFrame (pushV s value) {f with pc:=f.pc+1}) := by
  simp only [exec,lookup,Option.getD_some]

theorem prepared_locals_exec_set (cfg : NearCfg) (p : Prepared) (s : St)
    (f : Frame) (pf : PFunc) (index : Nat) (xs : Array Val) (value : Val)
    (stack : s.stack=xs.push value) :
    exec cfg p s f pf (.localSet index)=
      .cont (setFrame {s with stack:=xs} {f with pc:=f.pc+1,locals:=f.locals.set! index value}) := by
  simp [exec,popV,stack]

theorem prepared_locals_exec_tee (cfg : NearCfg) (p : Prepared) (s : St)
    (f : Frame) (pf : PFunc) (index : Nat) (xs : Array Val) (value : Val)
    (stack : s.stack=xs.push value) :
    exec cfg p s f pf (.localTee index)=
      .cont (setFrame s {f with pc:=f.pc+1,locals:=f.locals.set! index value}) := by
  simp [exec,stack]

/-- Real prepared range charging is reused unchanged, including absent gas
entries represented by PreparedWasmCharge. No mock opcode fee is introduced. -/
theorem prepared_locals_step_charge (cfg : NearCfg) (p : Prepared) (s : St)
    (f : Frame) (fs : List Frame) (pf : PFunc) (op : PreparedLocalOp) (index amount : Nat)
    (frames : s.frames=f::fs) (func : p.funcs[f.fn]?=some pf)
    (code : pf.code[f.pc]?=some (op.instr index))
    (metadata : PreparedWasmCharge pf f.pc amount)
    (bounded : amount<u64Bound) (enough : amount≤s.gas.g) :
    step cfg p s=exec cfg p {s with gas:={s.gas with g:=s.gas.g-amount}}
      f pf (op.instr index) :=
  prepared_wasm_step_charge cfg p s f fs pf (op.instr index) amount frames func code metadata bounded enough

end NearCompression
