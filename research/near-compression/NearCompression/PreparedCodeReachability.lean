import NearCompression.PreparedCodeBinding

namespace NearCompression
open ZkFormal.Algebra NearSpecV3.Wasm

/-- A bounded real instruction stream with a genuine terminal end. This
checks the actual last opcode, not the synthetic padded public records. -/
def preparedCodeTerminatedCheck (pf : PFunc) (pub : List Fp) : Bool :=
  preparedCodePublicCheck pf pub && (match pf.code[pf.code.size-1]? with | some .end_ => true | _ => false)

theorem prepared_code_terminated_shape (pf : PFunc) (pub : List Fp)
    (checked : preparedCodeTerminatedCheck pf pub=true) :
    preparedCodePublicCheck pf pub=true ∧ 0<pf.code.size ∧ pf.code.size≤16 ∧
      pf.code[pf.code.size-1]?=some .end_ := by
  simp only [preparedCodeTerminatedCheck,Bool.and_eq_true] at checked
  have shape:=checked.1
  simp only [preparedCodePublicCheck,Bool.and_eq_true] at shape
  have bounds:=of_decide_eq_true shape.1
  refine ⟨checked.1,bounds.1,bounds.2.1,?_⟩
  have last:=checked.2
  split at last
  · assumption
  · contradiction

/-- A real non-end opcode cannot advance into the synthetic public padding. -/
theorem prepared_code_live_successor (pf : PFunc) (pub : List Fp) (pc : Nat) (ins : Instr)
    (checked : preparedCodeTerminatedCheck pf pub=true) (live : pc<pf.code.size)
    (code : pf.code[pc]?=some ins) (continuing : ins≠.end_) : pc+1<pf.code.size := by
  have last:=(prepared_code_terminated_shape pf pub checked).2.2.2
  by_cases enough : pc+1<pf.code.size
  · exact enough
  · have eq : pc=pf.code.size-1 := by omega
    rw [←eq,code] at last
    have same : ins=.end_:=Option.some.inj last
    exact False.elim (continuing same)

/-- A checked selected live row has a real continuing opcode and actual fee,
so PC+1 remains within the real prepared code array. -/
theorem prepared_code_selected_successor (pf : PFunc) (pub : List Fp)
    (checked : preparedCodeTerminatedCheck pf pub=true) (pc : Nat) (live : pc<pf.code.size)
    (row next : Nat → Fp) (selected : ∀ i,i<16 → row i=if i=pc then 1 else 0)
    (notEnd : (preparedFetchPython 3).evalWith (preparedRowEnv row next (fun i=>pub.getD i 0) 0 0)=0) :
    pc+1<pf.code.size := by
  have shape:=prepared_code_terminated_shape pf pub checked
  obtain ⟨op,code,_,tags,_⟩:=prepared_code_selected_fee pf pub shape.1 pc live
    (Nat.lt_of_lt_of_le live shape.2.2.1) row next selected
  apply prepared_code_live_successor pf pub pc op.instr checked live code
  cases op with
  | constant v => intro eq;cases eq
  | add => intro eq;cases eq
  | drop => intro eq;cases eq
  | end_ =>
    have contradiction:=tags 3 (by decide)
    rw [notEnd] at contradiction
    have impossible : (0:Fp)=1 := contradiction
    exact False.elim ((by decide : (0:Fp)≠1) impossible)

end NearCompression
