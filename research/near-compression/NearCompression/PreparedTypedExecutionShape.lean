import NearCompression.PreparedTypedEqzAuthenticated
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

private theorem columns : ∀i:Fin 12,
    preparedTypedOpcodeColumn i<1285 ∧ preparedTypedOpcodeColumn i≠682 ∧ preparedTypedOpcodeColumn i≠1283 := by decide
private theorem opcode_at : ∀count:Fin 5,
    (preparedTypedLiteralExec count)[1286]?=some preparedTypedLiteralExec1286 := by decide
private theorem last_done_at : ∀count:Fin 5,
    (preparedTypedLiteralExec count)[1618+66*(4-count.val)]?=some preparedLocalsLiteralExec0997 := by decide

/-- Exact literal Boolean columns and the opcode sum select one of all twelve
supported tags. No selected-opcode or prepared-code equality is supplied. -/
theorem prepared_typed_opcode_total (count : Nat) (hc : count≤4)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub) (hr : r<tr.height t) :
    ∃tag,tag<12 ∧ ∀i,i<12 → tr.cell t r (preparedTypedOpcodeColumn i)=if i=tag then 1 else 0 := by
  let row:=fun i=>tr.cell t r (preparedTypedOpcodeColumn i)
  have bits : ∀i,i<12 → (row i).toNat≤1 := by
    intro i hi
    have bounds:=columns ⟨i,hi⟩
    exact prepared_typed_source_boolean count hc tr t r pub localH hr _ bounds.1 bounds.2.1 bounds.2.2
  have h:=localH.constr r hr _ (List.mem_of_getElem? (opcode_at ⟨count,by omega⟩))
  have sum : preparedFieldSum 12 row=1 := by
    change ((row 0+row 1+(row 2+row 3))+(row 4+row 5+(row 6+row 7)))+
      (row 8+row 9+(row 10+row 11))+ -(1:Fp)=0 at h
    simp only [preparedFieldSum,Nat.reduceAdd]
    grind
  obtain ⟨tag,bound,hot⟩:=prepared_onehot 12 0 row (by decide)
    (by simpa only [Nat.zero_add] using bits) (by simpa only [Nat.zero_add] using sum)
  exact ⟨tag,bound,by simpa only [Nat.zero_add] using hot⟩

/-- The exact last-row DONE constraint prohibits an active final trace row. -/
theorem prepared_typed_table_active_nonlast (count : Nat) (hc : count≤4)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub)
    (hr : r<tr.height t) (active : tr.cell t r 41=0) : r+1<tr.height t := by
  have h:=localH.constr r hr _ (List.mem_of_getElem? (last_done_at ⟨count,by omega⟩))
  change (if r+1=tr.height t then (1:Fp) else 0)*(tr.cell t r 41+ -(1:Fp))=0 at h
  by_cases last:r+1=tr.height t
  · rw [ite_eq_left last,active] at h
    have impossible : (1:Fp)=0:=by grind
    exact False.elim ((by decide : (1:Fp)≠0) impossible)
  · omega

theorem prepared_typed_active_nonlast (codeCount count : Nat) (hc : count≤4)
    (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP (preparedTypedLiteralAir codeCount count) pub tr)
    (r : Nat) (hr : r<tr.height 0) (active : tr.cell 0 r 41=0) : r+1<tr.height 0 :=
  prepared_typed_table_active_nonlast count hc tr 0 r pub
    (prepared_typed_exec_local codeCount count tr pub holds) hr active
end NearCompression
