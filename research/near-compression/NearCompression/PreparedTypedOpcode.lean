import NearCompression.PreparedTypedSource
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
def preparedTypedOpcodeColumn (i : Nat) : Nat :=
  [466,467,468,469,605,606,683,684,685,1280,1281,1282].getD i 0
private theorem opcode_column_bounds : ∀i:Fin 12,
    preparedTypedOpcodeColumn i<1285 ∧ preparedTypedOpcodeColumn i≠682 ∧ preparedTypedOpcodeColumn i≠1283 := by decide
private theorem opcode_at : ∀count:Fin 5,
    (preparedTypedLiteralExec count)[1286]?=some preparedTypedLiteralExec1286 := by decide

theorem prepared_typed_opcode_selected (count : Nat) (hc : count≤4)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (localH : TableLocal (preparedTypedLiteralExecTable count) tr t pub) (hr : r<tr.height t)
    (selected : Nat) (hs : selected<12) (opcode : tr.cell t r (preparedTypedOpcodeColumn selected)=1) :
    ∀i,i<12 → tr.cell t r (preparedTypedOpcodeColumn i)=if i=selected then 1 else 0 := by
  let row:=fun i=>tr.cell t r (preparedTypedOpcodeColumn i)
  have bits : ∀i,i<12 → (row i).toNat≤1 := by
    intro i hi
    have b:=opcode_column_bounds ⟨i,hi⟩
    exact prepared_typed_source_boolean count hc tr t r pub localH hr _ b.1 b.2.1 b.2.2
  have h:=localH.constr r hr _ (List.mem_of_getElem? (opcode_at ⟨count,by omega⟩))
  have sum : preparedFieldSum 12 row=1 := by
    change ((row 0+row 1+(row 2+row 3))+(row 4+row 5+(row 6+row 7)))+
      (row 8+row 9+(row 10+row 11))+ -(1:Fp)=0 at h
    simp only [preparedFieldSum,Nat.reduceAdd]
    grind
  obtain ⟨idx,ib,hot⟩:=prepared_onehot 12 0 row (by decide) (by simpa only [Nat.zero_add] using bits) (by simpa only [Nat.zero_add] using sum)
  simp only [Nat.zero_add] at hot
  have eq : idx=selected := by
    have x:=hot selected hs
    change row selected=1 at opcode
    by_cases z:selected=idx
    · omega
    · rw [if_neg z] at x
      have one : (0:Fp)≠1:=by decide
      exact False.elim (one (x.symm.trans opcode))
  subst idx
  exact hot
end NearCompression
