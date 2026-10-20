import NearCompression.MerklePaddingBridge
import ZkFormal.NearV3.Sched.Complete.Cmp

/-! Exact natural bus-count preservation for the shortened nonempty Merkle
renderer. Its nonzero inverse padding column contributes no multiplicity. -/
set_option autoImplicit false
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Render
open ZkFormal.NearV3.Candidates ZkFormal.NearV3.Candidates.MerkleRender
open ZkFormal.NearV3.Sched.Complete

theorem merkle_current_cells (n : Nat) (lv : List (List MNode)) (pub : List Fp)
    (logSize r c : Nat) :
    (merkleTraceAtLog n lv pub logSize).cell T_MRK r c =
    (MerkleEmpty.liftTrace (trace n lv) T_MRK pub).cell T_MRK r c :=
  (merkle_old_cells n lv pub r c).symm

theorem merkle_interaction_values (n : Nat) (lv : List (List MNode)) (pub : List Fp)
    (logSize r : Nat) (i : Interaction) (hi : i∈MerkleEmpty.table.interactions) :
    i.msgVal (merkleTraceAtLog n lv pub logSize) T_MRK r pub =
      i.msgVal (MerkleEmpty.liftTrace (trace n lv) T_MRK pub) T_MRK r pub ∧
    i.multNat (merkleTraceAtLog n lv pub logSize) T_MRK r pub =
      i.multNat (MerkleEmpty.liftTrace (trace n lv) T_MRK pub) T_MRK r pub := by
  simp only [MerkleEmpty.table,MerklePublic.table,List.mem_map] at hi
  obtain ⟨a,ha,rfl⟩ := hi
  obtain ⟨j,hj,rfl⟩ := ha
  simp only [Mrk.interactions,List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl <;>
    simp [Interaction.msgVal,Interaction.multNat,Interaction.multNat.go,
      MerkleEmpty.interaction,MerklePublic.interaction,MerklePublic.expression,
      MerkleEmpty.gate,MerkleEmpty.active,Dsl.send,Dsl.recv,Dsl.c,Dsl.not,Dsl.k,
      Dsl.mid,Dsl.smul,Dsl.sub,Expr.eval,Expr.evalWith,rowEnv,merkle_current_cells]
theorem merkle_padding_mult_zero (n : Nat) (lv : List (List MNode)) (pub : List Fp)
    (r : Nat) (hr : (MrkGen.recs n).length+1≤r)
    (i : Interaction) (hi : i∈MerkleEmpty.table.interactions) :
    i.multNat (MerkleEmpty.liftTrace (trace n lv) T_MRK pub) T_MRK r pub=0 := by
  have r0 : r≠0 := by omega
  have rr : ¬r-1<(MrkGen.recs n).length := by omega
  simp only [MerkleEmpty.table,MerklePublic.table,List.mem_map] at hi
  obtain ⟨a,ha,rfl⟩ := hi
  obtain ⟨j,hj,rfl⟩ := ha
  simp only [Mrk.interactions,List.mem_cons,List.not_mem_nil,or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl <;>
    simp [Interaction.multNat,Interaction.multNat.go,
      MerkleEmpty.interaction,MerklePublic.interaction,MerklePublic.expression,
      MerkleEmpty.gate,MerkleEmpty.active,Dsl.send,Dsl.recv,Dsl.c,Dsl.not,Dsl.k,Dsl.sub,
      Expr.eval,Expr.evalWith,rowEnv,MerkleEmpty.liftTrace,trace,MrkGen.cell,
      MerkleEmpty.emptyCol,MerkleEmpty.inverseCol,Mrk.sg,Mrk.wf,Mrk.rt,Mrk.gM,Mrk.gO,r0,rr] <;>
    decide
theorem merkle_row_count_eq (n : Nat) (lv : List (List MNode)) (pub : List Fp)
    (logSize r bus : Nat) (send : Bool) (message : List Fp) :
    (MerkleEmpty.table.interactions.map fun i =>
      if i.bus=bus ∧ i.send=send ∧ i.msgVal (merkleTraceAtLog n lv pub logSize) T_MRK r pub=message
      then i.multNat (merkleTraceAtLog n lv pub logSize) T_MRK r pub else 0).sum =
    (MerkleEmpty.table.interactions.map fun i =>
      if i.bus=bus ∧ i.send=send ∧ i.msgVal (MerkleEmpty.liftTrace (trace n lv) T_MRK pub) T_MRK r pub=message
      then i.multNat (MerkleEmpty.liftTrace (trace n lv) T_MRK pub) T_MRK r pub else 0).sum := by
  apply congrArg List.sum
  apply List.map_congr_left
  intro i hi
  have values := merkle_interaction_values n lv pub logSize r i hi
  rw [values.1,values.2]

/-- Exact natural multiplicity for every bus, direction and message agrees
with the actual old nonempty lift renderer. No traffic equality premise. -/
theorem merkle_shrink_bus_count (n : Nat) (lv : List (List MNode)) (pub : List Fp)
    (newLog : Nat) (hlog : newLog≤19)
    (fits : (MrkGen.recs n).length+1≤2^newLog)
    (bus : Nat) (send : Bool) (message : List Fp) :
    tableBusCount MerkleEmpty.table.interactions (merkleTraceAtLog n lv pub newLog) T_MRK pub bus send message =
    tableBusCount MerkleEmpty.table.interactions
      (MerkleEmpty.liftTrace (trace n lv) T_MRK pub) T_MRK pub bus send message := by
  let g := fun r => (MerkleEmpty.table.interactions.map fun i =>
    if i.bus=bus ∧ i.send=send ∧ i.msgVal (MerkleEmpty.liftTrace (trace n lv) T_MRK pub) T_MRK r pub=message
    then i.multNat (MerkleEmpty.liftTrace (trace n lv) T_MRK pub) T_MRK r pub else 0).sum
  have hz : ∀ r,(MrkGen.recs n).length+1≤r → g r=0 := by
    intro r hr
    unfold g
    rw [List.map_congr_left (g := fun _ => 0) (fun i hi => by
      rw [merkle_padding_mult_zero n lv pub r hr i hi]
      simp)]
    exact sum_map_zero _
  have fitsOld : (MrkGen.recs n).length+1≤2^19 :=
    Nat.le_trans fits (Nat.pow_le_pow_right (by decide) hlog)
  simp only [busCount_sum,merkle_row_count_eq]
  change ((List.range (2^newLog)).map g).sum=((List.range (2^19)).map g).sum
  rw [sum_range_trunc g hz _ fits,sum_range_trunc g hz _ fitsOld]

/-- Restate against the actual honest renderer under its nonempty branch. -/
theorem merkle_shrink_honest_bus_count (n : Nat) (lv : List (List MNode)) (pub : List Fp)
    (nonempty : n≠0) (newLog : Nat) (hlog : newLog≤19)
    (fits : (MrkGen.recs n).length+1≤2^newLog)
    (bus : Nat) (send : Bool) (message : List Fp) :
    tableBusCount MerkleEmpty.table.interactions (merkleTraceAtLog n lv pub newLog) T_MRK pub bus send message =
    tableBusCount MerkleEmpty.table.interactions (MerkleRender.honestTrace n lv pub) T_MRK pub bus send message := by
  rw [MerkleRender.honestTrace,ite_eq_right nonempty]
  exact merkle_shrink_bus_count n lv pub newLog hlog fits bus send message
end NearCompression
