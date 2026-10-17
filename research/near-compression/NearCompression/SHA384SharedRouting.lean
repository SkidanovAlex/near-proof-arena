import NearCompression.SHA384SharedCore
import NearCompression.SHA384EndpointRouting

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 NearSpecV3.SHA512
set_option maxRecDepth 65536

/-- Positive exact natural receive count forces an actual equal sending record.
No field-count substitution or caller matching premise is used. -/
theorem sha384_shared_receive_match (f0 f1 : List (Nat × Nat)) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384SharedAir f0 f1) pub tr) {t r : Nat}
    (ht : t<(sha384SharedAir f0 f1).tables.length) (hr : r<tr.height t)
    {i : Interaction} (hi : i∈(sha384SharedAir f0 f1).tables[t]!.interactions)
    (hs : i.send=false) (hm : i.multNat tr t r pub≠0) :
    ∃ t',t'<(sha384SharedAir f0 f1).tables.length ∧ ∃ r',r'<tr.height t' ∧
      ∃ i'∈(sha384SharedAir f0 f1).tables[t']!.interactions,
        i'.bus=i.bus ∧ i'.send=true ∧ i'.msgVal tr t' r' pub=i.msgVal tr t r pub ∧
          i'.multNat tr t' r' pub≠0 := by
  have positive := ZkFormal.Chacha.tableBusCount_pos hr hi hm
  rw [hs] at positive
  have bound := ZkFormal.Chacha.busCount_go_ge tr pub i.bus false (i.msgVal tr t r pub)
    (sha384SharedAir f0 f1).tables 0 t ht
  simp only [Nat.zero_add] at bound
  have recv : busCount (sha384SharedAir f0 f1).toAir tr pub i.bus false (i.msgVal tr t r pub)≠0 := by
    unfold busCount;omega
  have balance := h.balance i.bus (i.msgVal tr t r pub)
  have noPublic (send : Bool) : pubCount (sha384SharedAir f0 f1) pub i.bus send (i.msgVal tr t r pub)=0 := by
    apply ZkFormal.Chacha.pubCount_zero
    intro seg member hb
    simp [sha384SharedAir] at member
  rw [noPublic true,noPublic false,Nat.add_zero,Nat.add_zero] at balance
  have send : busCount (sha384SharedAir f0 f1).toAir tr pub i.bus true (i.msgVal tr t r pub)≠0 := by omega
  obtain ⟨t',ht',hc⟩ := ZkFormal.Chacha.busCount_go_pos tr pub i.bus true _ _ 0 send
  simp only [Nat.zero_add] at hc
  obtain ⟨r',hr',i',hi',hb',hs',msg,mult⟩ := ZkFormal.Chacha.exists_of_tableBusCount hc
  exact ⟨t',ht',r',hr',i',hi',hb',hs',msg,mult⟩

theorem sha384_shared_record_sender (f0 f1 : List (Nat × Nat)) (t : Nat)
    (ht : t<(sha384SharedAir f0 f1).tables.length) (i : Interaction)
    (hi : i∈(sha384SharedAir f0 f1).tables[t]!.interactions)
    (hb : i.bus=4) (hs : i.send=true) :
    t=2 ∧ i=⟨4,[.col 2 false,.col 3 false],.col 0 false :: sharedCols 4 176,true⟩ := by
  have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by
    simp only [sha384SharedAir,List.length_cons,List.length_nil] at ht;omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [sha384SharedAir,List.getElem!_cons_zero,List.getElem!_cons_succ,
    sha384SharedCore,sha384SharedEndpoint,sha384SharedRecords,sha384SharedCalls,sha384SharedInput,
    List.mem_cons,List.not_mem_nil,or_false] at hi
  · rcases hi with rfl | rfl | rfl <;> simp_all
  · rcases hi with rfl | rfl | rfl <;> simp_all
  · rcases hi with rfl | rfl | rfl | rfl <;> simp_all
  · rcases hi with rfl | rfl <;> simp_all
  · obtain ⟨b,hb',rfl⟩ := List.mem_map.mp hi;simp at hb
  · obtain ⟨b,hb',rfl⟩ := List.mem_map.mp hi;simp at hb

theorem sha384_shared_record_mult_active (f0 f1 : List (Nat × Nat)) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384SharedAir f0 f1) pub tr) (r : Nat) (hr : r<tr.height 2)
    (hm : (⟨4,[.col 2 false,.col 3 false],.col 0 false :: sharedCols 4 176,true⟩ : Interaction).multNat tr 2 r pub≠0) :
    tr.cell 2 r 1=1 := by
  have hc (e : Expr) (he : e∈sha384SharedRecords.constraints) : e.eval tr 2 r pub=0 :=
    h.constr 2 (by simp [sha384SharedAir]) r hr e he
  have bit := hc (instructionBitConstraint 1) (by simp [sha384SharedRecords,sharedPrefix])
  change tr.cell 2 r 1*(tr.cell 2 r 1 + -(1:Fp))=0 at bit
  have boolean : tr.cell 2 r 1=0 ∨ tr.cell 2 r 1=1 := by grind
  rcases boolean with inactive | active
  · have b0 := hc (.mul (sharedSub (.const 1) (.col 1 false)) (.col 2 false)) (by simp [sha384SharedRecords])
    have b1 := hc (.mul (sharedSub (.const 1) (.col 1 false)) (.col 3 false)) (by simp [sha384SharedRecords])
    change ((1:Fp)+ -tr.cell 2 r 1)*tr.cell 2 r 2=0 at b0
    change ((1:Fp)+ -tr.cell 2 r 1)*tr.cell 2 r 3=0 at b1
    rw [inactive] at b0 b1
    have zero0 : tr.cell 2 r 2=0 := by grind
    have zero1 : tr.cell 2 r 3=0 := by grind
    simp [Interaction.multNat,Interaction.multNat.go,Expr.eval,Expr.evalWith,rowEnv,zero0,zero1] at hm
    exact False.elim ((by decide : (0:Fp)≠1) hm)
  · exact active

/-- Every active call step consumes an actual active full-state/block/output
record, including all8 state words and the48-byte digest representation. -/
theorem sha384_shared_call_record (f0 f1 : List (Nat × Nat)) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384SharedAir f0 f1) pub tr) (r : Nat) (hr : r<tr.height 3)
    (active : tr.cell 3 r 2=1) :
    ∃ s,s<tr.height 2 ∧ tr.cell 2 s 1=1 ∧
      tr.cell 2 s 0=tr.cell 3 r 1 ∧
      (List.range 176).map (fun j => tr.cell 2 s (4+j))=
        (List.range 176).map (fun j => tr.cell 3 r (6+j)) := by
  let i : Interaction := ⟨4,[.col 2 false],.col 1 false :: sharedCols 6 176,false⟩
  have hi : i∈(sha384SharedAir f0 f1).tables[3]!.interactions := by
    simp [i,sha384SharedAir,sha384SharedCalls]
  have hm : i.multNat tr 3 r pub≠0 := by
    simp [i,Interaction.multNat,Interaction.multNat.go,Expr.eval,Expr.evalWith,rowEnv,active]
  obtain ⟨t,ht,s,hs,j,hj,bus,send,msg,mult⟩ := sha384_shared_receive_match f0 f1 pub tr h
    (by simp [sha384SharedAir]) hr hi rfl hm
  obtain ⟨rfl,rfl⟩ := sha384_shared_record_sender f0 f1 t ht j hj bus send
  have act := sha384_shared_record_mult_active f0 f1 pub tr h s hs mult
  change ((.col 0 false :: sharedCols 4 176).map (fun e => e.eval tr 2 s pub))=
    ((.col 1 false :: sharedCols 6 176).map (fun e => e.eval tr 3 r pub)) at msg
  simp only [List.map_cons,sharedCols,List.map_map,Function.comp_def,Expr.eval,Expr.evalWith,rowEnv,List.cons.injEq] at msg
  exact ⟨s,hs,act,msg.1,msg.2⟩

/-- Complete per-message natural fanout conservation, not just existence of a
matching record. This retains the actual two-bit multiplicity on every sender. -/
theorem sha384_shared_use_counts (f0 f1 : List (Nat × Nat)) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384SharedAir f0 f1) pub tr) (m : List Fp) :
    tableBusCount sha384SharedRecords.interactions tr 2 pub 4 true m=
      tableBusCount sha384SharedCalls.interactions tr 3 pub 4 false m := by
  have balance := h.balance 4 m
  have noPublic (send : Bool) : pubCount (sha384SharedAir f0 f1) pub 4 send m=0 := by
    apply ZkFormal.Chacha.pubCount_zero
    intro seg member hb
    simp [sha384SharedAir] at member
  rw [noPublic true,noPublic false,Nat.add_zero,Nat.add_zero] at balance
  have empty (xs : List Nat) : xs.foldr (fun _ (acc : Nat) => acc) 0=0 := by
    induction xs <;> simp_all
  simpa [empty,busCount,busCount.go,sha384SharedAir,sha384SharedCore,sha384SharedEndpoint,
    sha384SharedRecords,sha384SharedCalls,sha384SharedInput,tableBusCount,List.range_succ] using balance

end NearCompression
