import NearCompression.SHA384NodeChunk
import NearCompression.SHA384SharedRouting

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 NearSpecV3.SHA512
set_option maxRecDepth 65536

theorem sha384_chunk_receive_match (base count bits uses : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384NodeChunkAir base count bits uses) pub tr) {t r : Nat}
    (ht : t<(sha384NodeChunkAir base count bits uses).tables.length) (hr : r<tr.height t)
    {i : Interaction} (hi : i∈(sha384NodeChunkAir base count bits uses).tables[t]!.interactions)
    (hs : i.send=false) (hm : i.multNat tr t r pub≠0) :
    ∃ t',t'<(sha384NodeChunkAir base count bits uses).tables.length ∧ ∃ r',r'<tr.height t' ∧
      ∃ i'∈(sha384NodeChunkAir base count bits uses).tables[t']!.interactions,
        i'.bus=i.bus ∧ i'.send=true ∧ i'.msgVal tr t' r' pub=i.msgVal tr t r pub ∧
          i'.multNat tr t' r' pub≠0 := by
  have positive := ZkFormal.Chacha.tableBusCount_pos hr hi hm
  rw [hs] at positive
  have bound := ZkFormal.Chacha.busCount_go_ge tr pub i.bus false (i.msgVal tr t r pub)
    (sha384NodeChunkAir base count bits uses).tables 0 t ht
  simp only [Nat.zero_add] at bound
  have recv : busCount (sha384NodeChunkAir base count bits uses).toAir tr pub i.bus false (i.msgVal tr t r pub)≠0 := by
    unfold busCount;omega
  have balance := h.balance i.bus (i.msgVal tr t r pub)
  have noPublic (send : Bool) : pubCount (sha384NodeChunkAir base count bits uses) pub i.bus send (i.msgVal tr t r pub)=0 := by
    apply ZkFormal.Chacha.pubCount_zero
    intro seg member hb
    simp [sha384NodeChunkAir] at member
  rw [noPublic true,noPublic false,Nat.add_zero,Nat.add_zero] at balance
  have send : busCount (sha384NodeChunkAir base count bits uses).toAir tr pub i.bus true (i.msgVal tr t r pub)≠0 := by omega
  obtain ⟨t',ht',hc⟩ := ZkFormal.Chacha.busCount_go_pos tr pub i.bus true _ _ 0 send
  simp only [Nat.zero_add] at hc
  obtain ⟨r',hr',i',hi',hb',hs',msg,mult⟩ := ZkFormal.Chacha.exists_of_tableBusCount hc
  exact ⟨t',ht',r',hr',i',hi',hb',hs',msg,mult⟩


def chunkRecordSend (base bits : Nat) : Interaction :=
  ⟨4,(List.range bits).map (fun b => .col (2+b) false),chunkGlobal base (.col 0 false :: sharedCols (2+bits) 176),true⟩

theorem sha384_chunk_record_sender (base count bits uses t : Nat)
    (ht : t<(sha384NodeChunkAir base count bits uses).tables.length) (i : Interaction)
    (hi : i∈(sha384NodeChunkAir base count bits uses).tables[t]!.interactions)
    (hb : i.bus=4) (hs : i.send=true) : t=2 ∧ i=chunkRecordSend base bits := by
  have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 := by
    simp only [sha384NodeChunkAir,List.length_cons,List.length_nil] at ht;omega
  rcases cases with rfl | rfl | rfl | rfl
  all_goals simp only [sha384NodeChunkAir,List.getElem!_cons_zero,List.getElem!_cons_succ,
    List.mem_cons,List.not_mem_nil,or_false] at hi
  · rcases hi with rfl | rfl | rfl <;> simp_all
  · rcases hi with rfl | rfl | rfl <;> simp_all
  · rcases hi with rfl | rfl | rfl | rfl <;> simp_all [chunkRecordSend]
  · subst i;simp at hs

/-- Zero evaluated bits give exactly zero natural multiplicity. -/
theorem chunk_mult_zero (tr : Trace Fp) (t r : Nat) (pub : List Fp) (xs : List Expr) (k : Nat)
    (zero : ∀ e,e∈xs → e.eval tr t r pub=0) : Interaction.multNat.go tr t r pub xs k=0 := by
  induction xs generalizing k with
  | nil => rfl
  | cons x xs ih =>
    have z := zero x (by simp)
    have tail := ih (k+1) (by intro e he;exact zero e (by simp [he]))
    simp only [Interaction.multNat.go,z,show (0:Fp)≠1 from by decide,ite_false,Nat.zero_add,tail]

theorem sha384_chunk_record_mult_active (base count bits uses : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384NodeChunkAir base count bits uses) pub tr) (r : Nat) (hr : r<tr.height 2)
    (hm : (chunkRecordSend base bits).multNat tr 2 r pub≠0) : tr.cell 2 r 1=1 := by
  have hc (e : Expr) (he : e∈(sha384NodeChunkAir base count bits uses).tables[2]!.constraints) : e.eval tr 2 r pub=0 :=
    h.constr 2 (by simp [sha384NodeChunkAir]) r hr e he
  have bit := hc (instructionBitConstraint 1) (by simp [sha384NodeChunkAir,sharedPrefix])
  change tr.cell 2 r 1*(tr.cell 2 r 1 + -(1:Fp))=0 at bit
  have boolean : tr.cell 2 r 1=0 ∨ tr.cell 2 r 1=1 := by grind
  rcases boolean with inactive | active
  · have zeros (b : Nat) (hb : b<bits) : tr.cell 2 r (2+b)=0 := by
      have eq := hc (.mul (sharedSub (.const 1) (.col 1 false)) (.col (2+b) false))
        (List.mem_append_right _ (List.mem_flatMap.mpr ⟨b,List.mem_range.mpr hb,by simp⟩))
      change ((1:Fp)+ -tr.cell 2 r 1)*tr.cell 2 r (2+b)=0 at eq
      rw [inactive] at eq
      grind
    have zero := chunk_mult_zero tr 2 r pub ((List.range bits).map (fun b=>.col (2+b) false)) 0 (by
      intro e he
      obtain ⟨b,hb,rfl⟩ := List.mem_map.mp he
      exact zeros b (List.mem_range.mp hb))
    exact False.elim (hm zero)
  · exact active

/-- Each active ordered use receives one full active compression record. -/
theorem sha384_chunk_use_record (base count bits uses : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384NodeChunkAir base count bits uses) pub tr) (r : Nat) (hr : r<tr.height 3)
    (active : tr.cell 3 r 1=1) :
    ∃ s,s<tr.height 2 ∧ tr.cell 2 s 1=1 ∧
      Fp.ofNat base+tr.cell 2 s 0=tr.cell 3 r 2 ∧
      (List.range 176).map (fun j=>tr.cell 2 s (2+bits+j))=
        (List.range 176).map (fun j=>tr.cell 3 r (3+j)) := by
  let i : Interaction := ⟨4,[.col 1 false],sharedCols 2 177,false⟩
  have hi : i∈(sha384NodeChunkAir base count bits uses).tables[3]!.interactions := by simp [i,sha384NodeChunkAir]
  have hm : i.multNat tr 3 r pub≠0 := by
    simp [i,Interaction.multNat,Interaction.multNat.go,Expr.eval,Expr.evalWith,rowEnv,active]
  obtain ⟨t,ht,s,hs,j,hj,bus,send,msg,mult⟩ := sha384_chunk_receive_match base count bits uses pub tr h
    (by simp [sha384NodeChunkAir]) hr hi rfl hm
  obtain ⟨rfl,rfl⟩ := sha384_chunk_record_sender base count bits uses t ht j hj bus send
  have act := sha384_chunk_record_mult_active base count bits uses pub tr h s hs mult
  change ((chunkGlobal base (.col 0 false::sharedCols (2+bits) 176)).map (fun e=>e.eval tr 2 s pub))=
    ((.col 2 false::sharedCols 3 176).map (fun e=>e.eval tr 3 r pub)) at msg
  simp only [chunkGlobal,List.headD_cons,List.drop_succ_cons,List.drop_zero,List.map_cons,sharedCols,List.map_map,
    Function.comp_def,Expr.eval,Expr.evalWith,rowEnv,List.cons.injEq] at msg
  exact ⟨s,hs,act,msg.1,msg.2⟩

/-- Exact natural fanout, retaining every configured multiplicity bit. -/
theorem sha384_chunk_use_counts (base count bits uses : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384NodeChunkAir base count bits uses) pub tr) (m : List Fp) :
    tableBusCount (sha384NodeChunkAir base count bits uses).tables[2]!.interactions tr 2 pub 4 true m=
      tableBusCount (sha384NodeChunkAir base count bits uses).tables[3]!.interactions tr 3 pub 4 false m := by
  have balance := h.balance 4 m
  have noPublic (send : Bool) : pubCount (sha384NodeChunkAir base count bits uses) pub 4 send m=0 := by
    apply ZkFormal.Chacha.pubCount_zero
    intro seg member hb
    simp [sha384NodeChunkAir] at member
  rw [noPublic true,noPublic false,Nat.add_zero,Nat.add_zero] at balance
  have empty (xs : List Nat) : xs.foldr (fun _ (acc : Nat)=>acc) 0=0 := by induction xs <;> simp_all
  simpa [empty,busCount,busCount.go,sha384NodeChunkAir,tableBusCount,List.range_succ] using balance

/-- Adding the same global base to a nonempty message is injective; all remaining
fields are preserved verbatim. This uses field cancellation, not a hash assumption. -/
theorem chunk_global_match (base : Nat) (tr : Trace Fp) (t r u s : Nat) (pub : List Fp)
    (a b : List Expr) (ha : a≠[]) (hb : b≠[]) :
    (chunkGlobal base a).map (fun e=>e.eval tr t r pub)=
      (chunkGlobal base b).map (fun e=>e.eval tr u s pub) ↔
    a.map (fun e=>e.eval tr t r pub)=b.map (fun e=>e.eval tr u s pub) := by
  cases a with
  | nil => contradiction
  | cons a as =>
    cases b with
    | nil => contradiction
    | cons b bs =>
      simp only [chunkGlobal,List.headD_cons,List.drop_succ_cons,List.drop_zero,List.map_cons,List.cons.injEq,
        Expr.eval,Expr.evalWith,rowEnv]
      grind

end NearCompression
