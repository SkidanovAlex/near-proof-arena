import NearCompression.SHA384DirectSemantics

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2

theorem sha384_direct_receive_match (n : Nat) (fixed : List (Nat × Nat)) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384DirectInputAir n fixed) pub tr) {t r : Nat}
    (ht : t<(sha384DirectInputAir n fixed).tables.length) (hr : r<tr.height t)
    {i : Interaction} (hi : i ∈ (sha384DirectInputAir n fixed).tables[t]!.interactions)
    (hs : i.send=false) (busBound : i.bus≠5) (hm : i.multNat tr t r pub≠0) :
    ∃ t',t'<(sha384DirectInputAir n fixed).tables.length ∧ ∃ r',r'<tr.height t' ∧
      ∃ i' ∈ (sha384DirectInputAir n fixed).tables[t']!.interactions,
      i'.bus=i.bus ∧ i'.send=true ∧ i'.msgVal tr t' r' pub=i.msgVal tr t r pub ∧ i'.multNat tr t' r' pub≠0 := by
  have positive := ZkFormal.Chacha.tableBusCount_pos hr hi hm
  rw [hs] at positive
  have bound := ZkFormal.Chacha.busCount_go_ge tr pub i.bus false (i.msgVal tr t r pub)
    (sha384DirectInputAir n fixed).tables 0 t ht
  simp only [Nat.zero_add] at bound
  have recv : busCount (sha384DirectInputAir n fixed).toAir tr pub i.bus false (i.msgVal tr t r pub)≠0 := by
    unfold busCount;omega
  have balance := h.balance i.bus (i.msgVal tr t r pub)
  have noPublic : pubCount (sha384DirectInputAir n fixed) pub i.bus true (i.msgVal tr t r pub)=0 := by
    apply ZkFormal.Chacha.pubCount_zero
    intro seg member hb
    simp only [sha384DirectInputAir,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> simp_all
  rw [noPublic,Nat.add_zero] at balance
  have send : busCount (sha384DirectInputAir n fixed).toAir tr pub i.bus true (i.msgVal tr t r pub)≠0 := by omega
  obtain ⟨t',ht',hc⟩ := ZkFormal.Chacha.busCount_go_pos tr pub i.bus true _ _ 0 send
  simp only [Nat.zero_add] at hc
  obtain ⟨r',hr',i',hi',hb',hs',msg,mult⟩ := ZkFormal.Chacha.exists_of_tableBusCount hc
  exact ⟨t',ht',r',hr',i',hi',hb',hs',msg,mult⟩


/-- Bus4 padded blocks can only originate in the committed input table. -/
theorem sha384_direct_block_sender (n : Nat) (fixed : List (Nat × Nat))
    (t : Nat) (ht : t<(sha384DirectInputAir n fixed).tables.length)
    (i : Interaction) (member : i∈(sha384DirectInputAir n fixed).tables[t]!.interactions)
    (bus : i.bus=4) (send : i.send=true) : t=2 := by
  have cases : t=0 ∨ t=1 ∨ t=2 := by
    simp only [sha384DirectInputAir,List.length_cons,List.length_nil] at ht;omega
  rcases cases with rfl|rfl|rfl
  · simp only [sha384DirectInputAir,List.getElem!_cons_zero,sha384BatchCoreTable,
      List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl <;> simp_all
  · simp only [sha384DirectInputAir,List.getElem!_cons_succ,List.getElem!_cons_zero,
      sha384EndpointTable,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl <;> simp_all
  · rfl

/-- Every active direct padded-block send originates on input row0 and
carries one declared block, followed by its ordered64limb expressions. -/
theorem sha384_direct_sender_location (n : Nat) (fixed : List (Nat × Nat))
    (pub : List Fp) (tr : Trace Fp) (r : Nat) (i : Interaction)
    (member : i∈(sha384DirectInputTable n fixed).interactions)
    (active : i.multNat tr 2 r pub≠0) :
    ∃ block,block<sha384PaddedLength n/128 ∧ r=0 ∧
      i.msgVal tr 2 r pub=Fp.ofNat block ::
        (List.range 16).flatMap (fun word => (List.range 4).map (fun limb =>
          (sha384DirectLimb n block word limb).eval tr 2 0 pub)) := by
  obtain ⟨block,hb,rfl⟩:=List.mem_map.mp member
  have zero : r=0 := by
    by_cases z:r=0
    · exact z
    · simp [Interaction.multNat,Interaction.multNat.go,Expr.eval,Expr.evalWith,rowEnv,z] at active
      exact False.elim ((by decide : (0:Fp)≠1) active)
  subst r
  refine ⟨block,List.mem_range.mp hb,rfl,?_⟩
  simp only [Interaction.msgVal,List.map_cons,List.map_flatMap,List.map_map,Function.comp_def]
  rfl

/-- Actual bus balance binds any active block receive to one existing
committed-input block record. No padding-trace capacity premise is needed. -/
theorem sha384_direct_block_receive (n : Nat) (fixed : List (Nat × Nat))
    (pub : List Fp) (tr : Trace Fp) (h : HoldsP (sha384DirectInputAir n fixed) pub tr)
    (t r : Nat) (ht : t<(sha384DirectInputAir n fixed).tables.length) (hr : r<tr.height t)
    (i : Interaction) (member : i∈(sha384DirectInputAir n fixed).tables[t]!.interactions)
    (bus : i.bus=4) (recv : i.send=false) (active : i.multNat tr t r pub≠0) :
    ∃ block,block<sha384PaddedLength n/128 ∧
      i.msgVal tr t r pub=Fp.ofNat block ::
        (List.range 16).flatMap (fun word => (List.range 4).map (fun limb =>
          (sha384DirectLimb n block word limb).eval tr 2 0 pub)) := by
  obtain ⟨senderTable,hs,row,_,sender,hm,hb,send,msg,mult⟩:=
    sha384_direct_receive_match n fixed pub tr h ht hr member recv (by omega) active
  have table:=sha384_direct_block_sender n fixed senderTable hs sender hm (hb.trans bus) send
  subst senderTable
  obtain ⟨block,hblock,_,payload⟩:=sha384_direct_sender_location n fixed pub tr row sender hm mult
  exact ⟨block,hblock,msg.symm.trans payload⟩

end NearCompression
