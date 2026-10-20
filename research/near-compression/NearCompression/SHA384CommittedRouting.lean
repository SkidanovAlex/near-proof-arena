import NearCompression.SHA384CommittedBytes
import NearCompression.SHA384BatchedRouting

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2

/-- Every non-IV receive is matched by an actual internal send, using exact
natural bus balance. This includes private byte bus6 and padded-block bus4. -/
theorem sha384_committed_receive_match (n : Nat) (fixed : List (Nat × Nat)) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384CommittedInputAir n fixed) pub tr) {t r : Nat}
    (ht : t<(sha384CommittedInputAir n fixed).tables.length) (hr : r<tr.height t)
    {i : Interaction} (hi : i ∈ (sha384CommittedInputAir n fixed).tables[t]!.interactions)
    (hs : i.send=false) (busBound : i.bus≠5) (hm : i.multNat tr t r pub≠0) :
    ∃ t',t'<(sha384CommittedInputAir n fixed).tables.length ∧ ∃ r',r'<tr.height t' ∧
      ∃ i' ∈ (sha384CommittedInputAir n fixed).tables[t']!.interactions,
      i'.bus=i.bus ∧ i'.send=true ∧ i'.msgVal tr t' r' pub=i.msgVal tr t r pub ∧ i'.multNat tr t' r' pub≠0 := by
  have positive := ZkFormal.Chacha.tableBusCount_pos hr hi hm
  rw [hs] at positive
  have bound := ZkFormal.Chacha.busCount_go_ge tr pub i.bus false (i.msgVal tr t r pub)
    (sha384CommittedInputAir n fixed).tables 0 t ht
  simp only [Nat.zero_add] at bound
  have recv : busCount (sha384CommittedInputAir n fixed).toAir tr pub i.bus false (i.msgVal tr t r pub)≠0 := by
    unfold busCount;omega
  have balance := h.balance i.bus (i.msgVal tr t r pub)
  have noPublic : pubCount (sha384CommittedInputAir n fixed) pub i.bus true (i.msgVal tr t r pub)=0 := by
    apply ZkFormal.Chacha.pubCount_zero
    intro seg member hb
    simp only [sha384CommittedInputAir,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> simp_all
  rw [noPublic,Nat.add_zero] at balance
  have send : busCount (sha384CommittedInputAir n fixed).toAir tr pub i.bus true (i.msgVal tr t r pub)≠0 := by omega
  obtain ⟨t',ht',hc⟩ := ZkFormal.Chacha.busCount_go_pos tr pub i.bus true _ _ 0 send
  simp only [Nat.zero_add] at hc
  obtain ⟨r',hr',i',hi',hb',hs',msg,mult⟩ := ZkFormal.Chacha.exists_of_tableBusCount hc
  exact ⟨t',ht',r',hr',i',hi',hb',hs',msg,mult⟩

/-- Every active byte-input send comes from row zero and carries its actual
byte index and decoded field value. -/
theorem sha384_committed_input_send_location (n : Nat) (fixed : List (Nat × Nat))
    (pub : List Fp) (tr : Trace Fp) (r : Nat) (i : Interaction)
    (member : i∈(sha384CommittedInputTable n fixed).interactions)
    (active : i.multNat tr 2 r pub≠0) :
    ∃ index,index<n ∧ r=0 ∧ i.bus=6 ∧ i.send=true ∧
      i.msgVal tr 2 r pub=[Fp.ofNat index,(instructionBitExpr (8*index) 8).eval tr 2 0 pub] := by
  obtain ⟨index,hi,rfl⟩:=List.mem_map.mp member
  have zero : r=0 := by
    by_cases z:r=0
    · exact z
    · simp [Interaction.multNat,Interaction.multNat.go,Expr.eval,Expr.evalWith,rowEnv,z] at active
      exact False.elim ((by decide : (0:Fp)≠1) active)
  subst r
  exact ⟨index,List.mem_range.mp hi,rfl,rfl,rfl,rfl⟩

theorem sha384_committed_byte_sender (n : Nat) (fixed : List (Nat × Nat))
    (t : Nat) (ht : t<(sha384CommittedInputAir n fixed).tables.length)
    (i : Interaction) (member : i∈(sha384CommittedInputAir n fixed).tables[t]!.interactions)
    (bus : i.bus=6) (send : i.send=true) : t=2 := by
  have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 := by
    simp only [sha384CommittedInputAir,List.length_cons,List.length_nil] at ht;omega
  rcases cases with rfl|rfl|rfl|rfl
  · simp only [sha384CommittedInputAir,List.getElem!_cons_zero,sha384BatchCoreTable,
      List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl <;> simp_all
  · simp only [sha384CommittedInputAir,List.getElem!_cons_succ,List.getElem!_cons_zero,
      sha384EndpointTable,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl <;> simp_all
  · rfl
  · simp only [sha384CommittedInputAir,List.getElem!_cons_succ,List.getElem!_cons_zero,
      sha384CommittedPadTable,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with member|rfl
    · obtain ⟨b,_,member⟩:=List.mem_flatMap.mp member
      obtain ⟨j,_,eq⟩:=List.mem_filterMap.mp member
      split at eq
      · cases eq
        contradiction
      · cases eq
    · simp at bus

/-- Actual active padding bytes match the same indexed byte in the committed
input row. The length bound prevents distinct natural indices aliasing in Fp. -/
theorem sha384_committed_pad_input_byte (n : Nat) (fixed : List (Nat × Nat))
    (pub : List Fp) (tr : Trace Fp) (h : HoldsP (sha384CommittedInputAir n fixed) pub tr)
    (bound : n≤P) (b j : Nat) (hr : b<tr.height 3)
    (hb : b<sha384PaddedLength n/128) (hj : j<128) (realByte : 128*b+j<n) :
    (instructionBitExpr (8*j) 8).eval tr 3 b pub=
      (instructionBitExpr (8*(128*b+j)) 8).eval tr 2 0 pub := by
  let i : Interaction:=⟨6,[sha384PadSelect b],[.const (128*b+j),instructionBitExpr (8*j) 8],false⟩
  have member : i∈(sha384CommittedInputAir n fixed).tables[3]!.interactions := by
    apply List.mem_append_left
    apply List.mem_flatMap.mpr
    refine ⟨b,List.mem_range.mpr hb,?_⟩
    apply List.mem_filterMap.mpr
    exact ⟨j,List.mem_range.mpr hj,by rw [ite_eq_left realByte]⟩
  have selected:=sha384_committed_pad_selector n fixed pub tr h b hr b hb
  simp only [ite_true] at selected
  have active : i.multNat tr 3 b pub≠0 := by
    simp [i,Interaction.multNat,Interaction.multNat.go,sha384PadSelect,Expr.eval,Expr.evalWith,rowEnv,selected]
  obtain ⟨t,ht,r,hr',sender,hm,bus,send,msg,mult⟩:=sha384_committed_receive_match n fixed pub tr h
    (by simp [sha384CommittedInputAir]) hr member rfl (by change (6:Nat)≠5;decide) active
  have table:=sha384_committed_byte_sender n fixed t ht sender hm bus send
  subst t
  obtain ⟨index,hi,row,_,_,payload⟩:=sha384_committed_input_send_location n fixed pub tr r sender hm mult
  rw [payload] at msg
  change [Fp.ofNat index,(instructionBitExpr (8*index) 8).eval tr 2 0 pub]=
    [Fp.ofNat (128*b+j),(instructionBitExpr (8*j) 8).eval tr 3 b pub] at msg
  have tags:=congrArg (fun xs:List Fp => (xs.getD 0 0).toNat) msg
  change (Fp.ofNat index).toNat=(Fp.ofNat (128*b+j)).toNat at tags
  simp only [Fp.toNat_ofNat] at tags
  rw [Nat.mod_eq_of_lt (by omega),Nat.mod_eq_of_lt (by omega)] at tags
  have bytes:=congrArg (fun xs:List Fp => xs.getD 1 0) msg
  change (instructionBitExpr (8*index) 8).eval tr 2 0 pub=
    (instructionBitExpr (8*j) 8).eval tr 3 b pub at bytes
  rw [tags] at bytes
  exact bytes.symm

end NearCompression
