import NearCompression.SHA384BatchedCompression
import NearCompression.SHA384BatchedPadding
import NearCompression.SHA384EndpointRouting

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 NearSpecV3.SHA512
set_option maxRecDepth 65536

theorem sha384_batch_receive_match (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384BatchedAir n) pub tr) {t r : Nat}
    (ht : t<(sha384BatchedAir n).tables.length) (hr : r<tr.height t)
    {i : Interaction} (hi : i ∈ (sha384BatchedAir n).tables[t]!.interactions)
    (hs : i.send=false) (busBound : i.bus<4) (hm : i.multNat tr t r pub≠0) :
    ∃ t',t'<(sha384BatchedAir n).tables.length ∧ ∃ r',r'<tr.height t' ∧
      ∃ i' ∈ (sha384BatchedAir n).tables[t']!.interactions,
      i'.bus=i.bus ∧ i'.send=true ∧ i'.msgVal tr t' r' pub=i.msgVal tr t r pub ∧ i'.multNat tr t' r' pub≠0 := by
  have positive := ZkFormal.Chacha.tableBusCount_pos hr hi hm
  rw [hs] at positive
  have bound := ZkFormal.Chacha.busCount_go_ge tr pub i.bus false (i.msgVal tr t r pub)
    (sha384BatchedAir n).tables 0 t ht
  simp only [Nat.zero_add] at bound
  have recv : busCount (sha384BatchedAir n).toAir tr pub i.bus false (i.msgVal tr t r pub)≠0 := by
    unfold busCount;omega
  have balance := h.balance i.bus (i.msgVal tr t r pub)
  have noPublic : pubCount (sha384BatchedAir n) pub i.bus true (i.msgVal tr t r pub)=0 := by
    apply ZkFormal.Chacha.pubCount_zero
    intro seg member hb
    simp only [sha384BatchedAir,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl <;> simp_all <;> omega
  rw [noPublic,Nat.add_zero] at balance
  have send : busCount (sha384BatchedAir n).toAir tr pub i.bus true (i.msgVal tr t r pub)≠0 := by omega
  obtain ⟨t',ht',hc⟩ := ZkFormal.Chacha.busCount_go_pos tr pub i.bus true _ _ 0 send
  simp only [Nat.zero_add] at hc
  obtain ⟨r',hr',i',hi',hb',hs',msg,mult⟩ := ZkFormal.Chacha.exists_of_tableBusCount hc
  exact ⟨t',ht',r',hr',i',hi',hb',hs',msg,mult⟩


theorem sha384_batch_state_message_eval (tr : Trace Fp) (pub : List Fp) (r : Nat) (output previous : Bool) :
    (sha384BatchState output previous).map (fun e => e.eval tr 0 r pub)=
      (if previous then tr.cell 0 r 5233 + -(1:Fp) else tr.cell 0 r 5233) ::
        sha384CoreLimbs (tr.cell 0 r) output := by
  simp only [sha384BatchState,sha384CoreStateMessage,List.tail_cons,List.map_cons,List.map_flatMap,
    List.map_map,Function.comp_def,sha512_public_bitexpr_eval,sha384CoreLimbs]
  cases previous <;> rfl


theorem sha384_batch_input_sender (n t : Nat) (ht : t<(sha384BatchedAir n).tables.length)
    (output : Bool) (i : Interaction) (hi : i∈(sha384BatchedAir n).tables[t]!.interactions)
    (hb : i.bus=if output then 1 else 0) (hs : i.send=true) :
    t=0 ∧ i=⟨(if output then 1 else 0),[sha384BatchPhase (if output then 79 else 0)],sha384BatchState output,true⟩ := by
  have cases : t=0 ∨ t=1 := by simp only [sha384BatchedAir,List.length_cons,List.length_nil] at ht;omega
  rcases cases with rfl | rfl
  · simp only [sha384BatchedAir,List.getElem!_cons_zero,sha384BatchCoreTable,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl <;> cases output <;> simp_all
  · simp only [sha384BatchedAir,List.getElem!_cons_succ,List.getElem!_cons_zero,sha384EndpointTable,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> cases output <;> simp_all

/-- A nonzero phase multiplicity identifies one exact active segment boundary. -/
theorem sha384_batch_phase_location (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384BatchedAir n) pub tr) (bound : sha384PaddedLength n/128<P)
    (r phase : Nat) (hr : r<tr.height 0) (hp : phase<80)
    (one : tr.cell 0 r (5152+phase)=1) :
    ∃ block,block<sha384PaddedLength n/128 ∧ r=80*block+phase ∧ tr.cell 0 r 5233=Fp.ofNat block := by
  have active : tr.cell 0 r 5232=1 := by
    rcases sha384_batch_active_boolean n pub tr h r hr with zero | active
    · have inactive := sha384_batch_inactive_phase n pub tr h r hr zero phase hp
      rw [one] at inactive
      exact False.elim ((by decide : (1:Fp)≠0) inactive)
    · exact active
  have range := sha384_batch_active_bounded n pub tr h bound r hr active
  have phaseEq := sha384_batch_active_phase n pub tr h r hr active phase hp
  rw [one] at phaseEq
  have same : phase=r%80 := by
    by_cases eq : phase=r%80
    · exact eq
    · rw [ite_eq_right eq] at phaseEq
      exact False.elim ((by decide : (1:Fp)≠0) phaseEq)
  exact ⟨r/80,by omega,by omega,sha384_batch_active_tag n pub tr h r hr active⟩

theorem sha384_batch_endpoint_input (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384BatchedAir n) pub tr) (bound : sha384PaddedLength n/128<P)
    (r : Nat) (hr : r<tr.height 1) (active : tr.cell 1 r 1665=1) (output : Bool) :
    ∃ block,block<sha384PaddedLength n/128 ∧ tr.cell 1 r 1664=Fp.ofNat block ∧
      sha384EndpointLimbs (tr.cell 1 r) (if output then 4 else 0)=
        sha384CoreLimbs (tr.cell 0 (80*block+(if output then 79 else 0))) output := by
  let i : Interaction := ⟨(if output then 1 else 0),[.col 1665 false],
    sha384EndpointLimbMessage (if output then 4 else 0),false⟩
  have hi : i∈(sha384BatchedAir n).tables[1]!.interactions := by
    cases output <;> simp [i,sha384BatchedAir,sha384EndpointTable]
  have hm : i.multNat tr 1 r pub≠0 := by
    simp [i,Interaction.multNat,Interaction.multNat.go,Expr.eval,Expr.evalWith,rowEnv,active]
  obtain ⟨t,ht,s,hs,j,hj,bus,send,msg,mult⟩ := sha384_batch_receive_match n pub tr h
    (by simp [sha384BatchedAir]) hr hi rfl (by cases output <;> simp [i]) hm
  obtain ⟨rfl,rfl⟩ := sha384_batch_input_sender n t ht output j hj bus send
  have phase : tr.cell 0 s (5152+(if output then 79 else 0))=1 := by
    by_cases eq : tr.cell 0 s (5152+(if output then 79 else 0))=1
    · exact eq
    · simp [Interaction.multNat,Interaction.multNat.go,sha384BatchPhase,Expr.eval,Expr.evalWith,rowEnv,eq] at mult
  obtain ⟨block,hb,row,tag⟩ := sha384_batch_phase_location n pub tr h bound s _ hs
    (by cases output <;> decide) phase
  change (sha384BatchState output).map _ = (sha384EndpointLimbMessage (if output then 4 else 0)).map _ at msg
  rw [sha384_batch_state_message_eval,sha384_endpoint_message_eval] at msg
  simp only [Bool.false_eq_true,ite_false] at msg
  rw [tag,row] at msg
  exact ⟨block,hb,(List.cons.inj msg).1.symm,(List.cons.inj msg).2.symm⟩

theorem sha384_batch_endpoint_inputs (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384BatchedAir n) pub tr) (bound : sha384PaddedLength n/128<P)
    (r : Nat) (hr : r<tr.height 1) (active : tr.cell 1 r 1665=1) :
    ∃ block,block<sha384PaddedLength n/128 ∧ tr.cell 1 r 1664=Fp.ofNat block ∧
      sha384EndpointLimbs (tr.cell 1 r) 0=sha384CoreLimbs (tr.cell 0 (80*block)) false ∧
      sha384EndpointLimbs (tr.cell 1 r) 4=sha384CoreLimbs (tr.cell 0 (80*block+79)) true := by
  obtain ⟨a,ha,tagA,limbA⟩ := sha384_batch_endpoint_input n pub tr h bound r hr active false
  obtain ⟨b,hb,tagB,limbB⟩ := sha384_batch_endpoint_input n pub tr h bound r hr active true
  have same := congrArg Fp.toNat (tagA.symm.trans tagB)
  rw [Fp.toNat_ofNat,Fp.toNat_ofNat,Nat.mod_eq_of_lt (by omega : a<P),Nat.mod_eq_of_lt (by omega : b<P)] at same
  subst b
  exact ⟨a,ha,tagA,by simpa using limbA,limbB⟩

theorem sha384_batch_endpoint_compression (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384BatchedAir n) pub tr) (bound : sha384PaddedLength n/128<P)
    (r : Nat) (hr : r<tr.height 1) (active : tr.cell 1 r 1665=1) :
    ∃ block,block<sha384PaddedLength n/128 ∧ tr.cell 1 r 1664=Fp.ofNat block ∧
      sha384EndpointOutput (tr.cell 1 r)=sha384BatchCompression tr block := by
  obtain ⟨block,hb,tag,left,right⟩ := sha384_batch_endpoint_inputs n pub tr h bound r hr active
  refine ⟨block,hb,tag,?_⟩
  rw [sha384_batch_compression n pub tr h bound block hb]
  apply List.map_congr_left
  intro i hi
  have ib := List.mem_range.mp hi
  have first := sha384_batch_round_holds n pub tr h bound block 0 hb (by decide)
  have last := sha384_batch_round_holds n pub tr h bound block 79 hb (by decide)
  simp only [Nat.add_zero] at first
  have a := sha384_endpoint_word_decode _ _ 0 false first left i ib
  have b := sha384_endpoint_word_decode _ _ 4 true last right i ib
  simp only [Bool.false_eq_true,ite_false,ite_true] at a b
  rw [sha512_ff_input_words _ first i ib] at a
  rw [sha512_ff_output_words _ last i ib] at b
  have add := sha384_endpoint_add_sound (sha384BatchedAir n) tr pub 1
    (by simp [sha384BatchedAir]) n rfl h r i hr ib
  rw [a,b] at add
  exact add.symm


theorem sha384_batch_output_sender (n t : Nat) (ht : t<(sha384BatchedAir n).tables.length)
    (final : Bool) (i : Interaction) (hi : i∈(sha384BatchedAir n).tables[t]!.interactions)
    (hb : i.bus=if final then 3 else 2) (hs : i.send=true) :
    t=1 ∧ i=(sha384EndpointTable n).interactions[if final then 3 else 2]! := by
  have cases : t=0 ∨ t=1 := by simp only [sha384BatchedAir,List.length_cons,List.length_nil] at ht;omega
  rcases cases with rfl | rfl
  · simp only [sha384BatchedAir,List.getElem!_cons_zero,sha384BatchCoreTable,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl <;> cases final <;> simp_all
  · simp only [sha384BatchedAir,List.getElem!_cons_succ,List.getElem!_cons_zero,sha384EndpointTable,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> cases final <;> simp_all [sha384EndpointTable]

theorem sha384_batch_endpoint_send_active (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384BatchedAir n) pub tr) (r : Nat)
    (hr : r<tr.height 1) (final : Bool)
    (hm : ((sha384EndpointTable n).interactions[if final then 3 else 2]!).multNat tr
      1 r pub≠0) :
    tr.cell 1 r 1665=1 := by
  have hc := h.constr 1 (by simp [sha384BatchedAir]) r hr
    (.mul (.col 1665 false) (.add (.col 1665 false) (.neg (.const 1))))
    (by simp [sha384BatchedAir,sha384EndpointTable,instructionBitConstraint])
  change tr.cell 1 r 1665 * (tr.cell 1 r 1665 + -(1:Fp))=0 at hc
  cases final <;> simp only [sha384EndpointTable,ite_false,ite_true,Bool.false_eq_true,List.getElem!_cons_zero,List.getElem!_cons_succ,
    Interaction.multNat,Interaction.multNat.go,Expr.eval,Expr.evalWith,rowEnv] at hm
  all_goals split at hm
  all_goals first | (rename_i eq;grind) | (simp_all)



theorem sha384_batch_compression_link (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384BatchedAir n) pub tr) (bound : sha384PaddedLength n/128<P)
    (block : Nat) (hb : block+1<sha384PaddedLength n/128) :
    sha384BatchCompression tr block=sha512DecodedState (tr.cell 0 (80*(block+1))) := by
  let i : Interaction := ⟨2,[.mul (sha384BatchPhase 0) (.add (.const 1) (.neg .isFirst))],sha384BatchState false true,false⟩
  have hi : i∈(sha384BatchedAir n).tables[0]!.interactions := by simp [i,sha384BatchedAir,sha384BatchCoreTable]
  have metadata := sha384_batch_segment_metadata n pub tr h bound (block+1) 0 hb (by decide)
  simp only [Nat.add_zero] at metadata
  have phase := metadata.2.2.2 0 (by decide)
  simp only [ite_true] at phase
  have nz : 80*(block+1)≠0 := by omega
  have hm : i.multNat tr 0 (80*(block+1)) pub≠0 := by
    simp only [i,Interaction.multNat,Interaction.multNat.go,sha384BatchPhase,Expr.eval,Expr.evalWith,rowEnv,
      Bool.false_eq_true,ite_false,Nat.add_zero,phase,ite_eq_right nz]
    simp
    change (1:Fp)*(1+ -0)=1
    grind
  obtain ⟨t,ht,r,hr,j,hj,bus,send,msg,mult⟩ := sha384_batch_receive_match n pub tr h
    (by simp [sha384BatchedAir]) metadata.1 hi rfl (by decide) hm
  obtain ⟨rfl,rfl⟩ := sha384_batch_output_sender n t ht false j hj bus send
  have active := sha384_batch_endpoint_send_active n pub tr h r hr false mult
  obtain ⟨core,hcore,tag,out⟩ := sha384_batch_endpoint_compression n pub tr h bound r hr active
  change (sha384EndpointLimbMessage 8).map _ = (sha384BatchState false true).map _ at msg
  rw [sha384_endpoint_message_eval,sha384_batch_state_message_eval] at msg
  simp only [ite_true] at msg
  rw [metadata.2.2.1] at msg
  have cast : Fp.ofNat (block+1)=Fp.ofNat block+1 := Lean.Grind.Semiring.natCast_add _ _
  have previous : Fp.ofNat (block+1)+ -(1:Fp)=Fp.ofNat block := by rw [cast];grind
  rw [previous] at msg
  have tagEq := congrArg Fp.toNat (tag.symm.trans (List.cons.inj msg).1)
  rw [Fp.toNat_ofNat,Fp.toNat_ofNat,Nat.mod_eq_of_lt (by omega : core<P),Nat.mod_eq_of_lt (by omega : block<P)] at tagEq
  subst core
  rw [←out]
  apply List.map_congr_left
  intro k hk
  have kb := List.mem_range.mp hk
  have first := sha384_batch_round_holds n pub tr h bound (block+1) 0 hb (by decide)
  simp only [Nat.add_zero] at first
  have decoded := sha384_endpoint_word_decode _ _ 8 false first (List.cons.inj msg).2 k kb
  simpa only [Bool.false_eq_true,ite_false,sha512_ff_input_words _ first k kb] using decoded

end NearCompression

