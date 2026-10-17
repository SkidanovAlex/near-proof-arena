import NearCompression.SHA384EndpointCoreSemantics
import ZkFormal.Chacha.Bus

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 NearSpecV3.SHA512
set_option maxRecDepth 65536

def sha384CoreLimbs (row : Nat → Fp) (output : Bool) : List Fp :=
  (List.range 8).flatMap (fun i => (List.range 4).map (fun limb =>
    (instructionBitExpr ((if output then sha512FeedForwardResultBase i else sha512FeedForwardInputBase i)+16*limb) 16).evalWith (instructionAddEnv row)))
def sha384EndpointLimbs (row : Nat → Fp) (offset : Nat) : List Fp :=
  (List.range 8).flatMap (fun i => (List.range 4).map (fun limb => row (208*i+offset+limb)))

theorem sha384_core_message_eval (tr : Trace Fp) (pub : List Fp) (t r tag : Nat) (output : Bool) :
    (sha384CoreStateMessage tag output).map (fun e => e.eval tr t r pub)=
      Fp.ofNat tag :: sha384CoreLimbs (tr.cell t r) output := by
  simp only [sha384CoreStateMessage,List.map_cons,List.map_flatMap,List.map_map,Function.comp_def,
    sha512_public_bitexpr_eval,sha384CoreLimbs]
  rfl

theorem sha384_endpoint_message_eval (tr : Trace Fp) (pub : List Fp) (t r offset : Nat) :
    (sha384EndpointLimbMessage offset).map (fun e => e.eval tr t r pub)=
      tr.cell t r 1664 :: sha384EndpointLimbs (tr.cell t r) offset := by
  simp [sha384EndpointLimbMessage,sha384EndpointLimbs,List.map_flatMap,List.map_map,
    Function.comp_def,Expr.eval,Expr.evalWith,rowEnv]

theorem sha384_endpoint_table_index (n : Nat) :
    (sha384EndpointAir n).tables[sha384PaddedLength n/128]!
      =sha384EndpointTable n := by simp [sha384EndpointAir]

theorem sha384_endpoint_receive_match (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384EndpointAir n) pub tr) {t r : Nat}
    (ht : t<(sha384EndpointAir n).tables.length) (hr : r<tr.height t)
    {i : Interaction} (hi : i ∈ (sha384EndpointAir n).tables[t]!.interactions)
    (hs : i.send=false) (hm : i.multNat tr t r pub≠0) :
    ∃ t',t'<(sha384EndpointAir n).tables.length ∧ ∃ r',r'<tr.height t' ∧
      ∃ i' ∈ (sha384EndpointAir n).tables[t']!.interactions,
      i'.bus=i.bus ∧ i'.send=true ∧ i'.msgVal tr t' r' pub=i.msgVal tr t r pub ∧ i'.multNat tr t' r' pub≠0 := by
  have positive := ZkFormal.Chacha.tableBusCount_pos hr hi hm
  rw [hs] at positive
  have bound := ZkFormal.Chacha.busCount_go_ge tr pub i.bus false (i.msgVal tr t r pub)
    (sha384EndpointAir n).tables 0 t ht
  simp only [Nat.zero_add] at bound
  have recv : busCount (sha384EndpointAir n).toAir tr pub i.bus false (i.msgVal tr t r pub)≠0 := by
    unfold busCount;omega
  have balance := h.balance i.bus (i.msgVal tr t r pub)
  have noPublic : pubCount (sha384EndpointAir n) pub i.bus true (i.msgVal tr t r pub)=0 := by
    apply ZkFormal.Chacha.pubCount_zero
    intro seg member hb
    simp only [sha384EndpointAir,List.mem_singleton] at member
    subst seg
    simp
  rw [noPublic,Nat.add_zero] at balance
  have send : busCount (sha384EndpointAir n).toAir tr pub i.bus true (i.msgVal tr t r pub)≠0 := by omega
  obtain ⟨t',ht',hc⟩ := ZkFormal.Chacha.busCount_go_pos tr pub i.bus true _ _ 0 send
  simp only [Nat.zero_add] at hc
  obtain ⟨r',hr',i',hi',hb',hs',msg,mult⟩ := ZkFormal.Chacha.exists_of_tableBusCount hc
  exact ⟨t',ht',r',hr',i',hi',hb',hs',msg,mult⟩

theorem sha384_endpoint_input_sender (n t : Nat) (ht : t<(sha384EndpointAir n).tables.length)
    (output : Bool) (i : Interaction) (hi : i ∈ (sha384EndpointAir n).tables[t]!.interactions)
    (hb : i.bus=if output then 1 else 0) (hs : i.send=true) :
    t<sha384PaddedLength n/128 ∧ i=⟨(if output then 1 else 0),
      [if output then .col 5231 false else .isFirst],sha384CoreStateMessage t output,true⟩ := by
  by_cases core : t<sha384PaddedLength n/128
  · have table : (sha384EndpointAir n).tables[t]! = sha384EndpointCoreTable n t := by
      simpa [List.getElem!_eq_getElem?_getD,ht] using sha384_endpoint_core_table n t core
    rw [table] at hi
    by_cases positive : 0<t
    all_goals simp only [sha384EndpointCoreTable,positive,ite_true,ite_false,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hi
    all_goals rcases hi with (rfl | rfl) | hi
    all_goals first | (cases output <;> simp_all) | (subst i;cases output <;> simp_all)
  · have endIndex : t=sha384PaddedLength n/128 := by simp only [sha384EndpointAir,List.length_append,List.length_map,List.length_range,List.length_singleton] at ht;omega
    subst t
    rw [sha384_endpoint_table_index] at hi
    simp only [sha384EndpointTable,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> cases output <;> simp_all

/-- An active endpoint input is supplied by the uniquely tagged core at its
canonical boundary row. This uses natural bus counts, not field sums. -/
theorem sha384_endpoint_input_match (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384EndpointAir n) pub tr) (r : Nat)
    (hr : r<tr.height (sha384PaddedLength n/128))
    (active : tr.cell (sha384PaddedLength n/128) r 1665=1) (output : Bool) :
    ∃ t,t<sha384PaddedLength n/128 ∧
      tr.cell (sha384PaddedLength n/128) r 1664=Fp.ofNat t ∧
      sha384EndpointLimbs (tr.cell (sha384PaddedLength n/128) r) (if output then 4 else 0)=
        sha384CoreLimbs (tr.cell t (if output then 79 else 0)) output := by
  let i : Interaction := ⟨(if output then 1 else 0),[.col 1665 false],
    sha384EndpointLimbMessage (if output then 4 else 0),false⟩
  have hi : i ∈ (sha384EndpointAir n).tables[sha384PaddedLength n/128]!.interactions := by
    rw [sha384_endpoint_table_index]
    cases output <;> simp [i,sha384EndpointTable]
  have hm : i.multNat tr (sha384PaddedLength n/128) r pub≠0 := by
    simp [i,Interaction.multNat,Interaction.multNat.go,Expr.eval,Expr.evalWith,rowEnv,active]
  obtain ⟨t,ht,s,hs,j,hj,bus,send,msg,mult⟩ := sha384_endpoint_receive_match n pub tr h
    (by simp [sha384EndpointAir]) hr hi rfl hm
  obtain ⟨core,rfl⟩ := sha384_endpoint_input_sender n t ht output j hj bus send
  have sourceRow : s=(if output then 79 else 0) := by
    have phase := (sha384_endpoint_core_height_phase n pub tr h t core).2 s hs
    cases output
    · by_cases zero : s=0
      · exact zero
      · simp [Interaction.multNat,Interaction.multNat.go,Expr.eval,Expr.evalWith,rowEnv,zero] at mult
        exact False.elim ((by decide : (0:Fp)≠1) mult)
    · by_cases finalRow : s=79
      · exact finalRow
      · simp [Interaction.multNat,Interaction.multNat.go,Expr.eval,Expr.evalWith,rowEnv,phase,finalRow] at mult
        exact False.elim ((by decide : (0:Fp)≠1) mult)
  subst s
  change (sha384CoreStateMessage t output).map _ = (sha384EndpointLimbMessage (if output then 4 else 0)).map _ at msg
  rw [sha384_core_message_eval,sha384_endpoint_message_eval] at msg
  exact ⟨t,core,(List.cons.inj msg).1.symm,(List.cons.inj msg).2.symm⟩

theorem sha384_endpoint_inputs_same_core (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384EndpointAir n) pub tr) (bound : sha384PaddedLength n/128<P)
    (r : Nat) (hr : r<tr.height (sha384PaddedLength n/128))
    (active : tr.cell (sha384PaddedLength n/128) r 1665=1) :
    ∃ t,t<sha384PaddedLength n/128 ∧
      tr.cell (sha384PaddedLength n/128) r 1664=Fp.ofNat t ∧
      sha384EndpointLimbs (tr.cell (sha384PaddedLength n/128) r) 0=sha384CoreLimbs (tr.cell t 0) false ∧
      sha384EndpointLimbs (tr.cell (sha384PaddedLength n/128) r) 4=sha384CoreLimbs (tr.cell t 79) true := by
  obtain ⟨a,ha,tagA,limbA⟩ := sha384_endpoint_input_match n pub tr h r hr active false
  obtain ⟨b,hb,tagB,limbB⟩ := sha384_endpoint_input_match n pub tr h r hr active true
  have same := congrArg Fp.toNat (tagA.symm.trans tagB)
  rw [Fp.toNat_ofNat,Fp.toNat_ofNat,Nat.mod_eq_of_lt (by omega : a<P),Nat.mod_eq_of_lt (by omega : b<P)] at same
  subst b
  exact ⟨a,ha,tagA,limbA,limbB⟩

theorem sha384_endpoint_limb_ext (a b : Nat → Nat → Fp)
    (eq : (List.range 8).flatMap (fun i => (List.range 4).map (a i))=
      (List.range 8).flatMap (fun i => (List.range 4).map (b i)))
    (i j : Nat) (hi : i<8) (hj : j<4) : a i j=b i j := by
  have ic : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 := by omega
  have jc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
  simp only [show List.range 8=[0,1,2,3,4,5,6,7] from rfl,show List.range 4=[0,1,2,3] from rfl,List.append_nil,List.nil_append,List.flatMap_cons,
    List.flatMap_nil,List.map_cons,List.map_nil,List.cons_append,List.cons.injEq] at eq
  rcases ic with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases jc with rfl | rfl | rfl | rfl <;> grind


theorem sha384_endpoint_word_decode (row core : Nat → Fp) (offset : Nat) (output : Bool)
    (rounds : sha512RoundHolds (sha512CombinedRoundRow core))
    (eq : sha384EndpointLimbs row offset=sha384CoreLimbs core output)
    (i : Nat) (hi : i<8) :
    instructionAdd64Word (fun col => row (208*i+col)) offset =
      sha512BitsWord core (if output then sha512FeedForwardResultBase i else sha512FeedForwardInputBase i) := by
  let limbs := (List.range 4).map (fun j => row (208*i+offset+j))
  have eqL (j : Nat) (hj : j<4) : limbs.getD (0+j) 0 =
      (instructionBitExpr ((if output then sha512FeedForwardResultBase i else sha512FeedForwardInputBase i)+16*j) 16).evalWith (instructionAddEnv core) := by
    have limb := sha384_endpoint_limb_ext _ _ eq i j hi hj
    simpa [limbs,List.getD_eq_getElem?_getD,hj] using limb
  have decoded := (sha512_public_word_decode core limbs 0 _
    (fun bit hb => sha384_endpoint_state_bits core rounds output i bit hi hb) eqL).1
  simpa [sha512PublicWord,limbs,instructionAdd64Word,Nat.add_assoc] using decoded

def sha384EndpointOutput (row : Nat → Fp) : List Nat :=
  (List.range 8).map (fun i => instructionAdd64Word (fun col => row (208*i+col)) 8)

/-- Every active endpoint computes exactly the compression of its tagged core. -/
theorem sha384_endpoint_output_compression (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384EndpointAir n) pub tr) (bound : sha384PaddedLength n/128<P)
    (r : Nat) (hr : r<tr.height (sha384PaddedLength n/128))
    (active : tr.cell (sha384PaddedLength n/128) r 1665=1) :
    ∃ t,t<sha384PaddedLength n/128 ∧
      tr.cell (sha384PaddedLength n/128) r 1664=Fp.ofNat t ∧
      sha384EndpointOutput (tr.cell (sha384PaddedLength n/128) r)=sha384CoreCompression tr t := by
  obtain ⟨t,ht,tag,left,right⟩ := sha384_endpoint_inputs_same_core n pub tr h bound r hr active
  refine ⟨t,ht,tag,?_⟩
  rw [sha384_split_compression n pub tr h t ht]
  apply List.map_congr_left
  intro i hi
  have ib := List.mem_range.mp hi
  have first := sha384_endpoint_core_round_holds n pub tr h t ht 0 (Nat.two_pow_pos _)
  have last := sha384_endpoint_core_round_holds n pub tr h t ht 79 (by rw [(sha384_endpoint_core_height_phase n pub tr h t ht).1];decide)
  have a := sha384_endpoint_word_decode _ _ 0 false first left i ib
  have b := sha384_endpoint_word_decode _ _ 4 true last right i ib
  simp only [Bool.false_eq_true,ite_false,ite_true] at a b
  rw [sha512_ff_input_words _ first i ib] at a
  rw [sha512_ff_output_words _ last i ib] at b
  have add := sha384_endpoint_add_sound (sha384EndpointAir n) tr pub (sha384PaddedLength n/128)
    (by simp [sha384EndpointAir]) n (by simp [sha384EndpointAir]) h r i hr ib
  rw [a,b] at add
  exact add.symm


theorem sha384_endpoint_output_sender (n t : Nat) (ht : t<(sha384EndpointAir n).tables.length)
    (final : Bool) (i : Interaction) (hi : i ∈ (sha384EndpointAir n).tables[t]!.interactions)
    (hb : i.bus=if final then 3 else 2) (hs : i.send=true) :
    t=sha384PaddedLength n/128 ∧ i=(sha384EndpointTable n).interactions[if final then 3 else 2]! := by
  by_cases core : t<sha384PaddedLength n/128
  · have table : (sha384EndpointAir n).tables[t]! = sha384EndpointCoreTable n t := by
      simpa [List.getElem!_eq_getElem?_getD,ht] using sha384_endpoint_core_table n t core
    rw [table] at hi
    by_cases positive : 0<t
    all_goals simp only [sha384EndpointCoreTable,positive,ite_true,ite_false,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hi
    all_goals rcases hi with (rfl | rfl) | hi
    all_goals first | (cases final <;> simp_all) | (subst i;cases final <;> simp_all)
  · have endIndex : t=sha384PaddedLength n/128 := by simp only [sha384EndpointAir,List.length_append,List.length_map,List.length_range,List.length_singleton] at ht;omega
    subst t
    rw [sha384_endpoint_table_index] at hi
    simp only [sha384EndpointTable,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> cases final <;> simp_all [sha384EndpointTable]

theorem sha384_endpoint_send_active (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384EndpointAir n) pub tr) (r : Nat)
    (hr : r<tr.height (sha384PaddedLength n/128)) (final : Bool)
    (hm : ((sha384EndpointTable n).interactions[if final then 3 else 2]!).multNat tr
      (sha384PaddedLength n/128) r pub≠0) :
    tr.cell (sha384PaddedLength n/128) r 1665=1 := by
  have hc := h.constr (sha384PaddedLength n/128) (by simp [sha384EndpointAir]) r hr
    (.mul (.col 1665 false) (.add (.col 1665 false) (.neg (.const 1))))
    (by simp [sha384EndpointAir,sha384EndpointTable,instructionBitConstraint])
  change tr.cell (sha384PaddedLength n/128) r 1665 * (tr.cell (sha384PaddedLength n/128) r 1665 + -(1:Fp))=0 at hc
  cases final <;> simp only [sha384EndpointTable,ite_false,ite_true,Bool.false_eq_true,List.getElem!_cons_zero,List.getElem!_cons_succ,
    Interaction.multNat,Interaction.multNat.go,Expr.eval,Expr.evalWith,rowEnv] at hm
  all_goals split at hm
  all_goals first | (rename_i eq;grind) | (simp_all)


/-- The next core receives the previous tagged compression result, with no
standalone routing premise. -/
theorem sha384_endpoint_compression_link (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384EndpointAir n) pub tr) (bound : sha384PaddedLength n/128<P)
    (t : Nat) (ht : t+1<sha384PaddedLength n/128) :
    sha384CoreCompression tr t=sha512DecodedState (tr.cell (t+1) 0) := by
  let i : Interaction := ⟨2,[.isFirst],sha384CoreStateMessage t false,false⟩
  have table : (sha384EndpointAir n).tables[t+1]! = sha384EndpointCoreTable n (t+1) := by
    simpa [List.getElem!_eq_getElem?_getD,show t+1<(sha384EndpointAir n).tables.length by simp [sha384EndpointAir];omega] using sha384_endpoint_core_table n (t+1) ht
  have hi : i ∈ (sha384EndpointAir n).tables[t+1]!.interactions := by
    rw [table];simp [i,sha384EndpointCoreTable]
  have hm : i.multNat tr (t+1) 0 pub≠0 := by
    simp [i,Interaction.multNat,Interaction.multNat.go,Expr.eval,Expr.evalWith,rowEnv]
  obtain ⟨s,hs,r,hr,j,hj,bus,send,msg,mult⟩ := sha384_endpoint_receive_match n pub tr h
    (by simp [sha384EndpointAir];omega) (Nat.two_pow_pos _) hi rfl hm
  obtain ⟨rfl,rfl⟩ := sha384_endpoint_output_sender n s hs false j hj bus send
  have active := sha384_endpoint_send_active n pub tr h r hr false mult
  obtain ⟨core,hcore,tag,out⟩ := sha384_endpoint_output_compression n pub tr h bound r hr active
  change (sha384EndpointLimbMessage 8).map _ = (sha384CoreStateMessage t false).map _ at msg
  rw [sha384_core_message_eval,sha384_endpoint_message_eval] at msg
  have tagEq := congrArg Fp.toNat (tag.symm.trans (List.cons.inj msg).1)
  rw [Fp.toNat_ofNat,Fp.toNat_ofNat,Nat.mod_eq_of_lt (by omega : core<P),Nat.mod_eq_of_lt (by omega : t<P)] at tagEq
  subst core
  rw [←out]
  apply List.map_congr_left
  intro k hk
  have kb := List.mem_range.mp hk
  have first := sha384_endpoint_core_round_holds n pub tr h (t+1) ht 0 (Nat.two_pow_pos _)
  have decoded := sha384_endpoint_word_decode _ _ 8 false first (List.cons.inj msg).2 k kb
  simpa only [Bool.false_eq_true,ite_false,sha512_ff_input_words _ first k kb] using decoded


end NearCompression
