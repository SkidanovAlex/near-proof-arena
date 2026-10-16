import NearCompression.SHA384SharedRouting
import NearCompression.SHA384SharedPrefix
import NearCompression.SHA384SharedCompression
import NearCompression.SHA384BatchedRouting

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 NearSpecV3.SHA512
set_option maxRecDepth 65536

def sharedNodeSenderTable (bus : Nat) : Nat := if bus=1 then 0 else if bus=3 then 1 else 2
def sharedNodeSender (bus : Nat) : Interaction :=
  if bus=0 then ⟨0,[.const 0,.col 1 false],.col 0 false :: sharedCols 4 32,true⟩
  else if bus=1 then ⟨1,[sha384BatchPhase 79],sha384BatchState true,true⟩
  else if bus=2 then ⟨2,[.col 1 false],.col 0 false :: sharedCols 36 64,true⟩
  else ⟨3,[.col 1665 false],sha384EndpointLimbMessage 8 ++ sha384EndpointDigestMessage,true⟩

theorem sha384_shared_node_sender (f0 f1 : List (Nat × Nat)) (t bus : Nat)
    (ht : t<(sha384SharedAir f0 f1).tables.length) (hb : bus<4) (i : Interaction)
    (hi : i∈(sha384SharedAir f0 f1).tables[t]!.interactions)
    (busEq : i.bus=bus) (send : i.send=true) :
    t=sharedNodeSenderTable bus ∧ i=sharedNodeSender bus := by
  have buses : bus=0 ∨ bus=1 ∨ bus=2 ∨ bus=3 := by omega
  have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 := by
    simp only [sha384SharedAir,List.length_cons,List.length_nil] at ht;omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [sha384SharedAir,List.getElem!_cons_zero,List.getElem!_cons_succ,
    sha384SharedCore,sha384SharedEndpoint,sha384SharedRecords,sha384SharedCalls,sha384SharedInput,
    List.mem_cons,List.not_mem_nil,or_false] at hi
  · rcases hi with rfl | rfl | rfl <;> rcases buses with rfl | rfl | rfl | rfl <;>
      simp_all [sharedNodeSenderTable,sharedNodeSender]
  · rcases hi with rfl | rfl | rfl <;> rcases buses with rfl | rfl | rfl | rfl <;>
      simp_all [sharedNodeSenderTable,sharedNodeSender]
  · rcases hi with rfl | rfl | rfl | rfl <;> rcases buses with rfl | rfl | rfl | rfl <;>
      simp_all [sharedNodeSenderTable,sharedNodeSender]
  · rcases hi with rfl | rfl <;> rcases buses with rfl | rfl | rfl | rfl <;> simp_all
  · obtain ⟨b,hb',rfl⟩ := List.mem_map.mp hi
    simp at busEq
    omega
  · obtain ⟨b,hb',rfl⟩ := List.mem_map.mp hi
    simp at busEq
    omega

theorem sha384_shared_record_input_active (tr : Trace Fp) (pub : List Fp) (r bus : Nat)
    (hb : bus=0 ∨ bus=2) (hm : (sharedNodeSender bus).multNat tr 2 r pub≠0) :
    tr.cell 2 r 1=1 := by
  by_cases on : tr.cell 2 r 1=1
  · exact on
  · rcases hb with rfl | rfl <;>
      simp [sharedNodeSender,Interaction.multNat,Interaction.multNat.go,Expr.eval,Expr.evalWith,rowEnv,on] at hm
    exact False.elim ((by decide : (0:Fp)≠1) hm)

/-- Any bus0 receiver gets the A32 state from one actual active record. -/
theorem sha384_shared_receive_A (f0 f1 : List (Nat × Nat)) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384SharedAir f0 f1) pub tr) {t r : Nat}
    (ht : t<(sha384SharedAir f0 f1).tables.length) (hr : r<tr.height t)
    {i : Interaction} (hi : i∈(sha384SharedAir f0 f1).tables[t]!.interactions)
    (hb : i.bus=0) (hs : i.send=false) (hm : i.multNat tr t r pub≠0) :
    ∃ s,s<tr.height 2 ∧ tr.cell 2 s 1=1 ∧
      tr.cell 2 s 0 :: (List.range 32).map (fun j => tr.cell 2 s (4+j))=i.msgVal tr t r pub := by
  obtain ⟨u,hu,s,hs',j,hj,bus,send,msg,mult⟩ := sha384_shared_receive_match f0 f1 pub tr h ht hr hi hs hm
  rw [hb] at bus
  obtain ⟨table,interaction⟩ := sha384_shared_node_sender f0 f1 u 0 hu (by decide) j hj bus send
  change u=2 at table
  subst u
  subst j
  have on := sha384_shared_record_input_active tr pub s 0 (Or.inl rfl) mult
  refine ⟨s,hs',on,?_⟩
  simpa [sharedNodeSender,Interaction.msgVal,sharedCols,Function.comp_def,Expr.eval,Expr.evalWith,rowEnv] using msg

/-- Every active core phase is attached to exactly one canonical node index. -/
theorem sha384_shared_phase_location (f0 f1 : List (Nat × Nat)) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384SharedAir f0 f1) pub tr) (r phase : Nat)
    (hr : r<tr.height 0) (hp : phase<80) (one : tr.cell 0 r (5152+phase)=1) :
    ∃ node,node<5 ∧ r=80*node+phase ∧ tr.cell 0 r 5233=Fp.ofNat node := by
  have lc := sha384_shared_core_local f0 f1 pub tr h
  have on : tr.cell 0 r 5232=1 := by
    rcases sha384_local_active_boolean 5 pub tr lc r hr with zero | on
    · have inactive := sha384_local_inactive_phase 5 pub tr lc r hr zero phase hp
      rw [one] at inactive
      exact False.elim ((by decide : (1:Fp)≠0) inactive)
    · exact on
  have range := sha384_local_active_bounded 5 pub tr lc (by decide) r hr on
  have ph := sha384_local_active_phase 5 pub tr lc r hr on phase hp
  rw [one] at ph
  have same : phase=r%80 := by
    by_cases eq : phase=r%80
    · exact eq
    · rw [ite_eq_right eq] at ph
      exact False.elim ((by decide : (1:Fp)≠0) ph)
  exact ⟨r/80,by omega,by omega,sha384_local_active_tag 5 pub tr lc r hr on⟩

theorem sha384_shared_record_tag_identifies (f0 f1 : List (Nat × Nat)) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384SharedAir f0 f1) pub tr) (r node : Nat) (hr : r<tr.height 2)
    (on : tr.cell 2 r 1=1) (hn : node<5) (tag : tr.cell 2 r 0=Fp.ofNat node) : r=node := by
  have pf := sha384_shared_record_prefix f0 f1 pub tr h
  rw [shared_prefix_tag pf r hr on] at tag
  have bound := shared_prefix_bounded pf r hr on
  have eq := congrArg Fp.toNat tag
  simpa only [Fp.toNat_ofNat,Nat.mod_eq_of_lt (by unfold P;omega : r<P),
    Nat.mod_eq_of_lt (by unfold P;omega : node<P)] using eq

theorem sha384_shared_core_A (f0 f1 : List (Nat × Nat)) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384SharedAir f0 f1) pub tr) (node : Nat) (hn : node<5) :
    sha384CoreLimbs (tr.cell 0 (80*node)) false=(List.range 32).map (fun j => tr.cell 2 node (4+j)) := by
  have metadata := sha384_local_segment_metadata 5 pub tr (sha384_shared_core_local f0 f1 pub tr h)
    (by decide) node 0 hn (by decide)
  simp only [Nat.add_zero] at metadata
  let i : Interaction := ⟨0,[sha384BatchPhase 0],sha384BatchState false,false⟩
  have hi : i∈(sha384SharedAir f0 f1).tables[0]!.interactions := by simp [i,sha384SharedAir,sha384SharedCore]
  have phase := metadata.2.2.2 0 (by decide)
  simp only [ite_true] at phase
  have hm : i.multNat tr 0 (80*node) pub≠0 := by
    simp [i,Interaction.multNat,Interaction.multNat.go,sha384BatchPhase,Expr.eval,Expr.evalWith,rowEnv,phase]
  obtain ⟨r,hr,on,msg⟩ := sha384_shared_receive_A f0 f1 pub tr h (by simp [sha384SharedAir]) metadata.1 hi rfl rfl hm
  change _=(sha384BatchState false).map _ at msg
  rw [sha384_batch_state_message_eval] at msg
  simp only [Bool.false_eq_true,ite_false,metadata.2.2.1,List.cons.injEq] at msg
  have same := sha384_shared_record_tag_identifies f0 f1 pub tr h r node hr on hn msg.1
  subst r
  exact msg.2.symm

theorem sha384_shared_endpoint_A (f0 f1 : List (Nat × Nat)) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384SharedAir f0 f1) pub tr) (node : Nat) (hn : node<5) :
    sha384EndpointLimbs (tr.cell 1 node) 0=sha384CoreLimbs (tr.cell 0 (80*node)) false := by
  have pf := sha384_shared_endpoint_prefix f0 f1 pub tr h
  have cap := shared_prefix_capacity pf
  have hr : node<tr.height 1 := by omega
  have on := shared_prefix_required pf node hr hn
  have tag := shared_prefix_tag pf node hr on
  let i : Interaction := ⟨0,[.col 1665 false],sha384EndpointLimbMessage 0,false⟩
  have hi : i∈(sha384SharedAir f0 f1).tables[1]!.interactions := by simp [i,sha384SharedAir,sha384SharedEndpoint]
  have hm : i.multNat tr 1 node pub≠0 := by
    simp [i,Interaction.multNat,Interaction.multNat.go,Expr.eval,Expr.evalWith,rowEnv,on]
  obtain ⟨r,hr',active,msg⟩ := sha384_shared_receive_A f0 f1 pub tr h (by simp [sha384SharedAir]) hr hi rfl rfl hm
  change _=(sha384EndpointLimbMessage 0).map _ at msg
  rw [sha384_endpoint_message_eval,tag] at msg
  have same := sha384_shared_record_tag_identifies f0 f1 pub tr h r node hr' active hn (List.cons.inj msg).1
  subst r
  rw [sha384_shared_core_A f0 f1 pub tr h node hn]
  exact (List.cons.inj msg).2.symm

theorem sha384_shared_endpoint_B (f0 f1 : List (Nat × Nat)) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384SharedAir f0 f1) pub tr) (node : Nat) (hn : node<5) :
    sha384EndpointLimbs (tr.cell 1 node) 4=sha384CoreLimbs (tr.cell 0 (80*node+79)) true := by
  have pf := sha384_shared_endpoint_prefix f0 f1 pub tr h
  have cap := shared_prefix_capacity pf
  have hr : node<tr.height 1 := by omega
  have on := shared_prefix_required pf node hr hn
  have tag := shared_prefix_tag pf node hr on
  let i : Interaction := ⟨1,[.col 1665 false],sha384EndpointLimbMessage 4,false⟩
  have hi : i∈(sha384SharedAir f0 f1).tables[1]!.interactions := by simp [i,sha384SharedAir,sha384SharedEndpoint]
  have hm : i.multNat tr 1 node pub≠0 := by
    simp [i,Interaction.multNat,Interaction.multNat.go,Expr.eval,Expr.evalWith,rowEnv,on]
  obtain ⟨t,ht,r,hr',j,hj,bus,send,msg,mult⟩ := sha384_shared_receive_match f0 f1 pub tr h (by simp [sha384SharedAir]) hr hi rfl hm
  obtain ⟨table,interaction⟩ := sha384_shared_node_sender f0 f1 t 1 ht (by decide) j hj bus send
  change t=0 at table
  subst t
  subst j
  have phase : tr.cell 0 r (5152+79)=1 := by
    by_cases eq : tr.cell 0 r (5152+79)=1
    · exact eq
    · simp [sharedNodeSender,Interaction.multNat,Interaction.multNat.go,sha384BatchPhase,Expr.eval,Expr.evalWith,rowEnv,eq] at mult
  obtain ⟨b,hb,row,coreTag⟩ := sha384_shared_phase_location f0 f1 pub tr h r 79 hr' (by decide) phase
  change (sha384BatchState true).map _=(sha384EndpointLimbMessage 4).map _ at msg
  rw [sha384_batch_state_message_eval,sha384_endpoint_message_eval] at msg
  simp only [Bool.false_eq_true,ite_false,coreTag,tag,List.cons.injEq] at msg
  have same := congrArg Fp.toNat msg.1
  rw [Fp.toNat_ofNat,Fp.toNat_ofNat,Nat.mod_eq_of_lt (by unfold P;omega : b<P),
    Nat.mod_eq_of_lt (by unfold P;omega : node<P)] at same
  subst b
  rw [row] at msg
  exact msg.2.symm

/-- Feedforward is tied to the same uniquely tagged independent core node. -/
theorem sha384_shared_endpoint_compression (f0 f1 : List (Nat × Nat)) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384SharedAir f0 f1) pub tr) (node : Nat) (hn : node<5) :
    sha384EndpointOutput (tr.cell 1 node)=sha384BatchCompression tr node := by
  have left := sha384_shared_endpoint_A f0 f1 pub tr h node hn
  have right := sha384_shared_endpoint_B f0 f1 pub tr h node hn
  have pf := sha384_shared_endpoint_prefix f0 f1 pub tr h
  have cap := shared_prefix_capacity pf
  have hr : node<tr.height 1 := by omega
  have lc := sha384_shared_core_local f0 f1 pub tr h
  rw [sha384_shared_compression f0 f1 pub tr h node hn]
  apply List.map_congr_left
  intro i hi
  have ib := List.mem_range.mp hi
  have first := sha384_local_round_holds 5 pub tr lc (by decide) node 0 hn (by decide)
  have last := sha384_local_round_holds 5 pub tr lc (by decide) node 79 hn (by decide)
  simp only [Nat.add_zero] at first
  have a := sha384_endpoint_word_decode _ _ 0 false first left i ib
  have b := sha384_endpoint_word_decode _ _ 4 true last right i ib
  simp only [Bool.false_eq_true,ite_false,ite_true] at a b
  rw [sha512_ff_input_words _ first i ib] at a
  rw [sha512_ff_output_words _ last i ib] at b
  have add := sha384_shared_add_sound f0 f1 pub tr h node i hr ib
  rw [a,b] at add
  exact add.symm

/-- The primitive's whole block M64 is supplied by the same unique node record. -/
theorem sha384_shared_core_M (f0 f1 : List (Nat × Nat)) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384SharedAir f0 f1) pub tr) (node : Nat) (hn : node<5) :
    sha384BatchMessage.map (fun e => e.eval tr 0 (80*node) pub)=
      Fp.ofNat node :: (List.range 64).map (fun j => tr.cell 2 node (36+j)) := by
  have metadata := sha384_local_segment_metadata 5 pub tr (sha384_shared_core_local f0 f1 pub tr h)
    (by decide) node 0 hn (by decide)
  simp only [Nat.add_zero] at metadata
  let i : Interaction := ⟨2,[sha384BatchPhase 0],sha384BatchMessage,false⟩
  have hi : i∈(sha384SharedAir f0 f1).tables[0]!.interactions := by simp [i,sha384SharedAir,sha384SharedCore]
  have phase := metadata.2.2.2 0 (by decide)
  simp only [ite_true] at phase
  have hm : i.multNat tr 0 (80*node) pub≠0 := by
    simp [i,Interaction.multNat,Interaction.multNat.go,sha384BatchPhase,Expr.eval,Expr.evalWith,rowEnv,phase]
  obtain ⟨t,ht,r,hr,j,hj,bus,send,msg,mult⟩ := sha384_shared_receive_match f0 f1 pub tr h
    (by simp [sha384SharedAir]) metadata.1 hi rfl hm
  obtain ⟨table,interaction⟩ := sha384_shared_node_sender f0 f1 t 2 ht (by decide) j hj bus send
  change t=2 at table
  subst t
  subst j
  have on := sha384_shared_record_input_active tr pub r 2 (Or.inr rfl) mult
  change ((.col 0 false :: sharedCols 36 64).map (fun e => e.eval tr 2 r pub))=
    (sha384BatchMessage.map (fun e => e.eval tr 0 (80*node) pub)) at msg
  have tag : tr.cell 2 r 0=Fp.ofNat node := by
    have head := congrArg (fun xs : List Fp => xs.headD 0) msg
    simpa [List.headD,sha384BatchMessage,sha384BatchTag,Expr.eval,Expr.evalWith,rowEnv,metadata.2.2.1] using head
  have same := sha384_shared_record_tag_identifies f0 f1 pub tr h r node hr on hn tag
  subst r
  simpa [sharedCols,Function.comp_def,Expr.eval,Expr.evalWith,rowEnv,tag] using msg.symm

/-- Record C32 and D48 are exactly the full feedforward output and its digest
byte expressions, obtained through actual natural bus3 balance. -/
theorem sha384_shared_record_CD (f0 f1 : List (Nat × Nat)) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384SharedAir f0 f1) pub tr) (node : Nat) (hn : node<5) :
    (List.range 80).map (fun j => tr.cell 2 node (100+j))=
      sha384EndpointLimbs (tr.cell 1 node) 8 ++
        sha384EndpointDigestMessage.map (fun e => e.eval tr 1 node pub) := by
  have pf := sha384_shared_record_prefix f0 f1 pub tr h
  have cap := shared_prefix_capacity pf
  have hr : node<tr.height 2 := by omega
  have on := shared_prefix_required pf node hr hn
  have tag := shared_prefix_tag pf node hr on
  let i : Interaction := ⟨3,[.col 1 false],.col 0 false :: sharedCols 100 80,false⟩
  have hi : i∈(sha384SharedAir f0 f1).tables[2]!.interactions := by simp [i,sha384SharedAir,sha384SharedRecords]
  have hm : i.multNat tr 2 node pub≠0 := by
    simp [i,Interaction.multNat,Interaction.multNat.go,Expr.eval,Expr.evalWith,rowEnv,on]
  obtain ⟨t,ht,r,hr',j,hj,bus,send,msg,mult⟩ := sha384_shared_receive_match f0 f1 pub tr h
    (by simp [sha384SharedAir]) hr hi rfl hm
  obtain ⟨table,interaction⟩ := sha384_shared_node_sender f0 f1 t 3 ht (by decide) j hj bus send
  change t=1 at table
  subst t
  subst j
  have active : tr.cell 1 r 1665=1 := by
    by_cases eq : tr.cell 1 r 1665=1
    · exact eq
    · simp [sharedNodeSender,Interaction.multNat,Interaction.multNat.go,Expr.eval,Expr.evalWith,rowEnv,eq] at mult
  have ep := sha384_shared_endpoint_prefix f0 f1 pub tr h
  have rbound := shared_prefix_bounded ep r hr' active
  have rtag := shared_prefix_tag ep r hr' active
  change ((sha384EndpointLimbMessage 8 ++ sha384EndpointDigestMessage).map (fun e => e.eval tr 1 r pub))=
    ((.col 0 false :: sharedCols 100 80).map (fun e => e.eval tr 2 node pub)) at msg
  rw [List.map_append,sha384_endpoint_message_eval] at msg
  simp only [List.cons_append,List.map_cons,sharedCols,List.map_map,Function.comp_def,
    Expr.eval,Expr.evalWith,rowEnv,Bool.false_eq_true,ite_false,tag,rtag,List.cons.injEq] at msg
  have same := congrArg Fp.toNat msg.1
  rw [Fp.toNat_ofNat,Fp.toNat_ofNat,Nat.mod_eq_of_lt (by unfold P;omega : r<P),
    Nat.mod_eq_of_lt (by unfold P;omega : node<P)] at same
  subst r
  exact msg.2.symm

end NearCompression
