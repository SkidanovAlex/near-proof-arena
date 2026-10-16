import NearCompression.SHA384NodeChunkRouting
import NearCompression.SHA384BatchedRouting

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 NearSpecV3.SHA512
set_option maxRecDepth 65536

def chunkNodeSenderTable (bus : Nat) : Nat := if bus=1 then 0 else if bus=3 then 1 else 2
def chunkNodeSender (base bits bus : Nat) : Interaction :=
  if bus=0 then ⟨0,[.const 0,.col 1 false],chunkGlobal base (.col 0 false :: sharedCols (2+bits) 32),true⟩
  else if bus=1 then ⟨1,[sha384BatchPhase 79],chunkGlobal base (sha384BatchState true),true⟩
  else if bus=2 then ⟨2,[.col 1 false],chunkGlobal base (.col 0 false :: sharedCols (2+bits+32) 64),true⟩
  else ⟨3,[.col 1665 false],chunkGlobal base (sha384EndpointLimbMessage 8 ++ sha384EndpointDigestMessage),true⟩

theorem sha384_chunk_node_sender (base count bits uses : Nat) (t bus : Nat)
    (ht : t<(sha384NodeChunkAir base count bits uses).tables.length) (hb : bus<4) (i : Interaction)
    (hi : i∈(sha384NodeChunkAir base count bits uses).tables[t]!.interactions)
    (busEq : i.bus=bus) (send : i.send=true) :
    t=chunkNodeSenderTable bus ∧ i=chunkNodeSender base bits bus := by
  have buses : bus=0 ∨ bus=1 ∨ bus=2 ∨ bus=3 := by omega
  have cases : t=0 ∨ t=1 ∨ t=2 ∨ t=3 := by
    simp only [sha384NodeChunkAir,List.length_cons,List.length_nil] at ht;omega
  rcases cases with rfl | rfl | rfl | rfl
  all_goals simp only [sha384NodeChunkAir,List.getElem!_cons_zero,List.getElem!_cons_succ,
    List.mem_cons,List.not_mem_nil,or_false] at hi
  · rcases hi with rfl | rfl | rfl <;> rcases buses with rfl | rfl | rfl | rfl <;>
      simp_all [chunkNodeSenderTable,chunkNodeSender]
  · rcases hi with rfl | rfl | rfl <;> rcases buses with rfl | rfl | rfl | rfl <;>
      simp_all [chunkNodeSenderTable,chunkNodeSender]
  · rcases hi with rfl | rfl | rfl | rfl <;> rcases buses with rfl | rfl | rfl | rfl <;>
      simp_all [chunkNodeSenderTable,chunkNodeSender]
  · subst i; simp at send

theorem sha384_chunk_record_input_active (base bits : Nat) (tr : Trace Fp) (pub : List Fp) (r bus : Nat)
    (hb : bus=0 ∨ bus=2) (hm : (chunkNodeSender base bits bus).multNat tr 2 r pub≠0) :
    tr.cell 2 r 1=1 := by
  by_cases on : tr.cell 2 r 1=1
  · exact on
  · rcases hb with rfl | rfl <;>
      simp [chunkNodeSender,Interaction.multNat,Interaction.multNat.go,Expr.eval,Expr.evalWith,rowEnv,on] at hm
    exact False.elim ((by decide : (0:Fp)≠1) hm)

/-- Any bus0 receiver gets the A32 state from one actual active record. -/
theorem sha384_chunk_receive_A (base count bits uses : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384NodeChunkAir base count bits uses) pub tr) {t r : Nat}
    (ht : t<(sha384NodeChunkAir base count bits uses).tables.length) (hr : r<tr.height t)
    {i : Interaction} (hi : i∈(sha384NodeChunkAir base count bits uses).tables[t]!.interactions)
    (hb : i.bus=0) (hs : i.send=false) (hm : i.multNat tr t r pub≠0) :
    ∃ s,s<tr.height 2 ∧ tr.cell 2 s 1=1 ∧
      (chunkGlobal base (.col 0 false :: sharedCols (2+bits) 32)).map (fun e=>e.eval tr 2 s pub)=i.msgVal tr t r pub := by
  obtain ⟨u,hu,s,hs',j,hj,bus,send,msg,mult⟩ := sha384_chunk_receive_match base count bits uses pub tr h ht hr hi hs hm
  rw [hb] at bus
  obtain ⟨table,interaction⟩ := sha384_chunk_node_sender base count bits uses u 0 hu (by decide) j hj bus send
  change u=2 at table
  subst u
  subst j
  have on := sha384_chunk_record_input_active base bits tr pub s 0 (Or.inl rfl) mult
  refine ⟨s,hs',on,?_⟩
  simpa only [chunkNodeSender,ite_true,Interaction.msgVal] using msg

/-- Every active core phase is attached to exactly one canonical node index. -/
theorem sha384_chunk_phase_location (base count bits uses : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384NodeChunkAir base count bits uses) pub tr) (positive : 0<count) (small : count<P) (r phase : Nat)
    (hr : r<tr.height 0) (hp : phase<80) (one : tr.cell 0 r (5152+phase)=1) :
    ∃ node,node<count ∧ r=80*node+phase ∧ tr.cell 0 r 5233=Fp.ofNat node := by
  have lc := sha384_chunk_core_local base count bits uses pub tr h positive
  have on : tr.cell 0 r 5232=1 := by
    rcases sha384_local_active_boolean count pub tr lc r hr with zero | on
    · have inactive := sha384_local_inactive_phase count pub tr lc r hr zero phase hp
      rw [one] at inactive
      exact False.elim ((by decide : (1:Fp)≠0) inactive)
    · exact on
  have range := sha384_local_active_bounded count pub tr lc small r hr on
  have ph := sha384_local_active_phase count pub tr lc r hr on phase hp
  rw [one] at ph
  have same : phase=r%80 := by
    by_cases eq : phase=r%80
    · exact eq
    · rw [ite_eq_right eq] at ph
      exact False.elim ((by decide : (1:Fp)≠0) ph)
  exact ⟨r/80,by omega,by omega,sha384_local_active_tag count pub tr lc r hr on⟩

theorem sha384_chunk_record_tag_identifies (base count bits uses : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384NodeChunkAir base count bits uses) pub tr) (positive : 0<count) (small : count<P) (r node : Nat) (hr : r<tr.height 2)
    (on : tr.cell 2 r 1=1) (hn : node<count) (tag : tr.cell 2 r 0=Fp.ofNat node) : r=node := by
  have pf := sha384_chunk_record_prefix base count bits uses pub tr h positive small
  rw [shared_prefix_tag pf r hr on] at tag
  have bound := shared_prefix_bounded pf r hr on
  have eq := congrArg Fp.toNat tag
  simpa only [Fp.toNat_ofNat,Nat.mod_eq_of_lt (by omega : r<P),
    Nat.mod_eq_of_lt (by omega : node<P)] using eq

theorem sha384_chunk_core_A (base count bits uses : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384NodeChunkAir base count bits uses) pub tr) (positive : 0<count) (small : count<P) (node : Nat) (hn : node<count) :
    sha384CoreLimbs (tr.cell 0 (80*node)) false=(List.range 32).map (fun j => tr.cell 2 node (2+bits+j)) := by
  have metadata := sha384_local_segment_metadata count pub tr (sha384_chunk_core_local base count bits uses pub tr h positive)
    small node 0 hn (by decide)
  simp only [Nat.add_zero] at metadata
  let i : Interaction := ⟨0,[sha384BatchPhase 0],chunkGlobal base (sha384BatchState false),false⟩
  have hi : i∈(sha384NodeChunkAir base count bits uses).tables[0]!.interactions := by simp [i,sha384NodeChunkAir]
  have phase := metadata.2.2.2 0 (by decide)
  simp only [ite_true] at phase
  have hm : i.multNat tr 0 (80*node) pub≠0 := by
    simp [i,Interaction.multNat,Interaction.multNat.go,sha384BatchPhase,Expr.eval,Expr.evalWith,rowEnv,phase]
  obtain ⟨r,hr,on,msg⟩ := sha384_chunk_receive_A base count bits uses pub tr h (by simp [sha384NodeChunkAir]) metadata.1 hi rfl rfl hm
  change (chunkGlobal base (.col 0 false::sharedCols (2+bits) 32)).map _=
    (chunkGlobal base (sha384BatchState false)).map _ at msg
  have msg := (chunk_global_match base tr 2 r 0 (80*node) pub _ _ (by simp) (by simp [sha384BatchState])).mp msg
  rw [sha384_batch_state_message_eval] at msg
  simp only [List.map_cons,sharedCols,List.map_map,Function.comp_def,Expr.eval,Expr.evalWith,rowEnv] at msg
  simp only [Bool.false_eq_true,ite_false,metadata.2.2.1,List.cons.injEq] at msg
  have same := sha384_chunk_record_tag_identifies base count bits uses pub tr h positive small r node hr on hn msg.1
  subst r
  exact msg.2.symm

theorem sha384_chunk_endpoint_A (base count bits uses : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384NodeChunkAir base count bits uses) pub tr) (positive : 0<count) (small : count<P) (node : Nat) (hn : node<count) :
    sha384EndpointLimbs (tr.cell 1 node) 0=sha384CoreLimbs (tr.cell 0 (80*node)) false := by
  have pf := sha384_chunk_endpoint_prefix base count bits uses pub tr h positive small
  have cap := shared_prefix_capacity pf
  have hr : node<tr.height 1 := by omega
  have on := shared_prefix_required pf node hr hn
  have tag := shared_prefix_tag pf node hr on
  let i : Interaction := ⟨0,[.col 1665 false],chunkGlobal base (sha384EndpointLimbMessage 0),false⟩
  have hi : i∈(sha384NodeChunkAir base count bits uses).tables[1]!.interactions := by simp [i,sha384NodeChunkAir]
  have hm : i.multNat tr 1 node pub≠0 := by
    simp [i,Interaction.multNat,Interaction.multNat.go,Expr.eval,Expr.evalWith,rowEnv,on]
  obtain ⟨r,hr',active,msg⟩ := sha384_chunk_receive_A base count bits uses pub tr h (by simp [sha384NodeChunkAir]) hr hi rfl rfl hm
  change (chunkGlobal base (.col 0 false::sharedCols (2+bits) 32)).map _=
    (chunkGlobal base (sha384EndpointLimbMessage 0)).map _ at msg
  have msg := (chunk_global_match base tr 2 r 1 node pub _ _ (by simp) (by simp [sha384EndpointLimbMessage])).mp msg
  rw [sha384_endpoint_message_eval,tag] at msg
  simp only [List.map_cons,sharedCols,List.map_map,Function.comp_def,Expr.eval,Expr.evalWith,rowEnv,Bool.false_eq_true,ite_false] at msg
  have same := sha384_chunk_record_tag_identifies base count bits uses pub tr h positive small r node hr' active hn (List.cons.inj msg).1
  subst r
  rw [sha384_chunk_core_A base count bits uses pub tr h positive small node hn]
  exact (List.cons.inj msg).2.symm

theorem sha384_chunk_endpoint_B (base count bits uses : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384NodeChunkAir base count bits uses) pub tr) (positive : 0<count) (small : count<P) (node : Nat) (hn : node<count) :
    sha384EndpointLimbs (tr.cell 1 node) 4=sha384CoreLimbs (tr.cell 0 (80*node+79)) true := by
  have pf := sha384_chunk_endpoint_prefix base count bits uses pub tr h positive small
  have cap := shared_prefix_capacity pf
  have hr : node<tr.height 1 := by omega
  have on := shared_prefix_required pf node hr hn
  have tag := shared_prefix_tag pf node hr on
  let i : Interaction := ⟨1,[.col 1665 false],chunkGlobal base (sha384EndpointLimbMessage 4),false⟩
  have hi : i∈(sha384NodeChunkAir base count bits uses).tables[1]!.interactions := by simp [i,sha384NodeChunkAir]
  have hm : i.multNat tr 1 node pub≠0 := by
    simp [i,Interaction.multNat,Interaction.multNat.go,Expr.eval,Expr.evalWith,rowEnv,on]
  obtain ⟨t,ht,r,hr',j,hj,bus,send,msg,mult⟩ := sha384_chunk_receive_match base count bits uses pub tr h (by simp [sha384NodeChunkAir]) hr hi rfl hm
  obtain ⟨table,interaction⟩ := sha384_chunk_node_sender base count bits uses t 1 ht (by decide) j hj bus send
  change t=0 at table
  subst t
  subst j
  have phase : tr.cell 0 r (5152+79)=1 := by
    by_cases eq : tr.cell 0 r (5152+79)=1
    · exact eq
    · simp [chunkNodeSender,Interaction.multNat,Interaction.multNat.go,sha384BatchPhase,Expr.eval,Expr.evalWith,rowEnv,eq] at mult
  obtain ⟨b,hb,row,coreTag⟩ := sha384_chunk_phase_location base count bits uses pub tr h positive small r 79 hr' (by decide) phase
  change (chunkGlobal base (sha384BatchState true)).map _=(chunkGlobal base (sha384EndpointLimbMessage 4)).map _ at msg
  have msg := (chunk_global_match base tr 0 r 1 node pub _ _ (by simp [sha384BatchState]) (by simp [sha384EndpointLimbMessage])).mp msg
  rw [sha384_batch_state_message_eval,sha384_endpoint_message_eval] at msg
  simp only [Bool.false_eq_true,ite_false,coreTag,tag,List.cons.injEq] at msg
  have same := congrArg Fp.toNat msg.1
  rw [Fp.toNat_ofNat,Fp.toNat_ofNat,Nat.mod_eq_of_lt (by omega : b<P),
    Nat.mod_eq_of_lt (by omega : node<P)] at same
  subst b
  rw [row] at msg
  exact msg.2.symm

/-- Feedforward is tied to the same uniquely tagged independent core node. -/
theorem sha384_chunk_endpoint_compression (base count bits uses : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384NodeChunkAir base count bits uses) pub tr) (positive : 0<count) (small : count<P) (node : Nat) (hn : node<count) :
    sha384EndpointOutput (tr.cell 1 node)=sha384BatchCompression tr node := by
  have left := sha384_chunk_endpoint_A base count bits uses pub tr h positive small node hn
  have right := sha384_chunk_endpoint_B base count bits uses pub tr h positive small node hn
  have pf := sha384_chunk_endpoint_prefix base count bits uses pub tr h positive small
  have cap := shared_prefix_capacity pf
  have hr : node<tr.height 1 := by omega
  have lc := sha384_chunk_core_local base count bits uses pub tr h positive
  rw [sha384_local_compression count pub tr (sha384_chunk_core_local base count bits uses pub tr h positive) small node hn]
  apply List.map_congr_left
  intro i hi
  have ib := List.mem_range.mp hi
  have first := sha384_local_round_holds count pub tr lc small node 0 hn (by decide)
  have last := sha384_local_round_holds count pub tr lc small node 79 hn (by decide)
  simp only [Nat.add_zero] at first
  have a := sha384_endpoint_word_decode _ _ 0 false first left i ib
  have b := sha384_endpoint_word_decode _ _ 4 true last right i ib
  simp only [Bool.false_eq_true,ite_false,ite_true] at a b
  rw [sha512_ff_input_words _ first i ib] at a
  rw [sha512_ff_output_words _ last i ib] at b
  have add := sha384_chunk_add_sound base count bits uses pub tr h node i hr ib
  rw [a,b] at add
  exact add.symm

/-- The primitive's whole block M64 is supplied by the same unique node record. -/
theorem sha384_chunk_core_M (base count bits uses : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384NodeChunkAir base count bits uses) pub tr) (positive : 0<count) (small : count<P) (node : Nat) (hn : node<count) :
    sha384BatchMessage.map (fun e => e.eval tr 0 (80*node) pub)=
      Fp.ofNat node :: (List.range 64).map (fun j => tr.cell 2 node (2+bits+32+j)) := by
  have metadata := sha384_local_segment_metadata count pub tr (sha384_chunk_core_local base count bits uses pub tr h positive)
    small node 0 hn (by decide)
  simp only [Nat.add_zero] at metadata
  let i : Interaction := ⟨2,[sha384BatchPhase 0],chunkGlobal base sha384BatchMessage,false⟩
  have hi : i∈(sha384NodeChunkAir base count bits uses).tables[0]!.interactions := by simp [i,sha384NodeChunkAir]
  have phase := metadata.2.2.2 0 (by decide)
  simp only [ite_true] at phase
  have hm : i.multNat tr 0 (80*node) pub≠0 := by
    simp [i,Interaction.multNat,Interaction.multNat.go,sha384BatchPhase,Expr.eval,Expr.evalWith,rowEnv,phase]
  obtain ⟨t,ht,r,hr,j,hj,bus,send,msg,mult⟩ := sha384_chunk_receive_match base count bits uses pub tr h
    (by simp [sha384NodeChunkAir]) metadata.1 hi rfl hm
  obtain ⟨table,interaction⟩ := sha384_chunk_node_sender base count bits uses t 2 ht (by decide) j hj bus send
  change t=2 at table
  subst t
  subst j
  have on := sha384_chunk_record_input_active base bits tr pub r 2 (Or.inr rfl) mult
  change (chunkGlobal base (.col 0 false::sharedCols (2+bits+32) 64)).map _=
    (chunkGlobal base sha384BatchMessage).map _ at msg
  have msg := (chunk_global_match base tr 2 r 0 (80*node) pub _ _ (by simp) (by simp [sha384BatchMessage])).mp msg
  have tag : tr.cell 2 r 0=Fp.ofNat node := by
    have head := congrArg (fun xs : List Fp => xs.headD 0) msg
    simpa [List.headD,sha384BatchMessage,sha384BatchTag,Expr.eval,Expr.evalWith,rowEnv,metadata.2.2.1] using head
  have same := sha384_chunk_record_tag_identifies base count bits uses pub tr h positive small r node hr on hn tag
  subst r
  simpa [sharedCols,Function.comp_def,Expr.eval,Expr.evalWith,rowEnv,tag] using msg.symm

/-- Record C32 and D48 are exactly the full feedforward output and its digest
byte expressions, obtained through actual natural bus3 balance. -/
theorem sha384_chunk_record_CD (base count bits uses : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384NodeChunkAir base count bits uses) pub tr) (positive : 0<count) (small : count<P) (node : Nat) (hn : node<count) :
    (List.range 80).map (fun j => tr.cell 2 node (2+bits+96+j))=
      sha384EndpointLimbs (tr.cell 1 node) 8 ++
        sha384EndpointDigestMessage.map (fun e => e.eval tr 1 node pub) := by
  have pf := sha384_chunk_record_prefix base count bits uses pub tr h positive small
  have cap := shared_prefix_capacity pf
  have hr : node<tr.height 2 := by omega
  have on := shared_prefix_required pf node hr hn
  have tag := shared_prefix_tag pf node hr on
  let i : Interaction := ⟨3,[.col 1 false],chunkGlobal base (.col 0 false :: sharedCols (2+bits+96) 80),false⟩
  have hi : i∈(sha384NodeChunkAir base count bits uses).tables[2]!.interactions := by simp [i,sha384NodeChunkAir]
  have hm : i.multNat tr 2 node pub≠0 := by
    simp [i,Interaction.multNat,Interaction.multNat.go,Expr.eval,Expr.evalWith,rowEnv,on]
  obtain ⟨t,ht,r,hr',j,hj,bus,send,msg,mult⟩ := sha384_chunk_receive_match base count bits uses pub tr h
    (by simp [sha384NodeChunkAir]) hr hi rfl hm
  obtain ⟨table,interaction⟩ := sha384_chunk_node_sender base count bits uses t 3 ht (by decide) j hj bus send
  change t=1 at table
  subst t
  subst j
  have active : tr.cell 1 r 1665=1 := by
    by_cases eq : tr.cell 1 r 1665=1
    · exact eq
    · simp [chunkNodeSender,Interaction.multNat,Interaction.multNat.go,Expr.eval,Expr.evalWith,rowEnv,eq] at mult
  have ep := sha384_chunk_endpoint_prefix base count bits uses pub tr h positive small
  have rbound := shared_prefix_bounded ep r hr' active
  have rtag := shared_prefix_tag ep r hr' active
  change (chunkGlobal base (sha384EndpointLimbMessage 8 ++ sha384EndpointDigestMessage)).map _=
    (chunkGlobal base (.col 0 false::sharedCols (2+bits+96) 80)).map _ at msg
  have msg := (chunk_global_match base tr 1 r 2 node pub _ _
    (by simp [sha384EndpointLimbMessage]) (by simp)).mp msg
  rw [List.map_append,sha384_endpoint_message_eval] at msg
  simp only [List.cons_append,List.map_cons,sharedCols,List.map_map,Function.comp_def,
    Expr.eval,Expr.evalWith,rowEnv,Bool.false_eq_true,ite_false,tag,rtag,List.cons.injEq] at msg
  have same := congrArg Fp.toNat msg.1
  rw [Fp.toNat_ofNat,Fp.toNat_ofNat,Nat.mod_eq_of_lt (by omega : r<P),
    Nat.mod_eq_of_lt (by omega : node<P)] at same
  subst r
  exact msg.2.symm

end NearCompression
