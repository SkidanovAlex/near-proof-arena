import ZkFormal.NearV3.Assembly.TrieVParent

/-!
# ZkFormal.NearV3.Assembly.TrieParent — `PARENT` balance of the honest trie entries

Every node record `n` receives `PARENT [n, τ, depth, len, res]`; revealed kid windows send
`[c, τ, depth + 1, clen, cres]` and heads send `[rid, τ, 0, rlen, rres]`.  For the seeded
forest (`forestNodes`, DFS ids = positions) a record's receive is sent by its parent's kid
window (`viewKid`), or — for a tree root — by the tree's head (`forestWalkHeads`):

* `seedNodesT_parent` / `seedKidsT_parent` (mutual): the receives of a seeded tree are a
  permutation of its root message and its records' kid-window sends;
* `forestNodes_parent`: over the forest, the root messages are the heads' sends, provided every
  tree is revealed (`isNode`);
* the metadata passes keep every field of the messages.

`parentBal_native`: `Link3.ParentBal` for `TrieNative.nodes … q` and `TrieNative.heads … keys`
when every pre tree is a node and well-formed; `accepted_forest_isNode` derives both from
acceptance (the scheduler upsert of every pre tree succeeds, so no root is a bare hash).
`balancedAt_parent`: the bundle-level equation.
-/

namespace ZkFormal.NearV3.Assembly.TrieParent

open NearSpec NearSpecV3 ZkFormal.Near ZkFormal.NearV3 ZkFormal.NearV3.Assembly Render Render.UpsGen
  Rcpt.Candidates Rcpt.Candidates.NodePostUpdate ZkFormal.NearV3.Candidates

/-- Kid-window `PARENT` sends of a record. -/
def pS (s : NodeS3) : List ZkFormal.Near.Msg :=
  s.v.revealed.map fun (c, l, r, _, _) => [c, s.tau, s.depth + 1, l, r]

/-- The `PARENT` receive of record `n`. -/
def pR (s : NodeS3) (n : Nat) : ZkFormal.Near.Msg := [n, s.tau, s.depth, (s.v.ser false).length, s.res]

/-- Receives of a record list whose first id is `n`. -/
def recvFrom : Nat → List NodeS3 → List ZkFormal.Near.Msg
  | _, [] => []
  | n, s :: ss => pR s n :: recvFrom (n + 1) ss

theorem recvFrom_append : ∀ (n : Nat) (a b : List NodeS3),
    recvFrom n (a ++ b) = recvFrom n a ++ recvFrom (n + a.length) b
  | _, [], b => by simp [recvFrom]
  | n, s :: a, b => by
    simp only [List.cons_append, recvFrom, recvFrom_append (n + 1) a b, List.length_cons]
    rw [show n + 1 + a.length = n + (a.length + 1) by omega]

/-- The `PARENT` message of a tree root at id `n`, depth `d`. -/
def rootMsg (tau d n : Nat) (t : PTrie) : ZkFormal.Near.Msg := [n, tau, d, (nodeEnc t).length, viewTarget n t]

def rootOpt (tau d n : Nat) (t : PTrie) : List ZkFormal.Near.Msg := if isNode t then [rootMsg tau d n t] else []

/-- The root messages of the revealed kids of a kid list (ids allocated as in `seedKidsT`). -/
def kidWins (tau d : Nat) : Nat → Kids → List ZkFormal.Near.Msg
  | _, .nil => []
  | n, .none r => kidWins tau d n r
  | n, .some c r => rootOpt tau d n c ++ kidWins tau d (n + tsize c) r

def revMsgs (tau d : Nat) (ks : List NKid) : List ZkFormal.Near.Msg :=
  (ks.filterMap fun
      | .node c l r pre po => some (c, l, r, pre, po)
      | _ => none).map fun (c, l, r, _, _) => [c, tau, d, l, r]

theorem viewKids_wins (tau d : Nat) : ∀ n cs, revMsgs tau d (viewKids n cs) = kidWins tau d n cs
  | _, .nil => rfl
  | n, .none r => by
    simp only [viewKids, revMsgs, List.filterMap_cons, kidWins] at *
    exact viewKids_wins tau d n r
  | n, .some c r => by
    have ih := viewKids_wins tau d (n + tsize c) r
    simp only [revMsgs] at ih
    simp only [viewKids, revMsgs, List.filterMap_cons, kidWins, rootOpt, viewKid]
    by_cases hc : isNode c = true
    · simp [hc, ih, rootMsg]
    · simp [hc, ih]

theorem seedNodesT_length' (tau d n v : Nat) (t : PTrie) : (seedNodesT tau d n v t).length = tsize t :=
  seedNodesT_length tau d n v t

theorem seedNodeView_pR (tau d n v : Nat) (t : PTrie) (hw : t.wf = true) (hn : isNode t = true) :
    pR (seedNodeView tau d n v t) n = rootMsg tau d n t := by
  simp only [pR, seedNodeView, rootMsg, viewNode_ser n v t hw hn false, List.length_map]

mutual
theorem seedNodesT_parent (tau : Nat) : ∀ d n v t, t.wf = true →
    (recvFrom n (seedNodesT tau d n v t)).Perm (rootOpt tau d n t ++ (seedNodesT tau d n v t).flatMap pS)
  | _, _, _, .hash _, _ => by simp [seedNodesT, recvFrom, rootOpt, isNode]
  | d, n, v, .leaf k s m, hw => by
    simp only [seedNodesT, recvFrom, rootOpt, isNode, ite_true, List.flatMap_cons, List.flatMap_nil,
      seedNodeView_pR tau d n v _ hw rfl]
    simp [pS, seedNodeView, viewNode, NodeV3.revealed]
  | d, n, v, .ext k c m, hw => by
    have hc : c.wf = true := by
      simp only [PTrie.wf, Bool.and_eq_true] at hw
      exact hw.1.1.2
    have ih := seedNodesT_parent tau (d+1) (n+1) v c hc
    simp only [seedNodesT, recvFrom, rootOpt, isNode, ite_true, List.flatMap_cons,
      seedNodeView_pR tau d n v _ hw rfl, List.singleton_append]
    apply List.Perm.cons
    have hs : pS (seedNodeView tau d n v (.ext k c m)) = rootOpt tau (d+1) (n+1) c := by
      simp only [pS, seedNodeView, viewNode, viewKid, rootOpt]
      by_cases hn : isNode c = true
      · simp [hn, NodeV3.revealed, rootMsg]
      · simp [hn, NodeV3.revealed]
    rw [hs]
    exact ih
  | d, n, v, .branch sv cs m, hw => by
    have hk : Kids.wf cs 16 = true := by
      simp only [PTrie.wf, Bool.and_eq_true] at hw
      exact hw.1.2
    have ih := seedKidsT_parent tau (d+1) (n+1) (v+(optSlotVal sv).length) cs 16 hk
    simp only [seedNodesT, recvFrom, rootOpt, isNode, ite_true, List.flatMap_cons,
      seedNodeView_pR tau d n v _ hw rfl, List.singleton_append]
    apply List.Perm.cons
    have hs : pS (seedNodeView tau d n v (.branch sv cs m)) = kidWins tau (d+1) (n+1) cs := by
      rw [← viewKids_wins]
      simp only [pS, seedNodeView, viewNode, NodeV3.revealed, revMsgs]
      rfl
    rw [hs]
    exact ih
theorem seedKidsT_parent (tau : Nat) : ∀ d n v cs k, Kids.wf cs k = true →
    (recvFrom n (seedKidsT tau d n v cs)).Perm (kidWins tau d n cs ++ (seedKidsT tau d n v cs).flatMap pS)
  | _, _, _, .nil, _, _ => by simp [seedKidsT, recvFrom, kidWins]
  | d, n, v, .none rest, k, hw => by
    have hr : Kids.wf rest (k - 1) = true := by
      simp only [Kids.wf, Bool.and_eq_true] at hw
      exact hw.2
    simpa [seedKidsT, kidWins] using seedKidsT_parent tau d n v rest (k - 1) hr
  | d, n, v, .some c rest, k, hw => by
    have h2 : c.wf = true ∧ Kids.wf rest (k - 1) = true := by
      simp only [Kids.wf, Bool.and_eq_true] at hw
      exact ⟨hw.1.2, hw.2⟩
    have ihc := seedNodesT_parent tau d n v c h2.1
    have ihr := seedKidsT_parent tau d (n + tsize c) (v + (valsOf c).length) rest (k - 1) h2.2
    simp only [seedKidsT, recvFrom_append, seedNodesT_length', kidWins, List.flatMap_append]
    refine (ihc.append ihr).trans ?_
    simp only [List.append_assoc]
    apply List.Perm.append_left
    exact List.perm_append_comm_assoc _ _ _
end

/-- Root messages of a forest (one per tree, ids as in `forestNodes`). -/
def forestRoots : Nat → Nat → List PTrie → List ZkFormal.Near.Msg
  | _, _, [] => []
  | tau, n, t :: ts => rootOpt tau 0 n t ++ forestRoots (tau + 1) (n + tsize t) ts

theorem forestNodes_parent : ∀ tau nid vid ts, (∀ t ∈ ts, t.wf = true) →
    (recvFrom nid (forestNodes tau nid vid ts)).Perm
      (forestRoots tau nid ts ++ (forestNodes tau nid vid ts).flatMap pS)
  | _, _, _, [], _ => by simp [forestNodes, recvFrom, forestRoots]
  | tau, nid, vid, t :: ts, hw => by
    have iht := seedNodesT_parent tau 0 nid vid t (hw t (by simp))
    have ihr := forestNodes_parent (tau + 1) (nid + tsize t) (vid + (valsOf t).length) ts
      (fun t' h => hw t' (by simp [h]))
    simp only [forestNodes, recvFrom_append, seedNodesT_length', forestRoots, List.flatMap_append]
    refine (iht.append ihr).trans ?_
    simp only [List.append_assoc]
    apply List.Perm.append_left
    exact List.perm_append_comm_assoc _ _ _

/-- The heads' `PARENT` sends are the forest's root messages when every tree is revealed. -/
theorem forestWalkHeads_parent : ∀ tau n (pairs : List (PTrie × PTrie)),
    (∀ p ∈ pairs, isNode p.1 = true) →
    (forestWalkHeads tau n pairs).map (fun h => [h.rid, h.tau, 0, h.rlen, h.rres]) =
      forestRoots tau n (pairs.map Prod.fst)
  | _, _, [], _ => rfl
  | tau, n, (pre, post) :: rest, hn => by
    have h1 : isNode pre = true := hn (pre, post) (by simp)
    simp only [forestWalkHeads, List.map_cons, forestRoots, rootOpt, h1, ite_true, rootMsg,
      List.singleton_append, forestWalkHeads_parent (tau + 1) (n + tsize pre) rest
        (fun p hp => hn p (by simp [hp]))]

/-! ## Metadata passes -/

theorem pS_record (u : Inputs) (s : NodeS3) : pS (record u s) = pS s := by
  rcases s with ⟨v, tau, depth, res, uses, ubm, dup, hd, repE, ucid, mU⟩
  simp only [pS, record]
  cases v with
  | leaf k sl m => rfl
  | ext k c m => cases c <;> rfl
  | branch sv cs m =>
    simp only [node, NodeV3.revealed]
    induction cs with
    | nil => rfl
    | cons c cs ih =>
      cases c <;> simp_all [kid]

theorem pR_record (u : Inputs) (s : NodeS3) (n : Nat) : pR (record u s) n = pR s n := by
  simp only [pR, record, node_pre]

theorem recvFrom_records (u : Inputs) : ∀ (n : Nat) (ss : List NodeS3),
    recvFrom n (records u ss) = recvFrom n ss
  | _, [] => rfl
  | n, s :: ss => by
    simp only [records, List.map_cons, recvFrom, pR_record] at *
    rw [show (ss.map (record u)) = records u ss from rfl, recvFrom_records u (n + 1) ss]

theorem recvFrom_initialize : ∀ (n : Nat) (ss : List NodeS3), recvFrom n (initializeList n ss) = recvFrom n ss
  | _, [] => rfl
  | n, s :: ss => by
    simp only [initializeList, recvFrom, recvFrom_initialize (n + 1) ss]
    rfl

theorem recvFrom_assign (rs : List StoreDuplicateChain.Entry) :
    ∀ (n : Nat) (ss : List NodeS3), recvFrom n (ChainMetadata.assign rs n ss) = recvFrom n ss
  | _, [] => rfl
  | n, s :: ss => by
    simp only [ChainMetadata.assign, recvFrom, recvFrom_assign rs (n + 1) ss]
    rfl

theorem recvFrom_assignList (q : UseRequests) :
    ∀ (n : Nat) (ss : List NodeS3), recvFrom n (assignList q n ss) = recvFrom n ss
  | _, [] => rfl
  | n, s :: ss => by
    simp only [assignList, recvFrom, recvFrom_assignList q (n + 1) ss]
    rfl

theorem pS_initialize : ∀ (n : Nat) (ss : List NodeS3), (initializeList n ss).flatMap pS = ss.flatMap pS
  | _, [] => rfl
  | n, s :: ss => by simp only [initializeList, List.flatMap_cons, pS_initialize (n + 1) ss]; rfl

theorem pS_assign (rs : List StoreDuplicateChain.Entry) :
    ∀ (n : Nat) (ss : List NodeS3), (ChainMetadata.assign rs n ss).flatMap pS = ss.flatMap pS
  | _, [] => rfl
  | n, s :: ss => by simp only [ChainMetadata.assign, List.flatMap_cons, pS_assign rs (n + 1) ss]; rfl

theorem pS_assignList (q : UseRequests) :
    ∀ (n : Nat) (ss : List NodeS3), (assignList q n ss).flatMap pS = ss.flatMap pS
  | _, [] => rfl
  | n, s :: ss => by simp only [assignList, List.flatMap_cons, pS_assignList q (n + 1) ss]; rfl

theorem pS_records (u : Inputs) (ss : List NodeS3) : (records u ss).flatMap pS = ss.flatMap pS := by
  unfold records
  rw [List.flatMap_map]
  simp only [pS_record]

/-! ## The balance -/

theorem nodeSends_parent (vs : List NodeS3) : nodeSends3 vs B_PARENT = vs.flatMap pS := by
  rw [Link3.parentS]
  have : ∀ (l : List NodeS3) (k : Nat), (l.zip (List.range' k l.length)).flatMap
      (fun x => x.1.v.revealed.map fun (c, l, r, _, _) => [c, x.1.tau, x.1.depth + 1, l, r]) = l.flatMap pS := by
    intro l
    induction l with
    | nil => intro k; rfl
    | cons a l ih => intro k; simp only [List.length_cons, List.range'_succ, List.zip_cons_cons,
        List.flatMap_cons, ih]; rfl
  rw [List.range_eq_range']
  exact this vs 0

theorem nodeRecvs_parent (vs : List NodeS3) : nodeRecvs3 vs B_PARENT = recvFrom 0 vs := by
  rw [Link3.parentR]
  have : ∀ (l : List NodeS3) (k : Nat), (l.zip (List.range' k l.length)).map
      (fun x => [x.2, x.1.tau, x.1.depth, (x.1.v.ser false).length, x.1.res]) = recvFrom k l := by
    intro l
    induction l with
    | nil => intro k; rfl
    | cons a l ih => intro k; simp only [List.length_cons, List.range'_succ, List.zip_cons_cons,
        List.map_cons, ih, recvFrom, pR]
  rw [List.range_eq_range']
  exact this vs 0

/-- **`PARENT` balance of the honest node and head entries**, for revealed well-formed pre trees. -/
theorem parentBal_native (m : MainExecutionV3) (steps : List ImplicitStepV3) (oldPost : PTrie)
    (writes : List (List Nat × Bytes)) (q : UseRequests) (keys : List ZkFormal.Near.Msg)
    (hw : ∀ t ∈ TrieNative.forest m steps, t.wf = true)
    (hn : ∀ t ∈ TrieNative.forest m steps, isNode t = true) :
    Link3.ParentBal (TrieNative.nodes m steps oldPost writes q) (TrieNative.heads m steps oldPost writes keys) := by
  intro msg
  have hpre := nativeReplayForest_pre m steps oldPost writes
  have hheads : headSends (TrieNative.heads m steps oldPost writes keys) B_PARENT =
      forestRoots 0 0 (TrieNative.forest m steps) := by
    rw [Link3.headS]
    unfold TrieNative.heads assignHeadUses
    rw [List.map_map]
    have := forestWalkHeads_parent 0 0 ((nativeReplayForest m steps oldPost writes).map (fun r => (r.pre, r.post)))
      (by
        intro p hp
        obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hp
        apply hn
        rw [TrieNative.forest, ← hpre]
        exact List.mem_map.mpr ⟨r, hr, rfl⟩)
    rw [List.map_map] at this
    simp only [Function.comp_def] at this ⊢
    rw [this]
    show forestRoots 0 0 ((nativeReplayForest m steps oldPost writes).map ReplayTree.pre) = _
    rw [hpre]; rfl
  have hp : (nodeSends3 (TrieNative.nodes m steps oldPost writes q) B_PARENT ++
      headSends (TrieNative.heads m steps oldPost writes keys) B_PARENT).Perm
      (nodeRecvs3 (TrieNative.nodes m steps oldPost writes q) B_PARENT) := by
    rw [nodeSends_parent, nodeRecvs_parent, hheads]
    unfold TrieNative.nodes TrieNative.seedNodes
    rw [recvFrom_assignList, recvFrom_records, recvFrom_assign, recvFrom_initialize,
      pS_assignList, pS_records, pS_assign, pS_initialize]
    exact (List.perm_append_comm.trans (forestNodes_parent 0 0 0 _ hw).symm)
  unfold Link3.cnt3
  exact (hp.map _).count_eq msg

theorem get_isNode : ∀ (t : PTrie) (key : List Nat) {x : Bytes}, t.get key = some x → isNode t = true
  | .hash _, _, _, h => by simp [PTrie.get] at h
  | .leaf .., _, _, _ => rfl
  | .ext .., _, _, _ => rfl
  | .branch .., _, _, _ => rfl

theorem sized_isNode {t : PTrie} {ws : List (List Nat × Bytes)} {out : PTrie}
    (h : SizedAccountRun t ws out) (ho : isNode out = true) : isNode t = true := by
  induction h with
  | nil => exact ho
  | cons hread _ _ _ _ ih => exact get_isNode _ _ hread

/-- Every pre tree of an accepted witness is a revealed node: its scheduler upsert succeeds. -/
theorem accepted_forest_isNode {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    (hk : walkD0 cb = .ok k) (hw : decodeW wb = .ok w) (h : checkD0a B0 cb wb = .ok ())
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes} (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last) :
    ∀ t ∈ TrieNative.forest m steps, isNode t = true := by
  obtain ⟨writes, oldPost, us, -, hr, hus, -, -, hval, -⟩ :=
    accepted_rebased_origin_instances hk hw h hm hv (fun _ => default) (fun _ _ => default)
  have hupre : ∀ u ∈ us, isNode u.pre = true := by
    intro u hu
    have := (hval u hu).1.1
    cases hp : u.pre with
    | hash _ => rw [hp] at this; simp [traceUpsert] at this
    | _ => rfl
  have hpres : us.map SchedulerUpsertWitness.pre = oldPost :: steps.map ImplicitStepV3.pre := by
    have := congrArg (List.map Prod.fst) hus
    simpa [List.map_map, Function.comp_def] using this
  have hmem : ∀ t ∈ oldPost :: steps.map ImplicitStepV3.pre, isNode t = true := by
    rw [← hpres]
    intro t ht
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
    exact hupre u hu
  intro t ht
  rcases List.mem_cons.mp ht with rfl | ht
  · exact sized_isNode hr (hmem oldPost (by simp))
  · exact hmem t (List.mem_cons_of_mem _ ht)

end ZkFormal.NearV3.Assembly.TrieParent

namespace ZkFormal.NearV3.Assembly.TrieParent

open NearSpec NearSpecV3 ZkFormal.Near ZkFormal.NearV3 ZkFormal.NearV3.Assembly Render Render.UpsGen
  Rcpt.Candidates Rcpt.Candidates.NodePostUpdate ZkFormal.NearV3.Candidates

/-- **`PARENT` balance from acceptance** (any `oldPost`, `writes`, `q`, `keys`). -/
theorem parentBal_accepted {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    (hk : walkD0 cb = .ok k) (hw : decodeW wb = .ok w) (h : checkD0a B0 cb wb = .ok ())
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes} (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    (oldPost : PTrie) (writes : List (List Nat × Bytes)) (q : UseRequests) (keys : List ZkFormal.Near.Msg) :
    Link3.ParentBal (TrieNative.nodes m steps oldPost writes q) (TrieNative.heads m steps oldPost writes keys) := by
  have hwf : ∀ t ∈ TrieNative.forest m steps, t.wf = true := by
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · rw [hm.pre]; exact (built_spec _ trieFuel _ _ hm.root_length).2.1
    · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
      exact (hv.input_facts s hs).2.2
  exact parentBal_native m steps oldPost writes q keys hwf (accepted_forest_isNode hk hw h hm hv)

end ZkFormal.NearV3.Assembly.TrieParent

namespace ZkFormal.NearV3.Assembly

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.NearV3.Render

theorem covers_parent_send : Covers B_PARENT true (fun t => t == 2 || t == 3) = true := by decide +kernel
theorem covers_parent_recv : Covers B_PARENT false (fun t => t == 2) = true := by decide +kernel
theorem pub_parent (s : Bool) (pub m : List Fp) : pubCount nearAirV3 pub B_PARENT s m = 0 :=
  pub_off _ _ (by cases s <;> decide +kernel) pub m

namespace RenderBundleV3

variable {pub : List Fp} (R : RenderBundleV3 pub)

/-- **`PARENT` balance of a bundle** from the record-level `ParentBal` of its node and head
components. -/
theorem balancedAt_parent (vs : List NodeS3) (hs : List HeadE)
    (hn : ExtOf (R ⟨T_NODE, by decide⟩).tf (nodeTraffic3 vs)) (hh : (R ⟨T_HEAD, by decide⟩).tf = headTraffic hs)
    (hbal : Link3.ParentBal vs hs) : R.BalancedAt B_PARENT := by
  intro m
  rw [R.sum_tables true _ m _ covers_parent_send, R.sum_tables false _ m _ covers_parent_recv,
    pub_parent, pub_parent]
  have e2 := R.tf_ext 2 (by decide) hn B_PARENT (by decide) (by decide) (by decide)
  have e3 : R.tf 3 = headTraffic hs := by rw [← hh]; rfl
  have hf2 : (List.range 25).filter (fun t => t == 2 || t == 3) = [2, 3] := by decide
  have hf1 : (List.range 25).filter (fun t => t == 2) = [2] := by decide
  rw [hf2, hf1]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, e2.1, e2.2, e3, sel,
    ite_true, Bool.false_eq_true, ite_false, cnt, nodeTraffic3, headTraffic]
  have := hbal m
  simp only [Link3.cnt3, List.map_append, List.count_append] at this
  omega

end RenderBundleV3

end ZkFormal.NearV3.Assembly
