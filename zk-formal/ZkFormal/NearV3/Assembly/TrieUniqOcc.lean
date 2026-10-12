import ZkFormal.NearV3.Assembly.TrieEnt

/-!
# ZkFormal.NearV3.Assembly.TrieUniqOcc — the `DIGS` windows are the store occurrences

The `uniq` entries the honest node and head tables feed (`UniqNative.rawEnts`: one per
`DIGS` window) are, as a multiset, one entry per store occurrence of the pre forest
(`occEnt`: the occurrence id, its instance, the SHA-256 of its content):

* nodes (`forestNodes_nodeEnts`): a record's entry is sent by its parent's kid window
  (`viewKid`: the child's `hashOf` = SHA-256 of its encoding), a tree root's by its head;
* values (`forestNodes_valEnts`, `valueOccurrences_ents`): a value's entry is sent by its
  slot window (`viewSlot`), at the instance of its tree (`valueTau`).

`rawEnts_perm_occ`: `rawEnts (nodes … q) (heads … keys) ~ (allOccurrences …).map occEnt`
for revealed, well-formed pre trees.
-/

namespace ZkFormal.NearV3.Assembly.TrieUniqOcc

open NearSpec NearSpecV3 ZkFormal.Near ZkFormal.NearV3 ZkFormal.NearV3.Assembly Render Render.UpsGen
  Rcpt.Candidates Rcpt.Candidates.NodePostUpdate ZkFormal.NearV3.Candidates
  StoreDuplicateMetadata HonestStoreRepresentatives TrieParent

/-- The `uniq` entry of a store occurrence. -/
def occEnt (o : Occurrence) : UEnt := ⟨o.eid, o.key.1, (sha256 o.key.2).map UInt8.toNat⟩

theorem toBytes_toNat (b : Bytes) : toBytes (b.map UInt8.toNat) = b := by
  simp [toBytes, List.map_map, Function.comp_def]

/-! ## Node windows -/

/-- Kid-window entries of a record. -/
def kidEnts (s : NodeS3) : List UEnt :=
  s.v.revealed.map fun (c, _, _, pre, _) => (⟨msgId K_NPRE c, s.tau, pre⟩ : UEnt)

/-- Value-window entries of a record. -/
def valWinEnts (s : NodeS3) : List UEnt :=
  match s.v.value with
  | some (i, _, pre, _, _) => [⟨msgId K_VPRE i, s.tau, pre⟩]
  | none => []

theorem entsOf_split (s : NodeS3) : UniqNative.entsOf s = kidEnts s ++ valWinEnts s := rfl

/-- The occurrence entry of record `i`. -/
def recEnt (s : NodeS3) (i : Nat) : UEnt := ⟨eidN i, s.tau, (sha256 (toBytes (s.v.ser false))).map UInt8.toNat⟩

def entFrom : Nat → List NodeS3 → List UEnt
  | _, [] => []
  | n, s :: ss => recEnt s n :: entFrom (n + 1) ss

theorem entFrom_append : ∀ (n : Nat) (a b : List NodeS3),
    entFrom n (a ++ b) = entFrom n a ++ entFrom (n + a.length) b
  | _, [], b => by simp [entFrom]
  | n, s :: a, b => by
    simp only [List.cons_append, entFrom, entFrom_append (n + 1) a b, List.length_cons]
    rw [show n + 1 + a.length = n + (a.length + 1) by omega]

def rootE (tau n : Nat) (t : PTrie) : List UEnt :=
  if isNode t then [⟨eidN n, tau, t.hashOf.map UInt8.toNat⟩] else []

def kidRoots (tau : Nat) : Nat → Kids → List UEnt
  | _, .nil => []
  | n, .none r => kidRoots tau n r
  | n, .some c r => rootE tau n c ++ kidRoots tau (n + tsize c) r

def revEnts (tau : Nat) (ks : List NKid) : List UEnt :=
  (ks.filterMap fun
      | .node c l r pre po => some (c, l, r, pre, po)
      | _ => none).map fun (c, _, _, pre, _) => (⟨msgId K_NPRE c, tau, pre⟩ : UEnt)

theorem viewKids_ents (tau : Nat) : ∀ n cs, revEnts tau (viewKids n cs) = kidRoots tau n cs
  | _, .nil => rfl
  | n, .none r => by
    simp only [viewKids, revEnts, List.filterMap_cons, kidRoots] at *
    exact viewKids_ents tau n r
  | n, .some c r => by
    have ih := viewKids_ents tau (n + tsize c) r
    simp only [revEnts] at ih
    simp only [viewKids, revEnts, List.filterMap_cons, kidRoots, rootE, viewKid]
    by_cases hc : isNode c = true
    · simp [hc, ih, eidN]
    · simp [hc, ih]

theorem seedNodeView_recEnt (tau d n v : Nat) (t : PTrie) (hw : t.wf = true) (hn : isNode t = true) :
    recEnt (seedNodeView tau d n v t) n = ⟨eidN n, tau, t.hashOf.map UInt8.toNat⟩ := by
  simp only [recEnt, seedNodeView, viewNode_ser n v t hw hn false, toBytes_toNat,
    ← hashOf_eq_enc t hn]

mutual
theorem seedNodesT_ents (tau : Nat) : ∀ d n v t, t.wf = true →
    (entFrom n (seedNodesT tau d n v t)).Perm (rootE tau n t ++ (seedNodesT tau d n v t).flatMap kidEnts)
  | _, _, _, .hash _, _ => by simp [seedNodesT, entFrom, rootE, isNode]
  | d, n, v, .leaf k s m, hw => by
    simp only [seedNodesT, entFrom, rootE, isNode, ite_true, List.flatMap_cons, List.flatMap_nil,
      seedNodeView_recEnt tau d n v _ hw rfl]
    simp [kidEnts, seedNodeView, viewNode, NodeV3.revealed]
  | d, n, v, .ext k c m, hw => by
    have hc : c.wf = true := by
      simp only [PTrie.wf, Bool.and_eq_true] at hw
      exact hw.1.1.2
    have ih := seedNodesT_ents tau (d+1) (n+1) v c hc
    simp only [seedNodesT, entFrom, rootE, isNode, ite_true, List.flatMap_cons,
      seedNodeView_recEnt tau d n v _ hw rfl, List.singleton_append]
    apply List.Perm.cons
    have hs : kidEnts (seedNodeView tau d n v (.ext k c m)) = rootE tau (n+1) c := by
      simp only [kidEnts, seedNodeView, viewNode, viewKid, rootE]
      by_cases hn : isNode c = true
      · simp [hn, NodeV3.revealed, eidN]
      · simp [hn, NodeV3.revealed]
    rw [hs]
    exact ih
  | d, n, v, .branch sv cs m, hw => by
    have hk : Kids.wf cs 16 = true := by
      simp only [PTrie.wf, Bool.and_eq_true] at hw
      exact hw.1.2
    have ih := seedKidsT_ents tau (d+1) (n+1) (v+(optSlotVal sv).length) cs 16 hk
    simp only [seedNodesT, entFrom, rootE, isNode, ite_true, List.flatMap_cons,
      seedNodeView_recEnt tau d n v _ hw rfl, List.singleton_append]
    apply List.Perm.cons
    have hs : kidEnts (seedNodeView tau d n v (.branch sv cs m)) = kidRoots tau (n+1) cs := by
      rw [← viewKids_ents]
      simp only [kidEnts, seedNodeView, viewNode, NodeV3.revealed, revEnts]
      rfl
    rw [hs]
    exact ih
theorem seedKidsT_ents (tau : Nat) : ∀ d n v cs k, Kids.wf cs k = true →
    (entFrom n (seedKidsT tau d n v cs)).Perm (kidRoots tau n cs ++ (seedKidsT tau d n v cs).flatMap kidEnts)
  | _, _, _, .nil, _, _ => by simp [seedKidsT, entFrom, kidRoots]
  | d, n, v, .none rest, k, hw => by
    have hr : Kids.wf rest (k - 1) = true := by
      simp only [Kids.wf, Bool.and_eq_true] at hw
      exact hw.2
    simpa [seedKidsT, kidRoots] using seedKidsT_ents tau d n v rest (k - 1) hr
  | d, n, v, .some c rest, k, hw => by
    have h2 : c.wf = true ∧ Kids.wf rest (k - 1) = true := by
      simp only [Kids.wf, Bool.and_eq_true] at hw
      exact ⟨hw.1.2, hw.2⟩
    have ihc := seedNodesT_ents tau d n v c h2.1
    have ihr := seedKidsT_ents tau d (n + tsize c) (v + (valsOf c).length) rest (k - 1) h2.2
    simp only [seedKidsT, entFrom_append, seedNodesT_length', kidRoots, List.flatMap_append]
    refine (ihc.append ihr).trans ?_
    simp only [List.append_assoc]
    apply List.Perm.append_left
    exact List.perm_append_comm_assoc _ _ _
end

def forestRootEnts : Nat → Nat → List PTrie → List UEnt
  | _, _, [] => []
  | tau, n, t :: ts => rootE tau n t ++ forestRootEnts (tau + 1) (n + tsize t) ts

theorem forestNodes_ents : ∀ tau nid vid ts, (∀ t ∈ ts, t.wf = true) →
    (entFrom nid (forestNodes tau nid vid ts)).Perm
      (forestRootEnts tau nid ts ++ (forestNodes tau nid vid ts).flatMap kidEnts)
  | _, _, _, [], _ => by simp [forestNodes, entFrom, forestRootEnts]
  | tau, nid, vid, t :: ts, hw => by
    have iht := seedNodesT_ents tau 0 nid vid t (hw t (by simp))
    have ihr := forestNodes_ents (tau + 1) (nid + tsize t) (vid + (valsOf t).length) ts
      (fun t' h => hw t' (by simp [h]))
    simp only [forestNodes, entFrom_append, seedNodesT_length', forestRootEnts, List.flatMap_append]
    refine (iht.append ihr).trans ?_
    simp only [List.append_assoc]
    apply List.Perm.append_left
    exact List.perm_append_comm_assoc _ _ _

theorem forestWalkHeads_ents : ∀ tau n (pairs : List (PTrie × PTrie)),
    (∀ p ∈ pairs, isNode p.1 = true) →
    (forestWalkHeads tau n pairs).map UniqNative.entH = forestRootEnts tau n (pairs.map Prod.fst)
  | _, _, [], _ => rfl
  | tau, n, (pre, post) :: rest, hn => by
    have h1 : isNode pre = true := hn (pre, post) (by simp)
    simp only [forestWalkHeads, List.map_cons, forestRootEnts, rootE, h1, ite_true,
      List.singleton_append, UniqNative.entH, eidN,
      forestWalkHeads_ents (tau + 1) (n + tsize pre) rest (fun p hp => hn p (by simp [hp]))]

/-! ## Value windows -/

def vEnt (tau : Nat) (e : ValE) : UEnt := ⟨eidV e, tau, (sha256 (toBytes e.bytes)).map UInt8.toNat⟩

mutual
theorem seedNodesT_valEnts (tau : Nat) : ∀ d n v t,
    (seedNodesT tau d n v t).flatMap valWinEnts = (seedValuesFrom v (valsOf t)).map (vEnt tau)
  | _, _, v, .hash _ => by simp [seedNodesT, valsOf, occs, seedValuesFrom]
  | d, n, v, .leaf k s m => by
    cases s <;> simp [seedNodesT, valWinEnts, seedNodeView, viewNode, viewSlot,
      NodeV3.value, valsOf_leaf, slotVal, seedValuesFrom, seedValue, vEnt, eidV, toBytes_toNat]
  | d, n, v, .ext k c m => by
    simp [seedNodesT, valWinEnts, seedNodeView, viewNode, NodeV3.value, valsOf_ext]
    exact seedNodesT_valEnts tau (d+1) (n+1) v c
  | d, n, v, .branch sv cs m => by
    have ih := seedKidsT_valEnts tau (d+1) (n+1) (v+(optSlotVal sv).length) cs
    cases sv with
    | none =>
      simpa [seedNodesT, valWinEnts, seedNodeView, viewNode, NodeV3.value, valsOf_branch,
        optSlotVal] using ih
    | some s =>
      cases s with
      | val value =>
        simp [seedNodesT, valWinEnts, seedNodeView, viewNode, viewSlot, NodeV3.value,
          valsOf_branch, optSlotVal, slotVal, seedValuesFrom, seedValue, vEnt, eidV, toBytes_toNat] at ih ⊢
        simpa [Nat.add_comm] using ih
      | ref l h =>
        simpa [seedNodesT, valWinEnts, seedNodeView, viewNode, viewSlot, NodeV3.value,
          valsOf_branch, optSlotVal, slotVal] using ih
theorem seedKidsT_valEnts (tau : Nat) : ∀ d n v cs,
    (seedKidsT tau d n v cs).flatMap valWinEnts = (seedValuesFrom v (kvals cs)).map (vEnt tau)
  | _, _, v, .nil => by simp [seedKidsT, kvals_nil, seedValuesFrom]
  | d, n, v, .none rest => by simpa [seedKidsT, kvals_none] using seedKidsT_valEnts tau d n v rest
  | d, n, v, .some c rest => by
    simp only [seedKidsT, List.flatMap_append, kvals_some, TrieVParent.seedValuesFrom_append',
      List.map_append, seedNodesT_valEnts tau d n v c,
      seedKidsT_valEnts tau d (n+tsize c) (v+(valsOf c).length) rest]
end

def valEntsF : Nat → Nat → List PTrie → List UEnt
  | _, _, [] => []
  | tau, vid, t :: ts => (seedValuesFrom vid (valsOf t)).map (vEnt tau) ++
      valEntsF (tau + 1) (vid + (valsOf t).length) ts

theorem forestNodes_valEnts : ∀ tau nid vid ts,
    (forestNodes tau nid vid ts).flatMap valWinEnts = valEntsF tau vid ts
  | _, _, _, [] => by simp [forestNodes, valEntsF]
  | tau, nid, vid, t :: ts => by
    simp only [forestNodes, List.flatMap_append, seedNodesT_valEnts, forestNodes_valEnts, valEntsF]

theorem valTau_ents : ∀ tau nid vid ts,
    (seedValuesFrom vid (forestBytes ts)).map
        (fun e => vEnt (Link3.valTau (forestNodes tau nid vid ts) e.vid) e) = valEntsF tau vid ts
  | _, _, _, [] => by simp [forestBytes, seedValuesFrom, valEntsF]
  | tau, nid, vid, t :: ts => by
    let a := seedNodesT tau 0 nid vid t
    let b := forestNodes (tau+1) (nid+tsize t) (vid+(valsOf t).length) ts
    have hvid : ∀ (w : Nat) (bs : List Bytes) (e : ValE), e ∈ seedValuesFrom w bs → e.vid ∈ List.range' w bs.length := by
      intro w bs e he
      rw [← seedValuesFrom_vids]
      exact List.mem_map.mpr ⟨e, he, rfl⟩
    change (seedValuesFrom vid (valsOf t ++ forestBytes ts)).map _ = _
    rw [TrieVParent.seedValuesFrom_append', List.map_append, valEntsF]
    have hb : forestNodes tau nid vid (t :: ts) = a ++ b := rfl
    rw [hb]
    congr 1
    · apply List.map_congr_left
      intro e he
      have hi := hvid _ _ e he
      rw [valTau_append_left a b e.vid (by simpa only [a, seedNodesT_valueIds] using hi),
        seedNodesT_valTau tau 0 nid vid t e.vid hi]
    · rw [← valTau_ents (tau+1) (nid+tsize t) (vid+(valsOf t).length) ts]
      apply List.map_congr_left
      intro e he
      have hi := hvid _ _ e he
      rw [valTau_append_right a b e.vid (by
        intro hbad
        simp only [a, seedNodesT_valueIds, List.mem_range'] at hbad
        simp only [List.mem_range'] at hi
        omega)]

theorem valueOccurrences_ents (ts : List PTrie) :
    (CombinedStoreOccurrences.valueOccurrences (NativeStoreProvenance.valueTau ts)
      (seedValuesFrom 0 (forestBytes ts))).map occEnt = valEntsF 0 0 ts := by
  rw [← valTau_ents 0 0 0 ts]
  simp only [CombinedStoreOccurrences.valueOccurrences, List.map_map]
  rfl

end ZkFormal.NearV3.Assembly.TrieUniqOcc

namespace ZkFormal.NearV3.Assembly.TrieUniqOcc

open NearSpec NearSpecV3 ZkFormal.Near ZkFormal.NearV3 ZkFormal.NearV3.Assembly Render Render.UpsGen
  Rcpt.Candidates Rcpt.Candidates.NodePostUpdate ZkFormal.NearV3.Candidates
  StoreDuplicateMetadata HonestStoreRepresentatives TrieParent

theorem flatMap_append_perm {α β : Type} (l : List α) (f g : α → List β) :
    (l.flatMap fun x => f x ++ g x).Perm (l.flatMap f ++ l.flatMap g) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons, List.append_assoc]
    apply List.Perm.append_left
    refine (ih.append_left (g a)).trans ?_
    simp only [← List.append_assoc]
    exact List.Perm.append_right _ List.perm_append_comm

theorem kidEnts_record (u : Inputs) (s : NodeS3) : kidEnts (record u s) = kidEnts s := by
  rcases s with ⟨v, tau, depth, res, uses, ubm, dup, hd, repE, ucid, mU⟩
  simp only [kidEnts, record]
  cases v with
  | leaf k sl m => rfl
  | ext k c m => cases c <;> rfl
  | branch sv cs m =>
    simp only [node, NodeV3.revealed]
    induction cs with
    | nil => rfl
    | cons c cs ih => cases c <;> simp_all [kid]

theorem valWinEnts_record (u : Inputs) (s : NodeS3) : valWinEnts (record u s) = valWinEnts s := by
  rcases s with ⟨v, tau, depth, res, uses, ubm, dup, hd, repE, ucid, mU⟩
  simp only [valWinEnts, record]
  cases v with
  | leaf k sl m =>
    cases sl with
    | ref l h => rfl
    | val lb i l pre po w => simp only [node, slot]; cases u.value i <;> rfl
  | ext k c m => rfl
  | branch sv cs m =>
    cases sv with
    | none => rfl
    | some sl =>
      cases sl with
      | ref l h => rfl
      | val lb i l pre po w => simp only [node, slot, Option.map]; cases u.value i <;> rfl

/-- The record transformations keep a per-record window function of `v` and `tau`. -/
theorem nodes_flatMap (f : NodeS3 → List UEnt) (hf : ∀ u s, f (record u s) = f s)
    (hv : ∀ s s' : NodeS3, s.v = s'.v → s.tau = s'.tau → f s = f s')
    (m : MainExecutionV3) (steps : List ImplicitStepV3) (oldPost : PTrie)
    (writes : List (List Nat × Bytes)) (q : UseRequests) :
    (TrieNative.nodes m steps oldPost writes q).flatMap f =
      (forestNodes 0 0 0 (TrieNative.forest m steps)).flatMap f := by
  unfold TrieNative.nodes TrieNative.seedNodes
  generalize forestNodes 0 0 0 (TrieNative.forest m steps) = ss
  generalize forestOldInputs (nativeReplayForest m steps oldPost writes) = u
  generalize TrieNative.chain m steps = cs
  suffices h : ∀ n (ss : List NodeS3),
      (assignList q n (records u (ChainMetadata.assign cs n (initializeList n ss)))).flatMap f = ss.flatMap f from
    h 0 ss
  intro n ss
  induction ss generalizing n with
  | nil => rfl
  | cons s ss ih =>
    simp only [initializeList, ChainMetadata.assign, records, List.map_cons, assignList, List.flatMap_cons]
    have h1 := ih (n + 1)
    simp only [records] at h1
    rw [h1]
    congr 1
    rw [hv (assignUses q n (record u (ChainMetadata.patch cs n (initializeMetadata n s))))
      (record u (ChainMetadata.patch cs n (initializeMetadata n s))) rfl rfl, hf]
    exact hv _ _ rfl rfl

theorem entFrom_zipIdx : ∀ (n : Nat) (ss : List NodeS3),
    entFrom n ss = (ss.zipIdx n).map fun p => recEnt p.1 p.2
  | _, [] => rfl
  | n, s :: ss => by simp only [entFrom, List.zipIdx_cons, List.map_cons, entFrom_zipIdx (n + 1) ss]

theorem entFrom_initialize : ∀ (n : Nat) (ss : List NodeS3), entFrom n (initializeList n ss) = entFrom n ss
  | _, [] => rfl
  | n, s :: ss => by simp only [initializeList, entFrom, entFrom_initialize (n + 1) ss]; rfl

theorem nodeOccurrences_ents (ss : List NodeS3) :
    (CombinedStoreOccurrences.nodeOccurrences ss).map occEnt = entFrom 0 ss := by
  rw [entFrom_zipIdx]
  simp only [CombinedStoreOccurrences.nodeOccurrences, List.map_map]
  rfl

/-- **The `DIGS` windows of the honest node and head entries are the store occurrences.** -/
theorem rawEnts_perm_occ (m : MainExecutionV3) (steps : List ImplicitStepV3) (oldPost : PTrie)
    (writes : List (List Nat × Bytes)) (q : UseRequests) (keys : List ZkFormal.Near.Msg)
    (hw : ∀ t ∈ TrieNative.forest m steps, t.wf = true)
    (hn : ∀ t ∈ TrieNative.forest m steps, isNode t = true) :
    (UniqNative.rawEnts (TrieNative.nodes m steps oldPost writes q) (TrieNative.heads m steps oldPost writes keys)).Perm
      ((CombinedStoreOccurrences.allOccurrences (TrieNative.seedNodes m steps)
        (NativeStoreProvenance.valueTau (TrieNative.forest m steps)) (TrieNative.seedVals m steps)).map occEnt) := by
  have hpre := nativeReplayForest_pre m steps oldPost writes
  have hheads : (TrieNative.heads m steps oldPost writes keys).map UniqNative.entH =
      forestRootEnts 0 0 (TrieNative.forest m steps) := by
    unfold TrieNative.heads assignHeadUses
    rw [List.map_map]
    have := forestWalkHeads_ents 0 0 ((nativeReplayForest m steps oldPost writes).map (fun r => (r.pre, r.post)))
      (by
        intro p hp
        obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hp
        apply hn
        rw [TrieNative.forest, ← hpre]
        exact List.mem_map.mpr ⟨r, hr, rfl⟩)
    rw [List.map_map] at this
    refine Eq.trans ?_ (this.trans ?_)
    · rfl
    · show forestRootEnts 0 0 ((nativeReplayForest m steps oldPost writes).map ReplayTree.pre) = _
      rw [hpre]; rfl
  have hk := nodes_flatMap kidEnts kidEnts_record (fun s s' h1 h2 => by simp only [kidEnts, h1, h2])
    m steps oldPost writes q
  have hvw := nodes_flatMap valWinEnts valWinEnts_record (fun s s' h1 h2 => by simp only [valWinEnts, h1, h2])
    m steps oldPost writes q
  have hsplit := flatMap_append_perm (TrieNative.nodes m steps oldPost writes q) kidEnts valWinEnts
  rw [hk, hvw, forestNodes_valEnts] at hsplit
  have hF := forestNodes_ents 0 0 0 (TrieNative.forest m steps) hw
  unfold UniqNative.rawEnts
  rw [hheads, CombinedStoreOccurrences.allOccurrences, List.map_append, nodeOccurrences_ents,
    TrieNative.seedNodes, entFrom_initialize]
  unfold TrieNative.seedVals
  rw [valueOccurrences_ents]
  -- rawEnts ~ (kid ++ val) ++ roots ~ (roots ++ kid) ++ val ~ entFrom ++ val
  refine ((hsplit.append_right _).trans ?_)
  refine (List.perm_append_comm.trans ?_)
  rw [← List.append_assoc]
  exact (hF.symm.append_right _)

end ZkFormal.NearV3.Assembly.TrieUniqOcc
