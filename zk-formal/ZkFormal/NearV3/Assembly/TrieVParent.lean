import ZkFormal.NearV3.Assembly.TrieNative
import ZkFormal.NearV3.Assembly.TrieBusBalance
import ZkFormal.NearV3.Link.Vals3

/-!
# ZkFormal.NearV3.Assembly.TrieVParent — `VPARENT` balance of the honest trie entries

Node records send `VPARENT (vid, len)` for their value window, value records receive
`VPARENT (vid, len)`.  For the seeded forest the node windows list, in DFS order, exactly the
values of `seedValuesFrom 0 (forestBytes ts)` (`forestNodes_vpar`); the metadata passes
(`initializeList`, `ChainMetadata.assign`, `records u`, `assignList q`, `assignValues`) keep
the value ids and lengths.  Hence `vparentBal_native`: `Link3.VParentBal` for the honest
`nodes … q` and `vals …` of `TrieNative`, for every `u`/`q`, and `balancedAt_vparent` at
the bundle level.  No hypothesis beyond the components' traffic.
-/

namespace ZkFormal.NearV3.Assembly.TrieVParent

open NearSpec NearSpecV3 ZkFormal.Near ZkFormal.NearV3 ZkFormal.NearV3.Assembly Render Render.UpsGen
  Rcpt.Candidates Rcpt.Candidates.NodePostUpdate ZkFormal.NearV3.Candidates

/-- The `VPARENT` message of a node record, if any. -/
def vparOpt (s : NodeS3) : Option ZkFormal.Near.Msg := s.v.value.map fun x => [x.1, x.2.1]

/-- The `VPARENT` message of a value record. -/
def vmsg (e : ValE) : ZkFormal.Near.Msg := [e.vid, e.len]

theorem seedValuesFrom_append' (vid : Nat) (a b : List Bytes) :
    seedValuesFrom vid (a ++ b) = seedValuesFrom vid a ++ seedValuesFrom (vid + a.length) b :=
  seedValuesFrom_append vid a b

mutual
theorem seedNodesT_vpar (tau : Nat) : ∀ d n v t,
    (seedNodesT tau d n v t).filterMap vparOpt = (seedValuesFrom v (valsOf t)).map vmsg
  | _, _, v, .hash _ => by simp [seedNodesT, valsOf, occs, seedValuesFrom]
  | d, n, v, .leaf k s m => by
    cases s <;> simp [seedNodesT, List.filterMap_cons, vparOpt, seedNodeView, viewNode, viewSlot,
      NodeV3.value, valsOf_leaf, slotVal, seedValuesFrom, seedValue, vmsg]
  | d, n, v, .ext k c m => by
    simp [seedNodesT, List.filterMap_cons, vparOpt, seedNodeView, viewNode, NodeV3.value, valsOf_ext]
    exact seedNodesT_vpar tau (d+1) (n+1) v c
  | d, n, v, .branch sv cs m => by
    have ih := seedKidsT_vpar tau (d+1) (n+1) (v+(optSlotVal sv).length) cs
    cases sv with
    | none =>
      simpa [seedNodesT, List.filterMap_cons, vparOpt, seedNodeView, viewNode, NodeV3.value, valsOf_branch,
        optSlotVal] using ih
    | some s =>
      cases s with
      | val value =>
        simp [seedNodesT, List.filterMap_cons, vparOpt, seedNodeView, viewNode, viewSlot, NodeV3.value,
          valsOf_branch, optSlotVal, slotVal, seedValuesFrom, seedValue, vmsg] at ih ⊢
        simpa [vparOpt, Nat.add_comm] using ih
      | ref l h =>
        simpa [seedNodesT, List.filterMap_cons, vparOpt, seedNodeView, viewNode, viewSlot, NodeV3.value,
          valsOf_branch, optSlotVal, slotVal] using ih
theorem seedKidsT_vpar (tau : Nat) : ∀ d n v cs,
    (seedKidsT tau d n v cs).filterMap vparOpt = (seedValuesFrom v (kvals cs)).map vmsg
  | _, _, v, .nil => by simp [seedKidsT, kvals_nil, seedValuesFrom]
  | d, n, v, .none rest => by simpa [seedKidsT, kvals_none] using seedKidsT_vpar tau d n v rest
  | d, n, v, .some c rest => by
    simp only [seedKidsT, List.filterMap_append, kvals_some, seedValuesFrom_append', List.map_append,
      seedNodesT_vpar tau d n v c, seedKidsT_vpar tau d (n+tsize c) (v+(valsOf c).length) rest]
end

theorem forestNodes_vpar : ∀ tau nid vid ts,
    (forestNodes tau nid vid ts).filterMap vparOpt = (seedValuesFrom vid (forestBytes ts)).map vmsg
  | _, _, _, [] => by simp [forestNodes, forestBytes, seedValuesFrom]
  | tau, nid, vid, t :: ts => by
    simp only [forestNodes, List.filterMap_append, seedNodesT_vpar, forestNodes_vpar, forestBytes,
      List.flatMap_cons, seedValuesFrom_append', List.map_append]

/-! ## The metadata passes keep the value windows -/

theorem vparOpt_record (u : Inputs) (s : NodeS3) : vparOpt (record u s) = vparOpt s := by
  rcases s with ⟨v, tau, depth, res, uses, ubm, dup, hd, repE, ucid, mU⟩
  simp only [vparOpt, record]
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

theorem initializeList_vpar : ∀ (n : Nat) (ss : List NodeS3),
    (initializeList n ss).filterMap vparOpt = ss.filterMap vparOpt
  | _, [] => rfl
  | n, s :: ss => by
    simp only [initializeList, List.filterMap_cons, initializeList_vpar (n+1) ss]
    rfl

theorem assign_vpar (rs : List StoreDuplicateChain.Entry) : ∀ (n : Nat) (ss : List NodeS3),
    (ChainMetadata.assign rs n ss).filterMap vparOpt = ss.filterMap vparOpt
  | _, [] => rfl
  | n, s :: ss => by
    simp only [ChainMetadata.assign, List.filterMap_cons, assign_vpar rs (n+1) ss]
    rfl

theorem records_vpar (u : Inputs) (ss : List NodeS3) :
    (records u ss).filterMap vparOpt = ss.filterMap vparOpt := by
  unfold records
  rw [List.filterMap_map]
  congr 1
  funext s
  exact vparOpt_record u s

theorem assignList_vpar (q : UseRequests) : ∀ (n : Nat) (ss : List NodeS3),
    (assignList q n ss).filterMap vparOpt = ss.filterMap vparOpt
  | _, [] => rfl
  | n, s :: ss => by
    simp only [assignList, List.filterMap_cons, assignList_vpar q (n+1) ss]
    rfl

theorem assignValues_vmsg (rs : List StoreDuplicateChain.Entry) (es : List ValE) :
    (ChainMetadata.assignValues rs es).map vmsg = es.map vmsg := by
  simp [ChainMetadata.assignValues, ChainMetadata.patchValue, vmsg]

/-! ## The balance -/

theorem nodeSends_vparent (vs : List NodeS3) : nodeSends3 vs B_VPARENT = vs.filterMap vparOpt := by
  rw [Link3.vparentS]
  have : ∀ (l : List NodeS3) (k : Nat), (l.zip (List.range' k l.length)).flatMap (fun x => Link3.vparMsg x.1) =
      l.filterMap vparOpt := by
    intro l
    induction l with
    | nil => intro k; rfl
    | cons a l ih =>
      intro k
      simp only [List.length_cons, List.range'_succ, List.zip_cons_cons, List.flatMap_cons, ih,
        List.filterMap_cons]
      unfold Link3.vparMsg vparOpt
      rcases a.v.value with _ | ⟨i, l', pre, po, w⟩ <;> rfl
  rw [List.range_eq_range']
  exact this vs 0

/-- **`VPARENT` balance of the honest node and value records** (any `oldPost`, `writes`, `q`). -/
theorem vparentBal_native (m : MainExecutionV3) (steps : List ImplicitStepV3) (oldPost : PTrie)
    (writes : List (List Nat × Bytes)) (q : UseRequests) :
    Link3.VParentBal (TrieNative.nodes m steps oldPost writes q) (TrieNative.vals m steps) := by
  intro msg
  have h : nodeSends3 (TrieNative.nodes m steps oldPost writes q) B_VPARENT =
      valRecvs (TrieNative.vals m steps) B_VPARENT := by
    rw [nodeSends_vparent, Link3.vparentR]
    unfold TrieNative.nodes TrieNative.vals TrieNative.seedNodes TrieNative.seedVals
    rw [assignList_vpar, records_vpar, assign_vpar, initializeList_vpar, forestNodes_vpar]
    exact (assignValues_vmsg _ _).symm
  rw [h]

end ZkFormal.NearV3.Assembly.TrieVParent

namespace ZkFormal.NearV3.Assembly

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.NearV3.Render

theorem covers_vparent_send : Covers B_VPARENT true (fun t => t == 2) = true := by decide +kernel
theorem covers_vparent_recv : Covers B_VPARENT false (fun t => t == 4) = true := by decide +kernel
theorem pub_vparent (s : Bool) (pub m : List Fp) : pubCount nearAirV3 pub B_VPARENT s m = 0 :=
  pub_off _ _ (by cases s <;> decide +kernel) pub m

namespace RenderBundleV3

variable {pub : List Fp} (R : RenderBundleV3 pub)

/-- **`VPARENT` balance of a bundle** from the record-level `VParentBal` of its node and value
components. -/
theorem balancedAt_vparent (vs : List NodeS3) (es : List ValE)
    (hn : (R ⟨T_NODE, by decide⟩).tf = nodeTraffic3 vs) (hv : (R ⟨T_VAL, by decide⟩).tf = valTraffic es)
    (hbal : Link3.VParentBal vs es) : R.BalancedAt B_VPARENT := by
  intro m
  rw [R.sum_tables true _ m _ covers_vparent_send, R.sum_tables false _ m _ covers_vparent_recv,
    pub_vparent, pub_vparent]
  have e2 : R.tf 2 = nodeTraffic3 vs := by rw [← hn]; rfl
  have e4 : R.tf 4 = valTraffic es := by rw [← hv]; rfl
  have hf2 : (List.range 25).filter (fun t => t == 2) = [2] := by decide
  have hf4 : (List.range 25).filter (fun t => t == 4) = [4] := by decide
  rw [hf2, hf4]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, e2, e4, sel,
    ite_true, Bool.false_eq_true, ite_false, cnt, nodeTraffic3, valTraffic]
  have := hbal m
  simp only [Link3.cnt3] at this
  omega

end RenderBundleV3

end ZkFormal.NearV3.Assembly
