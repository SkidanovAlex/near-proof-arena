import ZkFormal.NearV3.Assembly.TrieComplete
import ZkFormal.NearV3.Rcpt.Candidates.SharedPhysicalEdgeBalance
import ZkFormal.NearV3.Rcpt.Candidates.NodeBitmapMessages
import ZkFormal.NearV3.Rcpt.Candidates.NativeProviderCoverage

/-!
# ZkFormal.NearV3.Assembly.TrieUps — `upsV3` component: honest-input condition, view, EDGE/BMAP

* `upsRenderOk_of_family` — `UpsRenderOk` of an instance list from the per-instance native facts
  (`InstOk`, `NativePartFamily`: what `checkD0a_exactNativeTrafficList` delivers for the
  accepted scheduler upserts) and the row cap `R + 1 ≤ 2^22`; `upsRenderOk_ranked` — the same
  for the counter-ranked list `physicalPrefixUps p Is` (only the walk counters change).
* `aligned_view_walk_messages` — the view of the aligned honest trace (any height
  `≥ R + 1`) carries, on `EDGE` and `BMAP`, exactly `upsWalkMessages Is` (the four `W` rows of
  every instance): the ups component's traffic on these buses is trace-free.  (Port of
  `physical_view_messages`, which required the unpadded height `logOf (R + 1)`.)
* `edge_records`, `bmap_records` — record-level `EDGE`/`BMAP` conservation of node providers,
  head providers (EDGE), ranked lookup walks and ranked ups walks sharing one counter sequence
  (`joint_actual_edges` + `BusEdge.chain_perm`);
* `balancedAt_edge`, `balancedAt_bmap` — bundle level (tables 2, 3, 5, 7 / 2, 5, 7).
-/

namespace ZkFormal.NearV3.Assembly.TrieUps

open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3 ZkFormal.NearV3.Assembly
  Render Render.UpsGen UpsRows Rcpt.Candidates Rcpt.Candidates.NodePostUpdate ZkFormal.Size

theorem upsRenderOk_of_family (Is : List UpsInst) (hpos : 0 < Is.length) (hinst : ∀ I ∈ Is, InstOk I)
    (hfam : ∀ I ∈ Is, NativePartFamily I) (hcap : R Is + 1 ≤ 2 ^ 22) : UpsRenderOk Is :=
  ⟨⟨hpos, hinst, hcap⟩, fun I hI k hk => (hfam I hI k hk).2.2.1, fun I hI k hk => (hfam I hI k hk).2.1,
    fun I hI k hk => (hfam I hI k hk).2.2.2.1, fun I hI k hk => (hfam I hI k hk).1,
    fun I hI k hk => (hfam I hI k hk).2.2.2.2.1⟩

theorem rankUps_recsI (p : List WStep3) (I : UpsInst) : recsI (rankUps p I) = recsI I := rfl
theorem syncUps_recsI (I : UpsInst) : recsI (syncUps I) = recsI I := rfl

theorem rankUpsList_recs : ∀ (p : List WStep3) (Is : List UpsInst),
    (rankUpsList p Is).map recsI = Is.map recsI
  | _, [] => rfl
  | p, I :: Is => by simp only [rankUpsList, List.map_cons, rankUps_recsI, rankUpsList_recs]

theorem R_eq_of_recs {Is Js : List UpsInst} (h : Is.map recsI = Js.map recsI) : R Is = R Js := by
  have hl : Is.length = Js.length := by simpa using congrArg List.length h
  have hi : ∀ i, recsI (inst Is i) = recsI (inst Js i) := by
    intro i
    by_cases hi : i < Is.length
    · have := congrArg (fun l => l.getD i []) h
      simp only [inst, List.getD_eq_getElem?_getD, List.getElem?_map] at this ⊢
      rw [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem (hl ▸ hi)] at this ⊢
      simpa using this
    · simp only [inst, List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hi),
        List.getElem?_eq_none (by omega : Js.length ≤ i)]
  rw [← start_len, ← start_len, hl]
  unfold start
  simp only [hi]

theorem ranked_recs (p : List WStep3) (Is : List UpsInst) :
    (physicalPrefixUps p Is).map recsI = Is.map recsI := by
  unfold physicalPrefixUps
  rw [List.map_map]
  simp only [Function.comp_def, syncUps_recsI]
  exact rankUpsList_recs p Is

theorem R_ranked (p : List WStep3) (Is : List UpsInst) : R (physicalPrefixUps p Is) = R Is :=
  R_eq_of_recs (ranked_recs p Is)

/-- **`UpsRenderOk` of the counter-ranked native instances.** -/
theorem upsRenderOk_ranked (p : List WStep3) (Is : List UpsInst) (hpos : 0 < Is.length)
    (hinst : ∀ I ∈ Is, InstOk I) (hfam : ∀ I ∈ Is, NativePartFamily I) (hcap : R Is + 1 ≤ 2 ^ 22) :
    UpsRenderOk (physicalPrefixUps p Is) :=
  upsRenderOk_of_family _ (by
      have := congrArg List.length (ranked_recs p Is)
      simp only [List.length_map] at this; omega)
    (physicalPrefixUps_instOk p Is hinst) (physicalPrefixUps_parts p Is hfam) (by rw [R_ranked]; exact hcap)

/-! ## The aligned view on the walk buses -/

private theorem flat_congr' {α β : Type} (xs : List α) (f g : α → List β)
    (h : ∀ x ∈ xs, f x = g x) : xs.flatMap f = xs.flatMap g := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons]; rw [h x (by simp), ih (fun y hy => h y (by simp [hy]))]

private theorem map_range_getD' {α : Type} (xs : List α) (d : α) :
    (List.range xs.length).map (fun i => xs.getD i d) = xs := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_map, List.getElem_range]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

theorem segment_rows_at (Is : List UpsInst) (tr : Trace Fp) (t : Nat) (hH : R Is + 1 ≤ tr.height t)
    (hcell : ∀ r x, r < tr.height t → x < 200 → tr.cell t r x = ((cell Is r x : Int) : Fp))
    (i : Nat) (hi : i < Is.length) (d : Nat) (hd : d < (recsI (inst Is i)).length)
    (bus : Nat) (hb : bus = B_EDGE ∨ bus = B_BMAP) (sd : Bool) :
    uMsgs ((segOf tr t (start Is i, (recsI (inst Is i)).length)).row d)
      ((segOf tr t (start Is i, (recsI (inst Is i)).length)).next d) bus sd =
    uMsgs (generatedRow Is (start Is i + d) (i, (recsI (inst Is i)).getD d default)) (fun _ => 0) bus sd := by
  apply walk_bus_row_congr _ _ _ _ ?_ bus hb sd
  intro x hx
  rw [segOf_row tr t _ hd]
  have hend : start Is i + (recsI (inst Is i)).length ≤ R Is := by
    rw [← start_succ, ← start_len]
    exact sum_mono (by omega)
  rw [rowC_cell hcell (by omega) hx]
  simp only [cell, show start Is i + d < R Is by omega, ite_true, recs_seg hi hd]
  rfl

theorem view_walk_messages (Is : List UpsInst) (tr : Trace Fp) (t : Nat) (hH : R Is + 1 ≤ tr.height t)
    (hcell : ∀ r x, r < tr.height t → x < 200 → tr.cell t r x = ((cell Is r x : Int) : Fp))
    (bus : Nat) (hb : bus = B_EDGE ∨ bus = B_BMAP) (sd : Bool) :
    (viewOf tr t (segsOf Is)).flatMap (fun s => s.msgs bus sd) = upsWalkMessages Is bus sd := by
  simp only [viewOf, segsOf, List.flatMap_map]
  apply Eq.trans (b := (List.range Is.length).flatMap (fun i => upsWalkMessages [inst Is i] bus sd))
  · apply flat_congr'
    intro i hi
    have hi' := List.mem_range.mp hi
    unfold UpsSeg.msgs
    rw [segOf_len]
    have hh : (List.range (recsI (inst Is i)).length).flatMap
        (fun d => uMsgs ((segOf tr t (start Is i, (recsI (inst Is i)).length)).row d)
          ((segOf tr t (start Is i, (recsI (inst Is i)).length)).next d) bus sd) =
      (List.range (recsI (inst Is i)).length).flatMap
        (fun d => uMsgs (generatedRow Is 0 (i, (recsI (inst Is i)).getD d default)) (fun _ => 0) bus sd) := by
      apply flat_congr'
      intro d hd
      rw [segment_rows_at Is tr t hH hcell i hi' d (List.mem_range.mp hd) bus hb sd]
      exact generated_position_irrelevant Is i _ 0 _ _ _ bus hb sd
    rw [hh]
    have he := congrArg (List.flatMap (fun r => uMsgs (generatedRow Is 0 (i, r)) (fun _ => 0) bus sd))
      (map_range_getD' (recsI (inst Is i)) default)
    rw [List.flatMap_map] at he
    rw [he]
    exact generated_instance_traffic Is i (fun _ => 0) (fun _ _ => 0) bus hb sd
  · have he := congrArg (List.flatMap (fun I => upsWalkMessages [I] bus sd)) (map_range_getD' Is default)
    simp only [List.flatMap_map] at he
    rw [show (List.range Is.length).flatMap (fun i => upsWalkMessages [inst Is i] bus sd) =
      Is.flatMap (fun I => upsWalkMessages [I] bus sd) from he]
    simp only [upsWalkMessages, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- **The aligned ups component's `EDGE`/`BMAP` traffic is `upsWalkMessages`.** -/
theorem aligned_view_walk_messages (Is : List UpsInst) (h : UpsRenderOk Is) (t : Nat)
    (bus : Nat) (hb : bus = B_EDGE ∨ bus = B_BMAP) (sd : Bool) :
    (viewOf (upsTraceAligned Is) t (segsOf Is)).flatMap (fun s => s.msgs bus sd) = upsWalkMessages Is bus sd := by
  have hh := padded_log_fits (R Is + 1) h.ok.cap
  have hlog : (upsTraceAligned Is).log t = padLog22 (logOf (R Is + 1)) := rfl
  have hH : R Is + 1 ≤ (upsTraceAligned Is).height t := by
    unfold Trace.height; rw [hlog]; exact hh.1
  apply view_walk_messages Is _ t hH _ bus hb sd
  intro r x hr hx
  unfold Trace.height at hr; rw [hlog] at hr
  unfold upsTraceAligned
  rw [rowsTrace_mkTab _ _ _ t r x hr hx, Fp.ofNat_toNat]

/-! ## Record-level `EDGE` and `BMAP` -/

/-- **`EDGE` conservation** of head and node providers, ranked lookup walks and ranked ups walks. -/
theorem edge_records (ws : List WalkR) (Is : List UpsInst) (ho : ∀ I ∈ Is, InstOk I)
    (hl : ∀ I ∈ Is, ∀ t < 4, (step I t).mode ≤ 1 → (step I t).e.length = 6)
    (hs : List HeadE) (vs : List NodeS3) (hwf : ∀ s ∈ vs, s.v.wf) (q : UseRequests)
    (he : q.edges = walkEdgeKeys (ws ++ upsWalkInventory Is))
    (hh : (hs.map HeadE.tau).Nodup)
    (hc : ∀ e ∈ walkEdgeKeys (ws ++ upsWalkInventory Is), e ∈ headEdgeKeys hs ++ nodeEdgeKeys vs) (m : List Fp) :
    cnt (nodeSends3 (assignList q 0 vs) B_EDGE) m + cnt (headSends (assignHeadUses q.edges hs) B_EDGE) m +
        cnt (walkSends3 (rankWalks [] ws) B_EDGE) m +
        cnt (upsWalkMessages (physicalPrefixUps (ws.flatMap (·.steps)) Is) B_EDGE true) m =
      cnt (nodeRecvs3 (assignList q 0 vs) B_EDGE) m + cnt (headRecvs (assignHeadUses q.edges hs) B_EDGE) m +
        cnt (walkRecvs3 (rankWalks [] ws) B_EDGE) m +
        cnt (upsWalkMessages (physicalPrefixUps (ws.flatMap (·.steps)) Is) B_EDGE false) m := by
  have js : ((walkSends3 (rankWalks [] ws) B_EDGE).map Msg.toFp).count m +
      ((upsWalkMessages (physicalPrefixUps (ws.flatMap (·.steps)) Is) B_EDGE true).map Msg.toFp).count m =
      ((Near.Render.BusEdge.sendsW (walkEdgeKeys (ws ++ upsWalkInventory Is))).map Msg.toFp).count m := by
    have := congrArg (fun xs => (xs.map Msg.toFp).count m) (joint_actual_edges ws Is ho hl true)
    simpa only [ite_true, List.map_append, List.count_append, reduceMessages_toFp,
      completeCounterMessages] using this
  have jr : ((walkRecvs3 (rankWalks [] ws) B_EDGE).map Msg.toFp).count m +
      ((upsWalkMessages (physicalPrefixUps (ws.flatMap (·.steps)) Is) B_EDGE false).map Msg.toFp).count m =
      ((Near.Render.BusEdge.recvsW (walkEdgeKeys (ws ++ upsWalkInventory Is))).map Msg.toFp).count m := by
    have := congrArg (fun xs => (xs.map Msg.toFp).count m) (joint_actual_edges ws Is ho hl false)
    simpa only [Bool.false_eq_true, ite_false, List.map_append, List.count_append, reduceMessages_toFp,
      completeCounterMessages] using this
  have hperm := (Near.Render.BusEdge.chain_perm (headEdgeKeys hs ++ nodeEdgeKeys vs)
    (head_node_keys_distinct hs vs hh hwf) (walkEdgeKeys (ws ++ upsWalkInventory Is)) hc).map Msg.toFp
  have hcoun := hperm.count_eq m
  simp only [List.map_append, List.count_append] at hcoun
  rw [assigned_node_edges_send, assigned_node_edges_recv, (assigned_head_edges q.edges hs).1,
    (assigned_head_edges q.edges hs).2, he]
  simp only [cnt]
  generalize (headEdgeKeys hs).map (fun e => e ++ [(walkEdgeKeys (ws ++ upsWalkInventory Is)).count e]) = A at hcoun ⊢
  generalize (nodeEdgeKeys vs).map (fun e => e ++ [(walkEdgeKeys (ws ++ upsWalkInventory Is)).count e]) = B at hcoun ⊢
  omega

/-- **`BMAP` conservation** of node providers, ranked lookup walks and ranked ups walks. -/
theorem bmap_records (ws : List WalkR) (Is : List UpsInst) (ho : ∀ I ∈ Is, InstOk I)
    (vs : List NodeS3) (q : UseRequests) (hb : q.bmaps = walkBmapKeys (ws ++ upsWalkInventory Is))
    (hc : ∀ e ∈ walkBmapKeys (ws ++ upsWalkInventory Is), e ∈ nodeBitmapKeys vs) (m : List Fp) :
    cnt (nodeSends3 (assignList q 0 vs) B_BMAP) m + cnt (walkSends3 (rankWalks [] ws) B_BMAP) m +
        cnt (upsWalkMessages (physicalPrefixUps (ws.flatMap (·.steps)) Is) B_BMAP true) m =
      cnt (nodeRecvs3 (assignList q 0 vs) B_BMAP) m + cnt (walkRecvs3 (rankWalks [] ws) B_BMAP) m +
        cnt (upsWalkMessages (physicalPrefixUps (ws.flatMap (·.steps)) Is) B_BMAP false) m := by
  have js : ((walkSends3 (rankWalks [] ws) B_BMAP).map Msg.toFp).count m +
      ((upsWalkMessages (physicalPrefixUps (ws.flatMap (·.steps)) Is) B_BMAP true).map Msg.toFp).count m =
      ((Near.Render.BusEdge.sendsW (walkBmapKeys (ws ++ upsWalkInventory Is))).map Msg.toFp).count m := by
    have := congrArg (fun xs => (xs.map Msg.toFp).count m) (joint_actual_bitmaps ws Is ho true)
    simpa only [ite_true, List.map_append, List.count_append, reduceMessages_toFp,
      completeCounterMessages] using this
  have jr : ((walkRecvs3 (rankWalks [] ws) B_BMAP).map Msg.toFp).count m +
      ((upsWalkMessages (physicalPrefixUps (ws.flatMap (·.steps)) Is) B_BMAP false).map Msg.toFp).count m =
      ((Near.Render.BusEdge.recvsW (walkBmapKeys (ws ++ upsWalkInventory Is))).map Msg.toFp).count m := by
    have := congrArg (fun xs => (xs.map Msg.toFp).count m) (joint_actual_bitmaps ws Is ho false)
    simpa only [Bool.false_eq_true, ite_false, List.map_append, List.count_append, reduceMessages_toFp,
      completeCounterMessages] using this
  have hperm := (Near.Render.BusEdge.chain_perm (nodeBitmapKeys vs) (nodeBitmapKeys_distinct vs)
    (walkBmapKeys (ws ++ upsWalkInventory Is)) hc).map Msg.toFp
  have hcoun := hperm.count_eq m
  simp only [List.map_append, List.count_append] at hcoun
  rw [assigned_bitmap_send, assigned_bitmap_recv, hb]
  simp only [cnt]
  generalize (nodeBitmapKeys vs).map (fun e => e ++ [(walkBmapKeys (ws ++ upsWalkInventory Is)).count e]) = B at hcoun ⊢
  omega

end ZkFormal.NearV3.Assembly.TrieUps

namespace ZkFormal.NearV3.Assembly

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.NearV3.Render
  Rcpt.Candidates.NodePostUpdate

theorem covers_edge (s : Bool) : Covers B_EDGE s (fun t => t == 2 || t == 3 || t == 5 || t == 7) = true := by
  cases s <;> decide +kernel
theorem covers_bmap (s : Bool) : Covers B_BMAP s (fun t => t == 2 || t == 5 || t == 7) = true := by
  cases s <;> decide +kernel
theorem pub_edge (s : Bool) (pub m : List Fp) : pubCount nearAirV3 pub B_EDGE s m = 0 :=
  pub_off _ _ (by cases s <;> decide +kernel) pub m
theorem pub_bmap (s : Bool) (pub m : List Fp) : pubCount nearAirV3 pub B_BMAP s m = 0 :=
  pub_off _ _ (by cases s <;> decide +kernel) pub m

namespace RenderBundleV3

variable {pub : List Fp} (R : RenderBundleV3 pub)

theorem ups_tf_walk (Is : List UpsInst) (hok : UpsRenderOk Is)
    (hu : ExtOf (R ⟨T_UPS, by decide⟩).tf (upsTraffic (UpsRows.viewOf (upsTraceAligned Is) T_UPS (UpsGen.segsOf Is))))
    (bus : Nat) (hb : bus = B_EDGE ∨ bus = B_BMAP) (s : Bool) :
    sel s (R.tf 7) bus = upsWalkMessages Is bus s := by
  rw [R.tf_ext_sel 7 (by decide) hu bus (by rcases hb with rfl | rfl <;> decide)
    (by rcases hb with rfl | rfl <;> decide) (by rcases hb with rfl | rfl <;> decide) s]
  cases s
  · exact TrieUps.aligned_view_walk_messages Is hok T_UPS bus hb false
  · exact TrieUps.aligned_view_walk_messages Is hok T_UPS bus hb true

/-- **`EDGE` balance of a bundle** from the record-level conservation of its node, head, walk
and (aligned) ups components. -/
theorem balancedAt_edge (vs : List NodeS3) (hs : List HeadE) (ws : List WalkR) (Is : List UpsInst)
    (hok : UpsRenderOk Is)
    (hn : ExtOf (R ⟨T_NODE, by decide⟩).tf (nodeTraffic3 vs)) (hh : (R ⟨T_HEAD, by decide⟩).tf = headTraffic hs)
    (hw : (R ⟨T_WALK, by decide⟩).tf = walkTraffic3 ws)
    (hu : ExtOf (R ⟨T_UPS, by decide⟩).tf (upsTraffic (UpsRows.viewOf (upsTraceAligned Is) T_UPS (UpsGen.segsOf Is))))
    (hbal : ∀ m, cnt (nodeSends3 vs B_EDGE) m + cnt (headSends hs B_EDGE) m + cnt (walkSends3 ws B_EDGE) m +
        cnt (upsWalkMessages Is B_EDGE true) m =
      cnt (nodeRecvs3 vs B_EDGE) m + cnt (headRecvs hs B_EDGE) m + cnt (walkRecvs3 ws B_EDGE) m +
        cnt (upsWalkMessages Is B_EDGE false) m) :
    R.BalancedAt B_EDGE := by
  intro m
  rw [R.sum_tables true _ m _ (covers_edge true), R.sum_tables false _ m _ (covers_edge false),
    pub_edge, pub_edge]
  have e2 := R.tf_ext 2 (by decide) hn B_EDGE (by decide) (by decide) (by decide)
  have e3 : R.tf 3 = headTraffic hs := by rw [← hh]; rfl
  have e5 : R.tf 5 = walkTraffic3 ws := by rw [← hw]; rfl
  have hf : (List.range 25).filter (fun t => t == 2 || t == 3 || t == 5 || t == 7) = [2, 3, 5, 7] := by decide
  rw [hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    R.ups_tf_walk Is hok hu B_EDGE (Or.inl rfl)]
  simp only [e2.1, e2.2, e3, e5, sel, ite_true, Bool.false_eq_true, ite_false, nodeTraffic3, headTraffic, walkTraffic3]
  have := hbal m
  omega

/-- **`BMAP` balance of a bundle** from the record-level conservation of its node, walk and
(aligned) ups components. -/
theorem balancedAt_bmap (vs : List NodeS3) (ws : List WalkR) (Is : List UpsInst)
    (hok : UpsRenderOk Is)
    (hn : ExtOf (R ⟨T_NODE, by decide⟩).tf (nodeTraffic3 vs)) (hw : (R ⟨T_WALK, by decide⟩).tf = walkTraffic3 ws)
    (hu : ExtOf (R ⟨T_UPS, by decide⟩).tf (upsTraffic (UpsRows.viewOf (upsTraceAligned Is) T_UPS (UpsGen.segsOf Is))))
    (hbal : ∀ m, cnt (nodeSends3 vs B_BMAP) m + cnt (walkSends3 ws B_BMAP) m + cnt (upsWalkMessages Is B_BMAP true) m =
      cnt (nodeRecvs3 vs B_BMAP) m + cnt (walkRecvs3 ws B_BMAP) m + cnt (upsWalkMessages Is B_BMAP false) m) :
    R.BalancedAt B_BMAP := by
  intro m
  rw [R.sum_tables true _ m _ (covers_bmap true), R.sum_tables false _ m _ (covers_bmap false),
    pub_bmap, pub_bmap]
  have e2 := R.tf_ext 2 (by decide) hn B_BMAP (by decide) (by decide) (by decide)
  have e5 : R.tf 5 = walkTraffic3 ws := by rw [← hw]; rfl
  have hf : (List.range 25).filter (fun t => t == 2 || t == 5 || t == 7) = [2, 5, 7] := by decide
  rw [hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    R.ups_tf_walk Is hok hu B_BMAP (Or.inr rfl)]
  simp only [e2.1, e2.2, e5, sel, ite_true, Bool.false_eq_true, ite_false, nodeTraffic3, walkTraffic3]
  have := hbal m
  omega

end RenderBundleV3

end ZkFormal.NearV3.Assembly
