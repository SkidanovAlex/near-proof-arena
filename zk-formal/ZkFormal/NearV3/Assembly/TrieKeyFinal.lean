import ZkFormal.NearV3.Assembly.TrieUps
import ZkFormal.NearV3.Render.PaddedQvNative
import ZkFormal.NearV3.Candidates.QueueKeyRepair
import ZkFormal.NearV3.Candidates.NativeQueryKeyTraffic
import ZkFormal.NearV3.Candidates.NativeQueryFinalTraffic
import ZkFormal.NearV3.Rcpt.Candidates.NativeLookupQueryBounds
import ZkFormal.NearV3.Assembly.RenderV3RcptSide
import ZkFormal.NearV3.Assembly.TrieWalkAlign

/-!
# ZkFormal.NearV3.Assembly.TrieKeyFinal — `KEYNIB` (walk ← rcpt, qv)

`KEYNIB`: `rcptV3` (16) and `qvV3` (22) send, `walkV3` (5) receives; no public messages.

* `walk_keynib`: the walk component's receives are the key messages of the SAME native query list
  `allLookupQueries rs pre v pres resolve` (account, access-key, queue queries);
* **`qv_keynib`**: the qv render's sends (`qvNativeTraffic pre v pres`) are the key messages of
  `queueLookupQueries pre v pres (NativeQueueIds.resolve pre v pres)`;
* `qv_keynib_recv`, `rcpt_keynib_recv`: the silent sides;
* **`RenderBundleV3.balancedAt_keynib`**: the bundle balance, given the walk/qv components above
  (with `resolve := NativeQueueIds.resolve pre v pres`), the rcpt render `rcptTrafficB pub x`, and
  the receipt side's identity
  `RcptKeys`: the rcpt component's `KEYNIB` sends are (as field messages, up to order) the key
  messages of `accountLookupQueries rs ++ accessKeyLookupQueries rs` (receipt lane).
-/

namespace ZkFormal.NearV3.Assembly.TrieKeyFinal

open NearSpec NearSpecV3 ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3 ZkFormal.NearV3.Assembly
  Render Rcpt.Candidates.NodePostUpdate Qv Qv.Candidates Qv.Candidates.CombinedWalkGen

/-- The key messages of a query list. -/
def keyOf (qs : List NativeLookupQuery) : List ZkFormal.Near.Msg :=
  qs.flatMap (fun q => RcptE.keyMsgs q.wid (q.key ++ [SYM_END]))

theorem walk_keynib (pairs : List (PTrie × PTrie)) (qs : List NativeLookupQuery) (ws : List WalkR)
    (h : nativeQueryWalks pairs qs = some ws) :
    walkRecvs3 (rankWalks [] ws) B_KEYNIB = keyOf qs := by
  rw [Candidates.NativeQueryKey.ranks_key, Candidates.NativeQueryKey.queries_key pairs qs ws h]
  rfl

theorem keyMsgs_snoc (w : Nat) (xs : List Nat) (e : Nat) :
    RcptE.keyMsgs w (xs ++ [e]) = xs.zipIdx.map (fun ni => [w, ni.2, ni.1, 0]) ++ [[w, xs.length, e, 1]] := by
  unfold RcptE.keyMsgs
  rw [List.length_append, List.length_singleton, List.range_succ, List.map_append]
  congr 1
  · apply List.ext_getElem
    · simp
    · intro n h1 h2
      simp only [List.length_map, List.length_range] at h1
      simp [List.getElem_zipIdx, List.getD_eq_getElem?_getD, List.getElem?_append_left h1,
        List.getElem?_eq_getElem h1]
      omega
  · simp

theorem repaired_key (w : Walk) : w.repairedKeyWordMessages = Candidates.QueueKeyRepair.keyMessages w := by
  unfold Walk.repairedKeyWordMessages Candidates.QueueKeyRepair.keyMessages
  rw [keyMsgs_snoc, nibbles_length]
  rfl

theorem qv_keynib (pre : PTrie) (v : MainValues) (pres : List PTrie) :
    (qvNativeTraffic pre v pres).sends B_KEYNIB =
      keyOf (queueLookupQueries pre v pres (Candidates.NativeQueueIds.resolve pre v pres)) := by
  have hc : (Qv.Candidates.ValueGen.canonicalTraffic (qvNativeRecords pre v pres)).sends B_KEYNIB = [] := by
    simp [Qv.Candidates.ValueGen.canonicalTraffic, B_KEYNIB, B_VBYTES, ValueTable.B_QVC, B_QSH]
  have hw : (fun w : Walk => w.repairedWordMessages B_KEYNIB true) = fun w => w.repairedKeyWordMessages := by
    funext w; simp [Walk.repairedWordMessages]
  change (qvNativeWalks pre v pres).flatMap (fun w => w.repairedWordMessages B_KEYNIB true) ++ _ = _
  rw [hc, List.append_nil, hw, keyOf, queueLookupQueries, List.flatMap_map]
  unfold qvNativeWalks
  congr 1
  funext w
  rw [repaired_key]
  rfl

theorem keyOf_all (rs : List Receipt) (pre : PTrie) (v : MainValues) (pres : List PTrie) (resolve : Resolve) :
    keyOf (allLookupQueries rs pre v pres resolve) =
      keyOf (accountLookupQueries rs ++ accessKeyLookupQueries rs) ++ keyOf (queueLookupQueries pre v pres resolve) := by
  simp only [keyOf, allLookupQueries, List.flatMap_append]

/-- The receipt side's `KEYNIB` identity (receipt lane). -/
def RcptKeys (tf : Traffic) (rs : List Receipt) : Prop :=
  ((tf.sends B_KEYNIB).map Msg.toFp).Perm ((keyOf (accountLookupQueries rs ++ accessKeyLookupQueries rs)).map Msg.toFp)

theorem covers_keynib (s : Bool) : Covers B_KEYNIB s (fun t => t == 5 || t == 16 || t == 22) = true := by
  cases s <;> decide +kernel
theorem pub_keynib (s : Bool) (pub m : List Fp) : ZkFormal.V2.pubCount nearAirV3 pub B_KEYNIB s m = 0 :=
  pub_off _ _ (by cases s <;> decide +kernel) pub m

theorem walk_keynib_send (ws : List WalkR) : walkSends3 ws B_KEYNIB = [] := by
  simp [walkSends3, B_KEYNIB, B_EDGE, B_BMAP, B_FINAL]

theorem qv_keynib_recv (pre : PTrie) (v : MainValues) (pres : List PTrie) :
    (qvNativeTraffic pre v pres).recvs B_KEYNIB = [] := by
  simp [qvNativeTraffic, repairedTraffic, Walk.repairedWordMessages, Walk.wordMessages,
    Qv.Candidates.ValueGen.canonicalTraffic, B_KEYNIB, ValueTable.B_QVC, B_FINAL, B_QSH]

theorem rcpt_keynib_recv (pub : List ZkFormal.Algebra.Fp) (x : RcptSkeleton.RcptInput) :
    (RcptSkeleton.rcptTrafficB pub x).recvs B_KEYNIB = [] := by
  simp [RcptSkeleton.rcptTrafficB, B_KEYNIB, B_BND, rcptTraffic3, rcptRecvs3, rRecvs, B_DIGEST, B_FINAL, B_MEM, B_SREC, B_BYTES, B_AKC, B_RCL, B_RIDS, B_MPOS]

/-! ## `FINAL` (walk → rcpt, qv) -/

theorem walk_final (pairs : List (PTrie × PTrie)) (qs : List NativeLookupQuery) (ws : List WalkR)
    (h : nativeQueryWalks pairs qs = some ws) :
    walkSends3 (rankWalks [] ws) B_FINAL = qs.map (Candidates.NativeQueryFinal.queryMessage pairs) := by
  rw [Candidates.NativeQueryFinal.ranks_final, Candidates.NativeQueryFinal.queries_final pairs qs ws h]

theorem walk_final_recv (ws : List WalkR) : walkRecvs3 ws B_FINAL = [] := by
  simp [walkRecvs3, B_KEYNIB, B_EDGE, B_BMAP, B_FINAL]

/-- **The qv render's `FINAL` receives** are the final messages of the queue queries. -/
theorem qv_final (pre : PTrie) (v : MainValues) (pres : List PTrie) (pairs : List (PTrie × PTrie))
    (hp : pairs.map Prod.fst = pre :: pres) (hh : ∀ x ∈ queueInputs pre v pres, ∀ r ∈ x.2, r.Holds x.1) :
    (qvNativeTraffic pre v pres).recvs B_FINAL =
      (queueLookupQueries pre v pres (Candidates.NativeQueueIds.resolve pre v pres)).map
        (Candidates.NativeQueryFinal.queryMessage pairs) := by
  rw [← Candidates.NativeQueueFinalMessages.plan_messages pre v pres pairs hp hh]
  simp [qvNativeTraffic, repairedTraffic, Walk.repairedWordMessages, Walk.wordMessages,
    Qv.Candidates.ValueGen.canonicalTraffic, B_KEYNIB, ValueTable.B_QVC, B_FINAL, B_QSH, qvNativeWalks]

theorem qv_final_send (pre : PTrie) (v : MainValues) (pres : List PTrie) :
    (qvNativeTraffic pre v pres).sends B_FINAL = [] := by
  simp [qvNativeTraffic, repairedTraffic, Walk.repairedWordMessages, Walk.wordMessages,
    Qv.Candidates.ValueGen.canonicalTraffic, B_KEYNIB, ValueTable.B_QVC, B_FINAL, B_QSH, B_VBYTES]

theorem rcpt_final_send (pub : List ZkFormal.Algebra.Fp) (x : RcptSkeleton.RcptInput) :
    (RcptSkeleton.rcptTrafficB pub x).sends B_FINAL = [] := by
  simp [RcptSkeleton.rcptTrafficB, B_KEYNIB, B_BND, rcptTraffic3, rcptSends3, rSends, B_DIGEST, B_FINAL, B_MEM,
    B_SREC, B_BYTES, B_AKC, B_RCL, B_RIDS, B_MPOS]

/-- The receipt side's `FINAL` identity (receipt lane). -/
def RcptFinal (tf : Traffic) (pairs : List (PTrie × PTrie)) (rs : List Receipt) : Prop :=
  ((tf.recvs B_FINAL).map Msg.toFp).Perm
    (((accountLookupQueries rs ++ accessKeyLookupQueries rs).map
      (Candidates.NativeQueryFinal.queryMessage pairs)).map Msg.toFp)

theorem covers_final (s : Bool) : Covers B_FINAL s (fun t => t == 5 || t == 16 || t == 22) = true := by
  cases s <;> decide +kernel
theorem pub_final (s : Bool) (pub m : List Fp) : ZkFormal.V2.pubCount nearAirV3 pub B_FINAL s m = 0 :=
  pub_off _ _ (by cases s <;> decide +kernel) pub m

namespace RenderBundleV3

variable {pub : List Fp} (R : RenderBundleV3 pub)

/-- **`KEYNIB` balance of a bundle.** -/
theorem balancedAt_keynib (pairs : List (PTrie × PTrie)) (rs : List Receipt) (pre : PTrie) (v : MainValues)
    (pres : List PTrie) (ws : List WalkR)
    (hws : nativeQueryWalks pairs (allLookupQueries rs pre v pres
      (Candidates.NativeQueueIds.resolve pre v pres)) = some ws)
    (hw : (R ⟨T_WALK, by decide⟩).tf = walkTraffic3 (rankWalks [] ws))
    (hq : (R ⟨22, by decide⟩).tf = qvNativeTraffic pre v pres)
    (x : RcptSkeleton.RcptInput) (h16 : (R ⟨16, by decide⟩).tf = RcptSkeleton.rcptTrafficB pub x)
    (hr : RcptKeys (RcptSkeleton.rcptTrafficB pub x) rs) :
    R.BalancedAt B_KEYNIB := by
  intro m
  rw [R.sum_tables true _ m _ (covers_keynib true), R.sum_tables false _ m _ (covers_keynib false),
    pub_keynib, pub_keynib]
  have e5 : R.tf 5 = walkTraffic3 (rankWalks [] ws) := by rw [← hw]; rfl
  have e16 : R.tf 16 = RcptSkeleton.rcptTrafficB pub x := by rw [← h16]; rfl
  have e22 : R.tf 22 = qvNativeTraffic pre v pres := by rw [← hq]; rfl
  have hf : (List.range 25).filter (fun t => t == 5 || t == 16 || t == 22) = [5, 16, 22] := by decide
  rw [hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, e5, e16, e22, sel,
    ite_true, Bool.false_eq_true, ite_false, walkTraffic3, walk_keynib_send, rcpt_keynib_recv, qv_keynib_recv,
    walk_keynib pairs _ ws hws, qv_keynib, keyOf_all]
  have hp := hr.count_eq m
  simp only [cnt, List.map_append, List.count_append, List.map_nil, List.count_nil] at hp ⊢
  omega

/-- **`FINAL` balance of a bundle.** -/
theorem balancedAt_final (pairs : List (PTrie × PTrie)) (rs : List Receipt) (pre : PTrie) (v : MainValues)
    (pres : List PTrie) (ws : List WalkR) (hp : pairs.map Prod.fst = pre :: pres)
    (hh : ∀ x ∈ queueInputs pre v pres, ∀ r ∈ x.2, r.Holds x.1)
    (hws : nativeQueryWalks pairs (allLookupQueries rs pre v pres
      (Candidates.NativeQueueIds.resolve pre v pres)) = some ws)
    (hw : (R ⟨T_WALK, by decide⟩).tf = walkTraffic3 (rankWalks [] ws))
    (hq : (R ⟨22, by decide⟩).tf = qvNativeTraffic pre v pres)
    (x : RcptSkeleton.RcptInput) (h16 : (R ⟨16, by decide⟩).tf = RcptSkeleton.rcptTrafficB pub x)
    (hr : RcptFinal (RcptSkeleton.rcptTrafficB pub x) pairs rs) :
    R.BalancedAt B_FINAL := by
  intro m
  rw [R.sum_tables true _ m _ (covers_final true), R.sum_tables false _ m _ (covers_final false),
    pub_final, pub_final]
  have e5 : R.tf 5 = walkTraffic3 (rankWalks [] ws) := by rw [← hw]; rfl
  have e16 : R.tf 16 = RcptSkeleton.rcptTrafficB pub x := by rw [← h16]; rfl
  have e22 : R.tf 22 = qvNativeTraffic pre v pres := by rw [← hq]; rfl
  have hf : (List.range 25).filter (fun t => t == 5 || t == 16 || t == 22) = [5, 16, 22] := by decide
  rw [hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, e5, e16, e22, sel,
    ite_true, Bool.false_eq_true, ite_false, walkTraffic3, walk_final_recv, rcpt_final_send, qv_final_send,
    walk_final pairs _ ws hws, qv_final pre v pres pairs hp hh, allLookupQueries, List.map_append]
  have hp' := hr.count_eq m
  simp only [cnt, List.map_append, List.count_append, List.map_nil, List.count_nil] at hp' ⊢
  omega

end RenderBundleV3


/-- **`KEYNIB` and `FINAL` for an accepted witness** `A` (the receipt side's choice): the walk
component of the trie side (`trie_all_of` run on `A`'s data with
`resolve := NativeQueueIds.resolve A.m.pre A.qvVals (A.steps.map ImplicitStepV3.pre)`; its queue
values are `A.qvVals` by `TrieWalkAlign.trie_v_eq_qvVals`) and the receipt-side renders, given the
receipt lane's identities `RcptKeys` / `RcptFinal` for `rcptTrafficB A.pub A.rcptInput`. -/
theorem keynib_final_accepted {cb wb : Bytes} (A : AcceptedV3 cb wb) (R : RenderBundleV3 A.pub)
    {v : MainValues} {ws : List WalkR} (hvv : v.Valid) (hvr : v.Reads A.m.pre A.m.pre A.m.pre)
    (hws : nativeQueryWalks ((A.m.pre, A.m.result.trie) :: A.steps.map (fun s => (s.pre, s.post)))
      (allLookupQueries (appliedReceipts A.k A.w) A.m.pre v (A.steps.map ImplicitStepV3.pre)
        (Candidates.NativeQueueIds.resolve A.m.pre A.qvVals (A.steps.map ImplicitStepV3.pre))) = some ws)
    (hw : (R ⟨T_WALK, by decide⟩).tf = walkTraffic3 (rankWalks [] ws))
    (h16 : R ⟨16, by decide⟩ = A.rcptRenders.rcpt) (h22 : R ⟨22, by decide⟩ = A.rcptRenders.qv)
    (hk : RcptKeys (RcptSkeleton.rcptTrafficB A.pub A.rcptInput) (appliedReceipts A.k A.w))
    (hf : RcptFinal (RcptSkeleton.rcptTrafficB A.pub A.rcptInput)
      ((A.m.pre, A.m.result.trie) :: A.steps.map (fun s => (s.pre, s.post))) (appliedReceipts A.k A.w)) :
    R.BalancedAt B_KEYNIB ∧ R.BalancedAt B_FINAL := by
  have hv := TrieWalkAlign.trie_v_eq_qvVals A hvv hvr
  subst hv
  have t16 : (R ⟨16, by decide⟩).tf = RcptSkeleton.rcptTrafficB A.pub A.rcptInput := by rw [h16]; rfl
  have t22 : (R ⟨22, by decide⟩).tf = qvNativeTraffic A.m.pre A.qvVals (A.steps.map ImplicitStepV3.pre) := by
    rw [h22]; rfl
  have hp : ((A.m.pre, A.m.result.trie) :: A.steps.map (fun s => (s.pre, s.post))).map Prod.fst =
      A.m.pre :: A.steps.map ImplicitStepV3.pre := by simp [Function.comp_def]
  exact ⟨RenderBundleV3.balancedAt_keynib R _ _ _ _ _ ws hws hw t22 _ t16 hk,
    RenderBundleV3.balancedAt_final R _ _ _ _ _ ws hp A.qvHolds hws hw t22 _ t16 hf⟩

end ZkFormal.NearV3.Assembly.TrieKeyFinal
