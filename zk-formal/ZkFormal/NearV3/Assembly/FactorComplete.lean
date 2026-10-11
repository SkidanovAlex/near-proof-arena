import ZkFormal.NearV3.Assembly.NativeGoodGap
import ZkFormal.NearV3.Assembly.NativeUnfold
import ZkFormal.NearV3.Assembly.QueueSeed

/-!
# ZkFormal.NearV3.Assembly.FactorComplete — accepted witnesses admit semantic views

`FactorComplete` (`Good.lean`): every witness the amended checker accepts has semantic views
`GoodV3`. `NativeGoodGap.good_of_native` derives every field from native acceptance except
three bounds read on the *reconstructed* witness `witnessOfV3 k x` (A7, A9, A11). They are
closed here:

* the reconstructed witness re-runs natively with the same main execution and implicit
  steps (`nativeValid_reconstructed`, `ImplicitTraceValid.renorm`): its stores are
  `normalStore pre = (revealedStore pre).eraseDups`, which rebuild the same pre tries;
* hence `triesD0` of the reconstruction equals `triesD0N` of the original
  (`triesD0_reconstructed`): the reconstruction's post tries are rebuilt from exactly the
  revealed blobs, which is what A11 (`unfoldBytesN = unfoldBytes`) compares against;
* A7: `unfoldBytes (rec.) = unfoldBytesN (orig.) = unfoldBytes (orig.) ≤ B` by A11;
* A9: the scheduler inputs read only the pre tries, which are unchanged;
* A11 on the reconstruction: `triesD0N` of the reconstruction is `triesD0N` of the original.
-/

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Sched

/-- The reconstruction's store is the spec's `revealedStore`, deduplicated. -/
theorem normalStore_revealed (t : PTrie) : normalStore t = (revealedStore t).eraseDups := by
  have enc : NearSpecV3.nodeEnc = nodeEnc := rfl
  unfold normalStore revealedStore
  rw [native_valsOf_eq, enc, native_occs_eq]

theorem storeLookupEq_normal (t : PTrie) : StoreLookupEq (normalStore t) (revealedStore t) :=
  fun h => by rw [normalStore_revealed]; exact storeGet_eraseDups _ h

/-! ## `triesD0N` of an accepted witness in closed form -/

/-- `triesD0N`'s implicit loop body. -/
def unfoldStepN (k : WalkD0) (pair : Blk × Transition)
    (st : List (PTrie × PTrie) × Bytes) : Except String (ForInStep (List (PTrie × PTrie) × Bytes)) := do
  let ctx := blockCtx k.L k.H.shardId k.slotB2.gasLimit pair.1 pair.1.hdr.nextGasPrice
  let keys := [keyDelayedIdx,keyBwState]
  let pre := partialTrie pair.2.values st.2 keys
  let post ← applyMissingChunk prims ctx pre
  pure (.yield (st.1 ++ [(pre,rebuildPost (revealedStore pre) post keys)],post.hashOf))

def unfoldedPairsN (steps : List ImplicitStepV3) : List (PTrie × PTrie) :=
  steps.map (fun s => (s.pre,rebuildPost (revealedStore s.pre) s.post [keyDelayedIdx,keyBwState]))

theorem ImplicitTraceValid.unfoldN_result {k root pairs steps last}
    (hv : ImplicitTraceValid k root pairs steps last) (acc : List (PTrie × PTrie)) :
    forIn pairs (acc,root) (unfoldStepN k) = .ok (acc ++ unfoldedPairsN steps,last) := by
  induction hv generalizing acc with
  | nil => simp [unfoldedPairsN,pure,Except.pure]
  | cons root b t rest steps post last run checked tail ih =>
    simp only [List.forIn_cons,unfoldStepN,run,bind,Except.bind,pure,Except.pure]
    rw [ih]
    simp only [unfoldedPairsN,List.map_cons,List.append_assoc,List.singleton_append]

theorem triesD0N_native_result {cb wb : Bytes} {k : WalkD0} {w : StateWitness}
    {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes}
    (hk : walkD0 cb = .ok k) (hw : decodeW wb = .ok w) (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last) :
    triesD0N cb wb = .ok ((m.pre,rebuildPost (revealedStore m.pre) m.result.trie
      (mainKeys (appliedReceipts k w) m.bufferedShards)) :: unfoldedPairsN steps) := by
  obtain ⟨v,hfind,hparse⟩ := hm.buffered
  have run := hm.run
  rw [hm.pre] at run
  unfold MainExecutionV3.ctx at run
  have hloop := hv.unfoldN_result
  unfold ZkFormal.NearV3.Assembly.unfoldStepN at hloop
  dsimp only at hloop
  simp only [bind,Except.bind,pure,Except.pure] at hloop
  unfold triesD0N
  simp only [hk,hw,bind,Except.bind,hm.block,hm.previous,pure,Except.pure,hfind,hparse,run,hloop]
  rw [hm.pre]
  rfl

/-! ## The reconstructed witness re-runs natively -/

/-- The implicit transition the reconstruction writes for step `e`. -/
def renormTransition (e : ImplicitStepV3) : Transition :=
  ⟨List.replicate 32 0, normalStore e.pre, e.post.hashOf⟩

def renormStep (e : ImplicitStepV3) : ImplicitStepV3 := { e with witness := renormTransition e }

/-- The implicit trace over the renormalized transitions: same pre tries, same posts. -/
theorem ImplicitTraceValid.renorm {k root pairs steps last}
    (hv : ImplicitTraceValid k root pairs steps last) :
    ImplicitTraceValid k root (steps.map fun e => (e.block, renormTransition e))
      (steps.map renormStep) last := by
  induction hv with
  | nil root => exact .nil root
  | cons root b t rest steps post last run checked tail ih =>
    have hr := implicit_run_root_length run
    have hP : partialTrie (normalStore (partialTrie t.values root [keyDelayedIdx,keyBwState])) root
        [keyDelayedIdx,keyBwState] = partialTrie t.values root [keyDelayedIdx,keyBwState] :=
      partialTrie_normalStore _ _ _ hr
    have hc := ImplicitTraceValid.cons root b
      (renormTransition ⟨b,t,root,partialTrie t.values root [keyDelayedIdx,keyBwState],post⟩)
      _ _ post last (by simp only [renormTransition]; rw [hP]; exact run) rfl ih
    simp only [renormTransition] at hc
    rw [hP] at hc
    exact hc

theorem zip_map_map {α β γ : Type} (f : α → β) (g : α → γ) (l : List α) :
    (l.map f).zip (l.map g) = l.map fun a => (f a, g a) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, List.zip_cons_cons, ih]

section
variable {cb wb : Bytes} {k : WalkD0} {w : StateWitness} {bs : Bytes}
  {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes}

/-- The reconstruction's implicit transitions are the renormalized steps'. -/
theorem reconstructed_implicit (hd : decodeStateWitness bs = .ok w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    (hcount : w.implicit.length = k.implicitBlks.length)
    (hf : ∀ t ∈ m.pre :: steps.map ImplicitStepV3.pre, t.wf = true)
    (hc : (forestBytes (m.pre :: steps.map ImplicitStepV3.pre)).length ≤ ZkFormal.Algebra.P) :
    k.implicitBlks.zip (stateWitnessOfV3 k (nativeExecutionViews k w m steps)).implicit =
      steps.map fun e => (e.block, renormTransition e) := by
  have hlen : steps.length = k.implicitBlks.length := by
    rw [hv.length,List.length_zip,hcount,Nat.min_self]
  have hblocks : steps.map ImplicitStepV3.block = k.implicitBlks := by
    have hh := congrArg (List.map Prod.fst) hv.pairs
    simp only [List.map_map,Function.comp_def,
      List.map_fst_zip (by omega : k.implicitBlks.length ≤ w.implicit.length)] at hh
    exact hh
  have hviews := runtimePairs_implicit_views hv m hf hc
  have himp : (stateWitnessOfV3 k (nativeExecutionViews k w m steps)).implicit =
      steps.map renormTransition := by
    apply List.ext_getElem
    · simp [stateWitnessOfV3, hlen]
    · intro i h1 h2
      have hi : i < steps.length := by simpa using h2
      have hv' := hviews i steps[i] (List.getElem?_eq_getElem hi)
      simp only [stateWitnessOfV3, List.getElem_map, List.getElem_zipIdx, ExtV3.transition,
        renormTransition]
      rw [show 0 + i + 1 = 1 + i by omega]
      have e1 : (nativeExecutionViews k w m steps).store (1 + i) = normalStore steps[i].pre := hv'.2.1
      have e2 : (nativeExecutionViews k w m steps).post (1 + i) = steps[i].post.hashOf := hv'.2.2
      rw [e1, e2]
  rw [himp, ← hblocks, zip_map_map]

/-- The reconstructed witness re-runs natively with the same main execution. -/
theorem nativeValid_reconstructed (hd : decodeStateWitness bs = .ok w) (hm : m.NativeValid k w)
    (hf : ∀ t ∈ m.pre :: steps.map ImplicitStepV3.pre, t.wf = true)
    (hc : (forestBytes (m.pre :: steps.map ImplicitStepV3.pre)).length ≤ ZkFormal.Algebra.P) :
    m.NativeValid k (stateWitnessOfV3 k (nativeExecutionViews k w m steps)) := by
  have hs : (nativeExecutionViews k w m steps).store 0 = normalStore m.pre := by
    change (traceStoreViews (runtimePairs m steps)).store 0 = _
    rw [traceStoreViews_store,runtimePairs_pre]
    exact forestStoreViews_store hf hc rfl
  have hpost : (nativeExecutionViews k w m steps).post 0 = m.result.trie.hashOf := by
    change (traceStoreViews (runtimePairs m steps)).post 0 = _
    exact traceStoreViews_post (show (runtimePairs m steps)[0]? = some (m.pre,m.result.trie) from rfl)
  have hr := hm.root_length
  have happ : appliedReceipts k (stateWitnessOfV3 k (nativeExecutionViews k w m steps)) =
      appliedReceipts k w := by
    unfold appliedReceipts
    rw [nativeExecutionViews_entries hd]
  have run := hm.run
  rw [hm.pre] at run
  have hbuf := applyNewChunk_normalStore_buffered hr run
  refine ⟨hm.block, hm.previous, ?_, ?_, hm.preRoot, ?_, ?_, ?_⟩
  · obtain ⟨v, hv, hh⟩ := hm.buffered
    refine ⟨v, ?_, hh⟩
    change (partialTrie ((nativeExecutionViews k w m steps).store 0) _ _).find _ = _
    rw [hs, hm.pre, hbuf]
    exact hv
  · change m.pre = partialTrie ((nativeExecutionViews k w m steps).store 0) _ _
    rw [happ, hs, hm.pre, partialTrie_normalStore _ _ _ hr]
  · rw [happ]
    exact hm.run
  · change m.result.trie.hashOf = (nativeExecutionViews k w m steps).post 0
    rw [hpost]
  · exact nativeExecutionViews_main_payload hm hf hc

end

/-! ## A7, A9, A11 on the reconstruction -/

theorem decodeW_witnessOfV3 {k : WalkD0} {x : ExtV3} (hs : V3.D0Shape (stateWitnessOfV3 k x)) :
    decodeW (witnessOfV3 k x) = .ok (stateWitnessOfV3 k x) := by
  unfold decodeW witnessOfV3
  rw [V3.decodeWitnessFile_encode _ hs]
  simpa only [bind, Except.bind] using V3.decodeStateWitness_encode _ hs

section
variable {cb wb bs : Bytes} {k : WalkD0} {w : StateWitness}
  {m : MainExecutionV3} {steps : List ImplicitStepV3} {last : Bytes}

/-- `triesD0` of the reconstruction is `triesD0N` of the original, and so is `triesD0N` of
the reconstruction. -/
theorem tries_reconstructed (hk : walkD0 cb = .ok k) (hw : decodeW wb = .ok w)
    (hd : decodeStateWitness bs = .ok w) (hm : m.NativeValid k w)
    (hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last)
    (hcount : w.implicit.length = k.implicitBlks.length)
    (hf : ∀ t ∈ m.pre :: steps.map ImplicitStepV3.pre, t.wf = true)
    (hc : (forestBytes (m.pre :: steps.map ImplicitStepV3.pre)).length ≤ ZkFormal.Algebra.P)
    (hshape : V3.D0Shape (stateWitnessOfV3 k (nativeExecutionViews k w m steps))) :
    triesD0 cb (witnessOfV3 k (nativeExecutionViews k w m steps)) = triesD0N cb wb ∧
      triesD0N cb (witnessOfV3 k (nativeExecutionViews k w m steps)) = triesD0N cb wb := by
  have hw' := decodeW_witnessOfV3 hshape
  have hm' := nativeValid_reconstructed hd hm hf hc
  have hv' := hv.renorm
  rw [← reconstructed_implicit hd hv hcount hf hc] at hv'
  have hn := triesD0N_native_result hk hw hm hv
  have happ : appliedReceipts k (stateWitnessOfV3 k (nativeExecutionViews k w m steps)) =
      appliedReceipts k w := by
    unfold appliedReceipts
    rw [nativeExecutionViews_entries hd]
  have hs : (stateWitnessOfV3 k (nativeExecutionViews k w m steps)).main.values = normalStore m.pre := by
    change (traceStoreViews (runtimePairs m steps)).store 0 = _
    rw [traceStoreViews_store,runtimePairs_pre]
    exact forestStoreViews_store hf hc rfl
  have hpairsN : unfoldedPairsN (steps.map renormStep) = unfoldedPairsN steps := by
    simp only [unfoldedPairsN, List.map_map, Function.comp_def, renormStep]
  refine ⟨?_, ?_⟩
  · rw [triesD0_native_result hk hw' hm' hv', hn, hs, happ,
      (storeLookupEq_normal m.pre).rebuildPost]
    congr 2
    simp only [unfoldedPairs, unfoldedPairsN, List.map_map, Function.comp_def, renormStep,
      renormTransition]
    apply List.map_congr_left
    intro e _
    rw [(storeLookupEq_normal e.pre).rebuildPost]
  · rw [triesD0N_native_result hk hw' hm' hv', hn, happ, hpairsN]

theorem zip_map_congr3 {α β γ δ : Type} (F : α × β × γ → δ)
    (hF : ∀ c p q q', F (c,p,q) = F (c,p,q')) (cs : List α) (l l' : List (β × γ))
    (h : l.map Prod.fst = l'.map Prod.fst) : (cs.zip l).map F = (cs.zip l').map F := by
  induction cs generalizing l l' with
  | nil => simp
  | cons c cs ih =>
    cases l with
    | nil => cases l' with
      | nil => rfl
      | cons _ _ => simp at h
    | cons a l => cases l' with
      | nil => simp at h
      | cons a' l' =>
        obtain ⟨p, q⟩ := a
        obtain ⟨p', q'⟩ := a'
        simp only [List.map_cons, List.cons.injEq] at h
        obtain ⟨rfl, h⟩ := h
        simp only [List.zip_cons_cons, List.map_cons, hF c p q q', ih l l' h]

theorem zip_map_congr2 {α β δ : Type} (F : α × β → δ) (hF : ∀ a b b', F (a,b) = F (a,b'))
    (as : List α) (bs bs' : List β) (h : bs.length = bs'.length) :
    (as.zip bs).map F = (as.zip bs').map F := by
  induction as generalizing bs bs' with
  | nil => simp
  | cons a as ih =>
    cases bs with
    | nil => cases bs' with
      | nil => rfl
      | cons _ _ => simp at h
    | cons b bs => cases bs' with
      | nil => simp at h
      | cons b' bs' =>
        simp only [List.length_cons, Nat.add_right_cancel_iff] at h
        simp only [List.zip_cons_cons, List.map_cons, hF a b b', ih bs bs' h]

/-- The scheduler inputs read the witness only through its implicit count and the pre tries. -/
theorem schedInsD0_congr {cb wb₁ wb₂ : Bytes} {k : WalkD0} {w₁ w₂ : StateWitness}
    {L₁ L₂ : List (PTrie × PTrie)} (hk : walkD0 cb = .ok k)
    (hw₁ : decodeW wb₁ = .ok w₁) (hw₂ : decodeW wb₂ = .ok w₂)
    (hl : w₁.implicit.length = w₂.implicit.length)
    (ht₁ : triesD0 cb wb₁ = .ok L₁) (ht₂ : triesD0 cb wb₂ = .ok L₂)
    (hf : L₁.map Prod.fst = L₂.map Prod.fst) :
    schedInsD0 cb wb₁ = schedInsD0 cb wb₂ := by
  have e1 : (k.implicitBlks.zip w₁.implicit).map
        (fun x => blockCtx k.L k.H.shardId k.slotB2.gasLimit x.fst x.fst.hdr.nextGasPrice) =
      (k.implicitBlks.zip w₂.implicit).map
        (fun x => blockCtx k.L k.H.shardId k.slotB2.gasLimit x.fst x.fst.hdr.nextGasPrice) :=
    zip_map_congr2 _ (fun _ _ _ => rfl) _ _ _ hl
  have e2 : ∀ cs : List ApplyCtx, (cs.zip L₁).map (fun x : ApplyCtx × PTrie × PTrie =>
        ({ shardIds := x.fst.layout.shardIds, own := x.fst.own,
           prev := (x.2.fst.find keyBwState).getD none, statuses := x.fst.statuses,
           requests := x.fst.requests, prevBlockHash := x.fst.prevBlockHash } : SchedIn)) =
      (cs.zip L₂).map (fun x : ApplyCtx × PTrie × PTrie =>
        ({ shardIds := x.fst.layout.shardIds, own := x.fst.own,
           prev := (x.2.fst.find keyBwState).getD none, statuses := x.fst.statuses,
           requests := x.fst.requests, prevBlockHash := x.fst.prevBlockHash } : SchedIn)) :=
    fun cs => zip_map_congr3 _ (fun _ _ _ _ => rfl) cs _ _ hf
  unfold schedInsD0
  simp only [hk, hw₁, hw₂, ht₁, ht₂, bind, Except.bind, pure, Except.pure, e1, e2]

theorem chachaWords_congr {cb wb₁ wb₂ : Bytes} (h : schedInsD0 cb wb₁ = schedInsD0 cb wb₂) :
    chachaWords cb wb₁ = chachaWords cb wb₂ := by
  unfold chachaWords
  rw [h]

end

/-! ## `FactorComplete` -/

/-- **`FactorComplete`**: every witness the amended checker accepts admits semantic views
`GoodV3` (with the native hint and prepared statement). -/
theorem factorComplete : FactorComplete := by
  intro B cb wb h
  have ha := ((relD0a_iff B cb wb).mpr h)
  have ha2 := ha.2.2.1
  unfold a2 at ha2
  cases hk : walkD0 cb with
  | error err => simp only [hk, Bool.false_eq_true] at ha2
  | ok k =>
  cases hw : decodeW wb with
  | error err => simp only [hk, hw, Bool.false_eq_true] at ha2
  | ok w =>
  obtain ⟨m,steps,last,hm,ht,hv,hlen,_,hcap,hf⟩ := checkD0a_native_trace hk hw h
  obtain ⟨p,hgood⟩ := good_of_native hk hw h hm ht hv hcap hf
  -- the decoded witness file and the native facts behind the reconstruction's shape
  have hc := h
  unfold checkD0a at hc
  obtain ⟨u,hc,_⟩ := ReexecV3D0.bind_ok' hc
  cases u
  obtain ⟨_,_,_,_,hcount,_⟩ := checkD0_native_steps hk hw hc
  obtain ⟨raw,codes,hfile,hd,hraw,hepoch,hinner,hhash⟩ := checkD0_witness_fields hk hw hc
  have hsize := nativeExecutionViews_witness_size hd hm hv hcount hf hcap hepoch hinner hhash
  have hshape := nativeExecutionViews_shape hk hd hraw hm hv hcount hf hcap hepoch
    (Nat.le_trans hsize hraw)
  obtain ⟨htr, htrN⟩ := tries_reconstructed hk hw hd hm hv hcount hf hcap hshape
  let x := nativeExecutionViews k w m steps
  -- A7 via A11 on the original witness
  have h11 : unfoldBytesN cb wb = unfoldBytes cb wb := by
    simpa only [a11, beq_iff_eq] using ha.2.2.2.2.2.2.2.2
  have h7 : unfoldBytes cb wb ≤ B := by
    simpa only [a7, decide_eq_true_eq] using ha.2.2.2.2.1
  have hu : unfoldBytes cb (witnessOfV3 k x) = unfoldBytesN cb wb := by
    unfold unfoldBytes unfoldBytesN
    rw [htr]
  have huN : unfoldBytesN cb (witnessOfV3 k x) = unfoldBytesN cb wb := by
    unfold unfoldBytesN
    rw [htrN]
  -- A9: same pre tries
  have h9 : chachaWords cb wb ≤ W0 := by
    simpa only [a9, decide_eq_true_eq] using ha.2.2.2.2.2.2.1
  have hlenW : (stateWitnessOfV3 k x).implicit.length = w.implicit.length := by
    simp [stateWitnessOfV3, hcount]
  have hnat := triesD0_native_result hk hw hm hv
  have hN := triesD0N_native_result hk hw hm hv
  have hfst : ((m.pre,rebuildPost (revealedStore m.pre) m.result.trie
      (mainKeys (appliedReceipts k w) m.bufferedShards)) :: unfoldedPairsN steps).map Prod.fst =
      ((m.pre,rebuildPost w.main.values m.result.trie
      (mainKeys (appliedReceipts k w) m.bufferedShards)) :: unfoldedPairs steps).map Prod.fst := by
    simp [unfoldedPairsN, unfoldedPairs, List.map_map, Function.comp_def]
  have hw9 : chachaWords cb (witnessOfV3 k x) = chachaWords cb wb :=
    chachaWords_congr (schedInsD0_congr hk (decodeW_witnessOfV3 hshape) hw hlenW
      (htr.trans hN) hnat hfst)
  refine ⟨k, nativeHint k w m, p, x, hgood ?_ ?_ ?_⟩
  · rw [hu, h11]; exact h7
  · rw [hw9]; exact h9
  · rw [huN, hu]

end ZkFormal.NearV3.Assembly
