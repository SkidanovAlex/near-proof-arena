import ZkFormal.NearV3.Assembly.NativeUnfold
import ZkFormal.NearV3.Assembly.LinkCore
import ZkFormal.NearV3.Link.UnfoldRefine

/-!
# ZkFormal.NearV3.Assembly.A7Native — the native half of `unfoldedBytes` (RelD0a A7)

`unfoldBytes cb w` sums `unfoldedBytesT pre + unfoldedBytesT post` over the native tries of
`triesD0` (`(m.pre, m.result.trie)` and the implicit `(pre_τ, post_τ)`).  This module bounds it by
the **record trees** of the views:

* `triesD0_xOf` — for the reconstruction `x` with `D0Shape`, `SourceSemanticsV3.applied` and the
  main-store bound, any `m.Valid k x` with its implicit run `ImplicitRunV3` gives
  `triesD0 cb (witnessOfV3 k x) = .ok ((m.pre, m.result.trie) :: unfoldedPairs steps)`
  (`NativeUnfold.triesD0_native_result`);
* `implicit_refined` — the native implicit pre trie of instance `τ ∈ 1..K` refines the pre record
  tree `Fpre r τ` and its native post trie refines the record post tree
  `Qrec tr r τ = upsert (Tpost r τ) [0,15] (sv τ)` (the `upsV3` upsert, `LinkSched.upsLink_holds`);
* `main_refined` — the same for the main instance (`τ = 0`) and **any** `m.Valid k x`;
* **`unfold_le_records`** — `unfoldBytes cb (witnessOfV3 k x) ≤ Σ_{τ ≤ K} (U (Fpre r τ) + U (Qrec tr r τ))`
  (`Link3.unfoldedBytesT_le_of_refinedBy`).

What remains for the field is record-level only (`A7RecordBound`):
`Σ_{τ ≤ K} (U (Fpre r τ) + U (Qrec tr r τ)) ≤ nodeA7Sum + valA7Sum + Σ a7S` (then `A7Bound.a7_total_le`).
-/

namespace ZkFormal.NearV3.Assembly

open NearSpec NearSpecV3

namespace A7Native

/-! ## The native tries of the reconstruction -/

theorem decode_of_shape {k : WalkD0} {x : ExtV3} (hs : V3.D0Shape (stateWitnessOfV3 k x)) :
    decodeW (witnessOfV3 k x) = .ok (stateWitnessOfV3 k x) := by
  unfold decodeW witnessOfV3
  rw [V3.decodeWitnessFile_encode _ hs]
  simpa only [bind, Except.bind] using V3.decodeStateWitness_encode _ hs

theorem nativeValid_of {k : WalkD0} {x : ExtV3} {m : MainExecutionV3} (hm : m.Valid k x)
    (happ : appliedReceipts k (stateWitnessOfV3 k x) = x.applied)
    (hsb : ((x.store 0).map List.length).foldl (· + ·) 0 ≤ 3000000) :
    m.NativeValid k (stateWitnessOfV3 k x) where
  block := hm.block
  previous := hm.previous
  buffered := hm.buffered
  pre := by rw [happ]; exact hm.pre
  preRoot := hm.preRoot
  run := by rw [happ]; exact hm.run
  postRoot := hm.postRoot
  storeBytes := hsb

/-- **The native tries of the reconstruction.** -/
theorem triesD0_xOf {cb : Bytes} {k : WalkD0} {x : ExtV3} {m : MainExecutionV3} {last : Bytes}
    (hk : walkD0 cb = .ok k) (hs : V3.D0Shape (stateWitnessOfV3 k x))
    (happ : appliedReceipts k (stateWitnessOfV3 k x) = x.applied)
    (hsb : ((x.store 0).map List.length).foldl (· + ·) 0 ≤ 3000000) (hm : m.Valid k x)
    (hi : ImplicitRunV3 k x 1 m.result.trie.hashOf k.implicitBlks last) :
    ∃ steps, ImplicitTraceValid k m.result.trie.hashOf (implicitPairs x 1 k.implicitBlks) steps last ∧
      triesD0 cb (witnessOfV3 k x) = .ok ((m.pre, m.result.trie) :: unfoldedPairs steps) := by
  have hl := hi.witness_loop
  obtain ⟨steps, -, hv⟩ := checkedImplicitLoop_trace k _ _ _ hl
  refine ⟨steps, ?_, triesD0_native_result hk (decode_of_shape hs) (nativeValid_of hm happ hsb) hv⟩
  rwa [stateWitnessOfV3_implicit_pairs] at hv

theorem itv_nil_inv {k : WalkD0} {root last : Bytes} {steps : List ImplicitStepV3}
    (h : ImplicitTraceValid k root [] steps last) : steps = [] := by
  cases h; rfl

theorem itv_cons_inv {k : WalkD0} {root last : Bytes} {b : Blk} {t : Transition}
    {rest : List (Blk × Transition)} {steps : List ImplicitStepV3}
    (h : ImplicitTraceValid k root ((b, t) :: rest) steps last) :
    ∃ steps' post, applyMissingChunk prims
        (blockCtx k.L k.H.shardId k.slotB2.gasLimit b b.hdr.nextGasPrice)
        (partialTrie t.values root [keyDelayedIdx, keyBwState]) = .ok post ∧
      post.hashOf = t.postStateRoot ∧ ImplicitTraceValid k post.hashOf rest steps' last ∧
      steps = ⟨b, t, root, partialTrie t.values root [keyDelayedIdx, keyBwState], post⟩ :: steps' := by
  cases h with
  | cons _ _ _ _ steps' post _ run rc tail => exact ⟨steps', post, run, rc, tail, rfl⟩

theorem implicitPairs_cons (x : ExtV3) (τ : Nat) (b : Blk) (bs : List Blk) :
    implicitPairs x τ (b :: bs) = (b, x.transition τ) :: implicitPairs x (τ + 1) bs := by
  simp only [implicitPairs, List.zipIdx_cons, List.map_cons]

/-! ## The record post trees and the implicit instances -/

section Rec
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.NearV3 ZkFormal.NearV3.Link3
  ZkFormal.NearV3.UpsRows LinkImplicit

/-- The post-value record tree of instance `τ` (the tree `upsV3` upserts into). -/
noncomputable def Tpost (r : V3Records) (τ : Nat) : PTrie :=
  fullTree (Rpost r.nodes r.values) (Vpost r.nodes r.values (fun i => toB (LinkVPost.pnOf r.accts i)))
    (headAt r.heads τ).rid

/-- **The record post tree of instance `τ`**: the `[0,15]` upsert of `Tpost r τ` by the scheduler's
new value `sv τ` (`LinkSched.upsLink_holds`). -/
noncomputable def Qrec (tr : Trace Fp) (r : V3Records) (τ : Nat) : PTrie :=
  ((Tpost r τ).upsert UpsSpec.key (toB (Sched.svOf tr T_CODEC τ))).getD (.hash [])

variable {cb : NearSpec.Bytes} {h : NearSpecV3.Hint} {p : NearSpecV3.Prep} {oh : Nat}
  {tr : Trace Fp} {r : V3Records}

/-- The upsert defining `Qrec` is defined, with the `upsV3` facts. -/
theorem qrec_upsert (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < ZkFormal.Algebra.P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    {τ : Nat} (hτ : τ ≤ p.hdr.K) :
    (Tpost r τ).upsert UpsSpec.key (toB (Sched.svOf tr T_CODEC τ)) = some (Qrec tr r τ) := by
  obtain ⟨sv, rfl, -, U⟩ := LinkSched.upsLink_holds hp hsz hH T W
  obtain ⟨⟨Q, hQ, -⟩, -⟩ := U τ hτ
  unfold Qrec
  rw [show (Tpost r τ).upsert UpsSpec.key (toB (Sched.svOf tr T_CODEC τ)) = some Q from hQ]
  rfl

/-- **One implicit instance, refined**: the native pre trie refines `Fpre r τ`, and the native post
trie (any successful run on it) refines `Qrec tr r τ`. -/
theorem implicit_refined (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < ZkFormal.Algebra.P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    (Hpp : PostPreOff0 r) (Hdel : DelayedCovered p.hdr.K r)
    {x : ExtV3} (hxn : x.nodes = r.nodes) (hxv : x.values = r.values)
    {τ : Nat} (h1 : 1 ≤ τ) (hτK : τ ≤ p.hdr.K) {ctx : NearSpecV3.ApplyCtx}
    (hτ : τ < p.sched.length) (hctx : NearSpecV3.schedPub ctx = some p.sched[τ]) {post : PTrie}
    (hrun : NearSpecV3.applyMissingChunk NearSpecV3.prims ctx
      (NearSpecV3.partialTrie (x.store τ) (rootAt p r τ) [NearSpecV3.keyDelayedIdx, NearSpecV3.keyBwState])
        = .ok post) :
    (NearSpecV3.partialTrie (x.store τ) (rootAt p r τ)
      [NearSpecV3.keyDelayedIdx, NearSpecV3.keyBwState]).refinedBy (Fpre r τ) ∧
    post.refinedBy (Qrec tr r τ) := by
  have L := trieLink_of hp hsz hH T W
  obtain ⟨hh, htau⟩ := L.chain.head_mem τ hτK
  have hFeq : Tpost r τ = Fpre r τ := by
    apply tree_post_eq W.nodes W.heads W.values L.parent L.vparent (recBytes_of W L) hh
    intro e he hte hwe
    exact Hpp e he (by rw [hte, htau]; omega) hwe
  -- the scheduler step on the record tree lands on `Qrec`
  obtain ⟨f, m, fc, -, -, -, -, -, -, -, -, -, H⟩ := LinkSchedCore.schedCore_v3 hp hsz hH T W hτ
  obtain ⟨hcore, -⟩ := H
  have hQ := qrec_upsert hp hsz hH T W hτK
  have hsched : ∃ so, NearSpecV3.schedStep NearSpecV3.prims ctx (Fpre r τ) = .ok (Qrec tr r τ, so) := by
    rw [← hFeq]
    refine ⟨_, schedStep_sound ?_ hctx hcore hQ⟩
    unfold NearSpecV3.readKey Tpost
    rw [LinkVBytes.keyBwState_eq, LinkVBytes.codec_find hp hsz hH T W hτ hτK]
  obtain ⟨so, hsched⟩ := hsched
  have hbw : (Fpre r τ).find NearSpecV3.keyBwState = some (Sched.prevOf tr T_CODEC τ) := by
    rw [← hFeq, LinkVBytes.keyBwState_eq]; exact LinkVBytes.codec_find hp hsz hH T W hτ hτK
  have hdel := Hdel τ h1 hτK
  have hF : NearSpecV3.applyMissingChunk NearSpecV3.prims ctx (Fpre r τ) = .ok (Qrec tr r τ) := by
    obtain ⟨dv, hdv⟩ := Option.ne_none_iff_exists'.mp hdel
    unfold NearSpecV3.applyMissingChunk
    simp [NearSpecV3.readKey, hdv, hsched, bind, Except.bind, pure, Except.pure]
  have hkeys : ∀ k ∈ [NearSpecV3.keyDelayedIdx, NearSpecV3.keyBwState], (Fpre r τ).find k ≠ none := by
    intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl
    · exact hdel
    · rw [hbw]; simp
  obtain ⟨hr, hw, hfind⟩ := inst_pruned W L hτK _ hkeys
  have hstore : NearSpecV3.partialTrie (x.store τ) (rootAt p r τ)
      [NearSpecV3.keyDelayedIdx, NearSpecV3.keyBwState] =
      NearSpecV3.partialTrie (storeOf (Rpost r.nodes r.values) (valsOf3 r.nodes r.values) τ)
        (toB (headAt r.heads τ).pre) [NearSpecV3.keyDelayedIdx, NearSpecV3.keyBwState] := by
    simp only [ExtV3.store, ExtV3.rawStore, ExtV3.valuePosition, rootAt, partialTrie_eraseDups,
      ite_eq_left_iff.mpr (fun h => absurd hτK h), hxn, hxv]
    rfl
  rw [hstore] at hrun ⊢
  have hd' := hfind NearSpecV3.keyDelayedIdx (by simp)
  have hb' := hfind NearSpecV3.keyBwState (by simp)
  obtain ⟨P', hP', hPQ⟩ := LinkPartial.applyMissingChunk_refined hr hw
    (by rw [hd']; exact hdel) (by rw [hb', hbw]; simp) hF
  rw [hrun] at hP'
  cases hP'
  exact ⟨hr, hPQ⟩

/-- **The main record post tree is `Qrec … 0`**: the receipt core's trie family at the final value
assignment (length-preserving, agreeing with the post streams) is the `upsV3` upsert. -/
theorem tf_eq_qrec (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < ZkFormal.Algebra.P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    (h0 : 0 < p.sched.length) {o : NearSpecV3.Scheduler.Output}
    (ho : NearSpecV3.Scheduler.runCore p.sched[0] (Sched.prevOf tr T_CODEC 0) = some o)
    {v : Nat → NearSpec.Bytes} (hv : LinkTrieFam.LenOk r v)
    (hagree : ∀ e ∈ r.values, valTau r.nodes e.vid = 0 →
      v e.vid = if wrote r.nodes e.vid then toB (LinkVPost.pnOf r.accts e.vid) else toB e.bytes) :
    LinkTrieFam.Tf r 0 (schedOut o).state v = Qrec tr r 0 := by
  have L := trieLink_of hp hsz hH T W
  have hK : 0 ≤ p.hdr.K := Nat.zero_le _
  have hd := LinkTrieFam.dag_v W L hK hv
  have hFv : LinkTrieFam.Fv r 0 v = Tpost r 0 := by
    apply fullTree_vals hd ?_ hd.root_inst
    intro n nr hnr ht i hi
    obtain ⟨vr, hvr, hvt⟩ := hd.vals n nr hnr ht i hi
    simp only [LinkTrieFam.valsBy, List.getElem?_map] at hvr
    cases he : r.values[i]? with
    | none => rw [he] at hvr; cases hvr
    | some e =>
      rw [he] at hvr; cases hvr
      have hi' : i < r.values.length := (List.getElem?_eq_some_iff.mp he).1
      have he' : r.values[i] = e := (List.getElem?_eq_some_iff.mp he).2
      rw [LinkTrieFam.valOf_valsBy v hi', he', hagree e (List.mem_of_getElem? he) hvt]
      simp [valOf, Vpost, valsPost, he]
  obtain ⟨f, m, fc, -, -, -, -, -, -, -, -, -, H⟩ := LinkSchedCore.schedCore_v3 hp hsz hH T W h0
  obtain ⟨hrun, -⟩ := H
  have e := Option.some.inj (ho.symm.trans hrun)
  have hQ' : (Tpost r 0).upsert NearSpecV3.keyBwState (schedOut o).state = some (Qrec tr r 0) := by
    rw [e]; exact qrec_upsert hp hsz hH T W hK
  have hT := LinkTrieFam.Tf_upsert hp hsz hH T W h0 hK (schedOut o).state hv
  rw [hFv, hQ'] at hT
  exact (Option.some.inj hT).symm

/-- **The main instance, refined**: for any main execution of the reconstruction, the native pre
trie refines `Fpre r 0` and the native post trie refines `Qrec tr r 0`. -/
theorem main_refined (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < ZkFormal.Algebra.P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    {k : NearSpecV3.WalkD0} (hw : NearSpecV3.walkD0 cb = .ok k) (hn : h.n = (flatR r.lists).length)
    {x : ExtV3} (hxn : x.nodes = r.nodes) (hxv : x.values = r.values) (hxr : x.receipts = r.lists)
    {m : MainExecutionV3} (hm : m.Valid k x) :
    m.pre.refinedBy (Fpre r 0) ∧ m.result.trie.refinedBy (Qrec tr r 0) := by
  have L := trieLink_of hp hsz hH T W
  obtain ⟨pc, bs, hc, hbs, hfix, hgrp, K⟩ := RcptLink.mainRun_of_holdsP_q hp hsz hH T W hn
  obtain ⟨pc', hc', hb⟩ := Sched.bind_ok hp
  rw [hc] at hc'; cases hc'
  have hsched : p.sched = pc.sched := (prepBody_shape hb).2.1
  obtain ⟨h0c, hsp⟩ := LinkPrepCtx.prepClaim_sched0 hc
  have h0 : 0 < p.sched.length := by rw [hsched]; exact h0c
  have hctx : NearSpecV3.schedPub pc.ctxB2 = some p.sched[0] := by
    rw [hsp]; congr 1; simp only [hsched]
  obtain ⟨o, Q, ho, ML⟩ := LinkMainLink.mainTrieLink_holds hp hsz hH T W h0 hctx
  have hrun0 := K (LinkTrieFam.preV r) (LinkTrieFam.Tf r 0 (schedOut o).state) Q (schedOut o) ML
    (RcptLink.hroute_holds hp hsz hH T W pc hc)
    (fun oi hoi j hj => LinkFwd.hfwd_holds hp hsz hH T W pc hc h0 o ho oi hoi j hj)
  have hC := (LinkPrepCtx.prepClaim_context_of (m := m) (stateWitnessOfV3 k x) hc hw
    hm.block hm.previous).ctx
  rw [hC, ← LinkExec.applied_eq hxr] at hrun0
  -- the buffered shards of `m` are the record tree's
  obtain ⟨v0, hv0, hbs0⟩ := hbs
  obtain ⟨hprev, -, -⟩ := prepD0_root_endpoints hp hw
  have hroot0 : toB (headAt r.heads 0).pre = k.slotB2.prevStateRoot := by
    rw [L.chain.pre0, toB_toNat, hprev]
  have hst : ∀ ks, NearSpecV3.partialTrie (x.store 0) k.slotB2.prevStateRoot ks =
      NearSpecV3.partialTrie (storeOf (Rpost r.nodes r.values) (valsOf3 r.nodes r.values) 0)
        (toB (headAt r.heads 0).pre) ks := by
    intro ks
    rw [hroot0]
    simp only [ExtV3.store, ExtV3.rawStore, ExtV3.valuePosition, partialTrie_eraseDups, hxn, hxv]
    rfl
  have hbuf : (NearSpecV3.partialTrie (x.store 0) k.slotB2.prevStateRoot [NearSpecV3.keyBufferedIdx]).find
      NearSpecV3.keyBufferedIdx = some v0 := by
    have hc0 : ∀ key ∈ [NearSpecV3.keyBufferedIdx], (Fpre r 0).find key ≠ none := by
      intro key hk; simp only [List.mem_singleton] at hk; subst hk; rw [hv0]; simp
    obtain ⟨-, -, hf⟩ := inst_pruned W L (Nat.zero_le _) _ hc0
    rw [hst, hf _ (by simp), hv0]
  obtain ⟨v1, hv1, hbs1⟩ := hm.buffered
  rw [hbuf] at hv1
  cases hv1
  rw [hbs0] at hbs1
  have hbsE : bs = m.bufferedShards := by simpa using hbs1
  -- the pre trie
  have hcov := LinkTrieOk.hcov_of hp hsz hH T W h0 hxr hfix hgrp
  obtain ⟨hr, hwP, hfind⟩ := inst_pruned W L (Nat.zero_le _) _ hcov
  have hpre : m.pre = NearSpecV3.partialTrie (storeOf (Rpost r.nodes r.values) (valsOf3 r.nodes r.values) 0)
      (toB (headAt r.heads 0).pre) (NearSpecV3.mainKeys x.applied bs) := by
    rw [hm.pre, hst, hbsE]
  obtain ⟨hD, hB, hBI, hY⟩ := LinkMain.mainKeys_fixed x.applied bs
  obtain ⟨out', hout, href, -⟩ := LinkRefine.applyNewChunk_sim ⟨hr, hfind⟩ hwP
    (LinkMain.Fpre_wf W L (Nat.zero_le _)) hD hB hBI hY
    (fun v hv sh hsh y hy => by
      rw [hv0] at hv; cases hv
      rw [hbs0] at hsh; cases hsh
      exact LinkMain.mainKeys_group hy)
    (fun r hr => LinkMain.mainKeys_acct hr) (fun r hr h1 h2 => LinkMain.mainKeys_ak hr h1 h2) hrun0
  have hrun := hm.run
  rw [hpre] at hrun
  rw [hrun] at hout
  cases hout
  refine ⟨hpre ▸ hr, ?_⟩
  -- the record main output is `Qrec … 0`
  have H := LinkPostRec.recHyp_holds hp hsz hH T W
  have hinit := LinkPostRec.hinit_holds hp hsz hH T W (schedOut o).state
  have hrw := LinkPostRec.hrw_of hH T W H (schedOut o).state
  have hun := LinkPostRec.hun_of hp hsz hH T W H (schedOut o).state
  have hv : LinkTrieFam.LenOk r ((LinkTrieOk.Mdl r (schedOut o).state).valsAt
      (LinkTrieOk.Mdl r (schedOut o).state).rs.length) :=
    LinkTrieOk.lenOk_of hinit (RcptLink.RunModel.valsAt_lenPres _ _)
  have hTQ := tf_eq_qrec hp hsz hH T W h0 ho hv (by
    intro e he he0
    by_cases hw' : (LinkTrieOk.Mdl r (schedOut o).state).written e.vid = true
    · obtain ⟨hwr, hv'⟩ := hrw e.vid hw'
      simp only [hwr, hv', ↓reduceIte]
    · have hw'' : (LinkTrieOk.Mdl r (schedOut o).state).written e.vid = false := by simpa using hw'
      have hb' : (LinkTrieOk.Mdl r (schedOut o).state).valsAt
          (LinkTrieOk.Mdl r (schedOut o).state).rs.length e.vid = toB e.bytes := by
        simp only [RcptLink.RunModel.valsAt, hw'', Bool.false_eq_true, ↓reduceIte]
        obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem he
        exact LinkTrieFam.preV_at W ht
      rw [hb']
      split
      · rename_i hwr; exact (hun e he he0 hwr hw'').symm
      · rfl)
  rw [← hTQ]
  exact href

/-- **The implicit instances, summed**: the native implicit pairs from instance `τ` on are bounded by
the record trees of instances `τ, τ+1, …, K`. -/
theorem implicit_sum (hp : NearSpecV3.prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < ZkFormal.Algebra.P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    {k : NearSpecV3.WalkD0} (hw : NearSpecV3.walkD0 cb = .ok k) {m : MainExecutionV3}
    (hmb : k.blks[k.b2i]? = some m.block) (hmp : k.blks[k.b2i + 1]? = some m.previous)
    (Hpp : PostPreOff0 r) (Hdel : DelayedCovered p.hdr.K r)
    {x : ExtV3} (hxn : x.nodes = r.nodes) (hxv : x.values = r.values)
    (hxh : x.heads = xHeads (r.ups.map upsE)) :
    ∀ n τ, τ + n = p.hdr.K + 1 → 1 ≤ τ → ∀ steps last,
      ImplicitTraceValid k (rootAt p r τ) (implicitPairs x τ (k.implicitBlks.drop (τ - 1))) steps last →
      ((unfoldedPairs steps).map fun q => unfoldedBytesT q.1 + unfoldedBytesT q.2).sum ≤
        ((List.range' τ n).map fun j => unfoldedBytesT (Fpre r j) + unfoldedBytesT (Qrec tr r j)).sum := by
  have L := trieLink_of hp hsz hH T W
  obtain ⟨-, -, hKk⟩ := prepD0_root_endpoints hp hw
  intro n
  induction n with
  | zero =>
    intro τ hτ h1 steps last hv
    have hd : k.implicitBlks.drop (τ - 1) = [] := List.drop_eq_nil_of_le (by omega)
    rw [hd] at hv
    simp [implicitPairs] at hv
    rw [itv_nil_inv hv]
    simp [unfoldedPairs]
  | succ n ih =>
    intro τ hτ h1 steps last hv
    obtain ⟨j, rfl⟩ : ∃ j, τ = j + 1 := ⟨τ - 1, by omega⟩
    have hlt : j < k.implicitBlks.length := by omega
    simp only [Nat.add_sub_cancel] at hv
    rw [List.drop_eq_getElem_cons hlt, implicitPairs_cons] at hv
    obtain ⟨steps', post, hrun, hroot, htail, rfl⟩ := itv_cons_inv hv
    have hci : (schedulerContexts k m)[j + 1]? = some (NearSpecV3.blockCtx k.L k.H.shardId
        k.slotB2.gasLimit k.implicitBlks[j] k.implicitBlks[j].hdr.nextGasPrice) := by
      simp [schedulerContexts, List.getElem?_eq_getElem hlt]
    obtain ⟨sp, hsp, hpub⟩ := prepD0_context_index_of hp hw hmb hmp (j + 1) _ hci
    obtain ⟨hτs, hsp'⟩ := List.getElem?_eq_some_iff.mp hsp
    obtain ⟨hpre, hpost⟩ := implicit_refined hp hsz hH T W Hpp Hdel hxn hxv (τ := j + 1) (by omega)
      (by omega) hτs (by rw [hsp']; exact hpub) hrun
    have hnext : post.hashOf = rootAt p r (j + 1 + 1) := by
      rw [hroot]
      show x.post (j + 1) = _
      rw [post_xHeads hxh (L.chain.ups_mem (j + 1) (by omega)),
        LinkImplicit.ups_post hp hsz hH T W (by omega)]
    rw [hnext] at htail
    have hrec := ih (j + 1 + 1) (by omega) (by omega) steps' last (by simpa using htail)
    have h1' := Link3.unfoldedBytesT_le_of_refinedBy hpre
    have h2' := Link3.unfoldedBytesT_le_of_refinedBy hpost
    simp only [unfoldedPairs, List.map_cons, List.sum_cons, List.range'_succ] at hrec ⊢
    exact Nat.add_le_add (Nat.add_le_add h1' h2') hrec

/-- **`unfoldBytes` of the reconstruction is bounded by the record trees** (any dictionary `d`; the
shape and applied-receipts fields of `RestFieldsV3` as hypotheses):
`unfoldBytes cb (witnessOfV3 k (xOf r d)) ≤ Σ_{τ ≤ K} (U (Fpre r τ) + U (Qrec tr r τ))`. -/
theorem unfold_le_records (hp : NearSpecV3.prepD0 cb h = .ok p) {k : NearSpecV3.WalkD0}
    (hw : NearSpecV3.walkD0 cb = .ok k)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < ZkFormal.Algebra.P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (d : List DictionaryEntryV3) (hs : V3.D0Shape (stateWitnessOfV3 k (xOf r d)))
    (happ : appliedReceipts k (stateWitnessOfV3 k (xOf r d)) = (xOf r d).applied) :
    unfoldBytes cb (witnessOfV3 k (xOf r d)) ≤
      ((List.range (p.hdr.K + 1)).map fun τ => unfoldedBytesT (Fpre r τ) + unfoldedBytesT (Qrec tr r τ)).sum := by
  have hcount := receiptCount_of_records hp W.lists (xOf r d) rfl
  have hn : h.n = (flatR r.lists).length := by
    rw [hcount]
    simp only [ExtV3.applied, xOf, flatR, List.length_flatMap, List.length_map]
  obtain ⟨block, previous, hmb, hmp⟩ := walkD0_blocks hw
  obtain ⟨m, last, hm, hi, -⟩ :=
    RcptLink.executions_holdsP hp hsz hH T W hw hn (x := xOf r d) rfl rfl rfl rfl hmb hmp
  have hsb := mainStoreBytes_ext hp hsz hH T W (xOf r d) rfl rfl
  obtain ⟨steps, hv, htr⟩ := triesD0_xOf hw hs happ hsb hm hi
  obtain ⟨h1, h2⟩ := main_refined hp hsz hH T W hw hn (x := xOf r d) rfl rfl rfl hm
  have hroot : m.result.trie.hashOf = rootAt p r 1 := by
    rw [hm.postRoot, post0_eq hp hsz hH T W (x := xOf r d) rfl]
  rw [hroot] at hv
  have hI := implicit_sum hp hsz hH T W hw hm.block hm.previous
    (LinkPostRec.postPreOff0_holds hp hsz hH T W) (LinkDelayed.delayedCovered_holds hp hsz hH T W)
    (x := xOf r d) rfl rfl rfl p.hdr.K 1 (by omega) (Nat.le_refl 1) steps last (by simpa using hv)
  unfold unfoldBytes
  rw [htr]
  rw [List.range_eq_range', List.range'_succ]
  simp only [List.map_cons, List.sum_cons]
  exact Nat.add_le_add (Nat.add_le_add (Link3.unfoldedBytesT_le_of_refinedBy h1)
    (Link3.unfoldedBytesT_le_of_refinedBy h2)) hI

end Rec

end A7Native

end ZkFormal.NearV3.Assembly
