import ZkFormal.NearV3.Assembly.TrieA7Total
import ZkFormal.NearV3.Assembly.TrieAll
import ZkFormal.NearV3.Assembly.TrieKeyFinal
import ZkFormal.NearV3.Assembly.TrieShaEmpty
import ZkFormal.NearV3.Assembly.TrieDigestTrie
import ZkFormal.NearV3.Assembly.TrieDigestUps
import ZkFormal.NearV3.Assembly.TrieA7Bal
import ZkFormal.NearV3.Assembly.TrieA7SizeBal
import ZkFormal.NearV3.Assembly.TrieUpb
import ZkFormal.NearV3.Assembly.TrieUpsMemd
import ZkFormal.NearV3.Assembly.TrieUpsRoot
import ZkFormal.NearV3.Assembly.TrieComplete
import ZkFormal.NearV3.Assembly.TrieShared
import ZkFormal.NearV3.Assembly.TrieVslotNative
import ZkFormal.NearV3.Assembly.RenderV3A7
import ZkFormal.NearV3.Assembly.RenderV3RcptLayout
import ZkFormal.NearV3.Assembly.RenderV3RcptSide

/-!
# ZkFormal.NearV3.Assembly.TrieSide — the trie side of `CompleteV3Stmt` for an accepted witness

**`trie_side`**: for an accepted witness `A : AcceptedV3 cb wb` (the receipt side's native choice), given the
receipt/source SHA families' bounds and the size overhead bound, there are the account replay
(`writes`, `oldPost`), the use requests `q`, the scheduler upsert witnesses `us` and the renders of tables
0, 1 (SHA bins), 2 (node + A7), 3 (head), 4 (val + A7), 5 (walk), 6 (uniq), 7 (ups + A7), 21 (size + A7)
such that every bundle `R` carrying them balances

* unconditionally: `PARENT`, `VPARENT`, `ENT`, `DIGS`, `DUP`, `EDGE`, `BMAP`, `MIDROOT`, `ROOT`, `UPB`, `MEMD`,
  `RPL`, `RPLV`;
* `SIZE` given the receipt side's `srcp` render (20); the A7 running sum fits `B0` by `TrieA7Total.a7_bound`;
* `BYTES` / `DIGEST` given the codec (11) and receipt/source (16, 17, 20, 23) identities (`hcodec`/`hrest`,
  other lanes), with `X := ns.flatMap postSlotDigests` on the `DIGEST` side;
* `VSLOT` given the receipt side's `acct` render (17) and that its native account views are those of THIS
  `oldPost`;
* `KEYNIB` / `FINAL` given the receipt side's `rcpt` (16) / `qv` (22) renders and `RcptKeys` / `RcptFinal`.
-/

namespace ZkFormal.NearV3.Assembly.TrieSide

open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3 ZkFormal.NearV3.Assembly
  Render Render.UpsGen Rcpt.Candidates Rcpt.Candidates.NodePostUpdate ZkFormal.NearV3.UnfoldA7 TrieA7

/-- The received A7 totals of the size table: rows `0, 1, 2`. -/
def yA7 (a b c : Nat) : Nat → Nat := fun i => if i = 0 then a else if i = 1 then b else if i = 2 then c else 0

theorem sizeU_yA7 (a b c : Nat) : ∀ r, sizeU (yA7 a b c) r ≤ a + b + c
  | 0 => by simp [sizeU, yA7]; omega
  | 1 => by simp [sizeU, yA7, List.range_succ]
  | 2 => by simp [sizeU, yA7, List.range_succ]; omega
  | r + 3 => by
    have ih := sizeU_yA7 a b c (r + 2)
    have : sizeU (yA7 a b c) (r + 3) = sizeU (yA7 a b c) (r + 2) := by
      simp only [sizeU, List.range_succ (n := r + 3), List.map_append, List.sum_append, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil]
      simp [yA7]
    omega

/-- **The size premise in its exact form** (lead decision 2026-10-12): for every account replay the
trie side may export, the overhead, the honest non-duplicate node and non-empty non-duplicate value
bytes, and the source table's `srcpSize` fit `8 MiB` — given that node + value bytes fit `B0`
(`TrieA7Total.size_base`).  Only `SizeOk.tot` uses it.  Implied by the earlier coarse premise
(`sizeBudget_of_coarse`). -/
def SizeBudget {cb wb : Bytes} (A : AcceptedV3 cb wb) : Prop :=
  ∀ (writes : List (List Nat × Bytes)) (oldPost : PTrie) (q : UseRequests),
    SizedAccountRun A.m.pre writes oldPost → KeysFinal A.k A.w A.m writes oldPost →
    ((((TrieNative.nodes A.m A.steps oldPost writes q).filter fun s => !s.dup).map
        fun s => (s.v.ser false).length).sum +
      (((TrieNative.vals A.m A.steps).filter fun e => !e.vz && !e.dup).map ValE.len).sum ≤ 2000000) →
    ovhNat A.pub + (((TrieNative.nodes A.m A.steps oldPost writes q).filter fun s => !s.dup).map
        fun s => (s.v.ser false).length).sum +
      (((TrieNative.vals A.m A.steps).filter fun e => !e.vz && !e.dup).map ValE.len).sum +
      srcpSize (SrcpGen.blocksOfProofs A.srcps) ≤ 8388608

theorem sizeBudget_of_coarse {cb wb : Bytes} (A : AcceptedV3 cb wb)
    (h : ovhNat A.pub + 2000000 + srcpSize (SrcpGen.blocksOfProofs A.srcps) ≤ 8388608) : SizeBudget A := by
  intro writes oldPost q _ _ hb
  omega

/-- **The trie side of `CompleteV3Stmt`**, size premise in its exact form (`SizeBudget`). -/
theorem trie_side_exact {cb wb : Bytes} (A : AcceptedV3 cb wb)
    (receipt source : List Sha.Gen.Msg)
    (hrr : (Sha.Gen.honestRows receipt).length ≤ 1373299)
    (hpr : (Sha.Gen.honestRows source).length ≤ 2257792)
    (hsm : ∀ M ∈ source, (Sha.Gen.msgRows M).length ≤ 35)
    (hbr : ∀ M ∈ receipt, ∀ x ∈ M.bytes, x < 256) (hbs : ∀ M ∈ source, ∀ x ∈ M.bytes, x < 256)
    (hovh : SizeBudget A) :
    ∃ (writes : List (List Nat × Bytes)) (oldPost : PTrie) (q : UseRequests) (us : List SchedulerUpsertWitness)
      (r0 : TableRenderV3 A.pub 0 (by decide)) (r1 : TableRenderV3 A.pub 1 (by decide))
      (r2 : TableRenderV3 A.pub 2 (by decide)) (r3 : TableRenderV3 A.pub 3 (by decide))
      (r4 : TableRenderV3 A.pub 4 (by decide)) (r5 : TableRenderV3 A.pub 5 (by decide))
      (r6 : TableRenderV3 A.pub 6 (by decide)) (r7 : TableRenderV3 A.pub 7 (by decide))
      (r21 : TableRenderV3 A.pub 21 (by decide)),
      SizedAccountRun A.m.pre writes oldPost ∧ KeysFinal A.k A.w A.m writes oldPost ∧ (∀ u ∈ us, u.Valid) ∧
      CallPin A.k A.m A.steps us ∧
      (∃ (Js : List UpsInst) (hok : UpsRenderOk Js), r7 = upsRenderV3 A.pub Js hok ∧
        ExtOf r7.tf (upsTraffic (UpsRows.viewOf (upsTraceAligned Js) T_UPS (segsOf Js))) ∧
        Js.map (fun I => (I.tau, I.v)) = us.mapIdx (fun i u => (i, u.value.map UInt8.toNat)) ∧
        Js.map Assembly.UpsS0F.s0fOf = (A.m.pre :: A.steps.map ImplicitStepV3.pre).mapIdx
          (fun i t => Assembly.UpsS0F.s0fPair ((A.m.pre :: A.steps.map ImplicitStepV3.pre).take i) t)) ∧
      -- lane v3-render-vbytes: the value render's base traffic (for `VBYTES`)
      ExtOf r4.tf (valTraffic (TrieNative.vals A.m A.steps)) ∧
      ∀ R : RenderBundleV3 A.pub,
        R ⟨0, by decide⟩ = r0 → R ⟨1, by decide⟩ = r1 → R ⟨2, by decide⟩ = r2 → R ⟨3, by decide⟩ = r3 →
        R ⟨4, by decide⟩ = r4 → R ⟨5, by decide⟩ = r5 → R ⟨6, by decide⟩ = r6 → R ⟨7, by decide⟩ = r7 →
        R ⟨21, by decide⟩ = r21 →
        (R.BalancedAt B_PARENT ∧ R.BalancedAt B_VPARENT ∧ R.BalancedAt B_ENT ∧ R.BalancedAt B_DIGS ∧
          R.BalancedAt B_DUP ∧ R.BalancedAt B_EDGE ∧ R.BalancedAt B_BMAP ∧ R.BalancedAt B_MIDROOT ∧
          R.BalancedAt B_ROOT ∧ R.BalancedAt B_UPB ∧ R.BalancedAt B_MEMD ∧ R.BalancedAt B_RPL ∧
          R.BalancedAt B_RPLV) ∧
        (R ⟨20, by decide⟩ = A.rcptRenders.srcp → R.BalancedAt B_SIZE) ∧
        ((∀ m, cnt ((R.tf 11).sends B_BYTES) m = cnt (Sha.Gen.expectedBytes (schedulerSanityJobs 0 us)) m) →
          (∀ m, cnt ((R.tf 16).sends B_BYTES) m + cnt ((R.tf 17).sends B_BYTES) m +
              cnt ((R.tf 20).sends B_BYTES) m + cnt ((R.tf 23).sends B_BYTES) m =
            cnt (Sha.Gen.expectedBytes (receipt ++ source)) m + ZkFormal.V2.pubCount nearAirV3 A.pub B_BYTES false m) →
          R.BalancedAt B_BYTES) ∧
        ((∀ m, cnt ((R.tf 11).recvs B_DIGEST) m = cnt (Sha.Gen.expectedDigests (schedulerSanityJobs 0 us)) m) →
          (∀ m, cnt ((R.tf 16).recvs B_DIGEST) m + cnt ((R.tf 20).recvs B_DIGEST) m +
              cnt ((R.tf 23).recvs B_DIGEST) m +
              cnt ((TrieNative.nodes A.m A.steps oldPost writes q).flatMap postSlotDigests) m =
            cnt (Sha.Gen.expectedDigests (receipt ++ source)) m) →
          R.BalancedAt B_DIGEST) ∧
        (R ⟨17, by decide⟩ = A.rcptRenders.acct →
          nativeAccountViews A.m.pre oldPost (appliedReceipts A.k A.w) = some A.accts → R.BalancedAt B_VSLOT) ∧
        (R ⟨16, by decide⟩ = A.rcptRenders.rcpt → R ⟨22, by decide⟩ = A.rcptRenders.qv →
          TrieKeyFinal.RcptKeys (RcptSkeleton.rcptTrafficB A.pub A.rcptInput) (appliedReceipts A.k A.w) →
          TrieKeyFinal.RcptFinal (RcptSkeleton.rcptTrafficB A.pub A.rcptInput)
            ((A.m.pre, A.m.result.trie) :: A.steps.map (fun s => (s.pre, s.post))) (appliedReceipts A.k A.w) →
          R.BalancedAt B_KEYNIB ∧ R.BalancedAt B_FINAL) := by
  obtain ⟨writes, oldPost, insts, ws, hr, hkf, ⟨v, hvv, hvr, hws⟩, ⟨Rw, hRw⟩, horigin, hsha, hshaP, ha7, hedges, hbmaps,
    hall⟩ := TrieAll.trie_all_of A.hk A.hw A.h A.hm A.hv
      (Candidates.NativeQueueIds.resolve A.m.pre A.qvVals (A.steps.map ImplicitStepV3.pre)) A.pub
  have hW := TrieUpb.keys_length (TrieUpsNative.upsRanked ws insts) T_UPS
  obtain ⟨⟨hn, hval, Rh, Ru, hextN, hRh, hextV, hRu⟩, hups, hP, hVP, hE, hD, hU, hedge, hbmap, hmid, hlens, hroot1,
    hroot2, hupb, hmemd⟩ := hall _ hW
  have hcap := TrieA7Cap.rowCap_of_upsSha hsha
  obtain ⟨hok, hextU⟩ := hups hcap
  generalize hq : TrieUpsNative.useReq ws insts (Candidates.PhysicalWindowRequests.keys
    (upsTraceAligned (TrieUpsNative.upsRanked ws insts)) T_UPS) = q at *
  generalize hJs : TrieUpsNative.upsRanked ws insts = Js at *
  obtain ⟨S, SV, hS, hSV⟩ := TrieA7.a7_perm_native A.m A.steps oldPost writes insts ws q horigin hn hval
  have hA7 := TrieA7Total.a7_bound (ws := ws) ha7 hn hval hS hSV
  have hbase := TrieA7Total.size_base (oldPost := oldPost) (writes := writes) (q := q) ha7
  obtain ⟨us, hpin, htv, hs0, husv, hrows, hsched⟩ := TrieDigestUps.ups_sha_scheduler_pin hshaP
  rw [hJs] at hS hSV hA7
  have hqe : q.edges.length < Algebra.P := by rw [← hq]; exact hedges
  have hqb : q.bmaps.length < Algebra.P := by rw [← hq]; exact hbmaps
  have hqw : q.windows.length < Algebra.P := by rw [← hq]; exact hW
  obtain ⟨b0, b1, h0, h1, t0, t1, pb, pd, hnat⟩ := TrieShaEmpty.sha_bins_ofE A.hk A.hw A.h A.hm A.hv oldPost writes q
    hqe hqb hqw hval.wf us hrows receipt source hrr hpr hsm hbr hbs A.pub
  -- the size render
  let ns := TrieNative.nodes A.m A.steps oldPost writes q
  let es := TrieNative.vals A.m A.steps
  let bs := SrcpGen.blocksOfProofs A.srcps
  let yN := yA7 (nodeA7Total ns S) (valA7Total es SV) (upsA7Total Js)
  have hA7' : nodeA7Total ns S + valA7Total es SV + upsA7Total Js ≤ 2000000 := hA7
  have hbase' : ((ns.filter fun s => !s.dup).map fun s => (s.v.ser false).length).sum +
      ((es.filter fun e => !e.vz && !e.dup).map ValE.len).sum ≤ 2000000 := hbase
  have hB : ∀ r, r < (sizeTraceAligned A.pub (honestSizeV ns es bs)).height T_SIZE →
      (sizeTraceAligned A.pub (honestSizeV ns es bs)).cell T_SIZE r ZkFormal.NearV3.SizeV3.la = 1 →
      sizeU yN r ≤ UnfoldA7.B0 := by
    intro r _ _
    have := sizeU_yA7 (nodeA7Total ns S) (valA7Total es SV) (upsA7Total Js) r
    exact Nat.le_trans this hA7'
  have hSizeOk : SizeOk A.pub (honestSizeV ns es bs) := by
    constructor
    · show _ + _ ≤ 3000000
      exact Nat.le_trans hbase' (by decide)
    · show ovhNat A.pub + ((ns.filter fun s => !s.dup).map fun s => (s.v.ser false).length).sum +
          ((es.filter fun e => !e.vz && !e.dup).map ValE.len).sum + srcpSize bs ≤ 8388608
      exact hovh writes oldPost q hr hkf hbase'
  refine ⟨writes, oldPost, q, us, shaRenderV3 A.pub 0 (by decide) b0 h0, shaRenderV3 A.pub 1 (by decide) b1 h1,
    nodeRenderV3 A.pub ns hn (selN ns S), Rh, valRenderV3 A.pub es hval (selV es SV), Rw, Ru,
    upsRenderV3 A.pub Js hok, sizeRenderV3 A.pub _ hSizeOk yN hB, hr, hkf, husv, hpin,
    ⟨Js, hok, rfl, hextU, by rw [← hJs]; exact htv _, by rw [← hJs]; exact hs0 _⟩, hextV _, ?_⟩
  intro R e0 e1 e2 e3 e4 e5 e6 e7 e21
  have e2' : R ⟨T_NODE, by decide⟩ = nodeRenderV3 A.pub ns hn (selN ns S) := e2
  have e3' : R ⟨T_HEAD, by decide⟩ = Rh := e3
  have e4' : R ⟨T_VAL, by decide⟩ = valRenderV3 A.pub es hval (selV es SV) := e4
  have e5' : R ⟨T_WALK, by decide⟩ = Rw := e5
  have e6' : R ⟨T_UNIQ, by decide⟩ = Ru := e6
  have e7' : R ⟨T_UPS, by decide⟩ = upsRenderV3 A.pub Js hok := e7
  have e21' : R ⟨T_SIZE, by decide⟩ = sizeRenderV3 A.pub _ hSizeOk yN hB := e21
  have fN : ExtOf (R ⟨T_NODE, by decide⟩).tf (nodeTraffic3 ns) := by rw [e2']; exact hextN _
  have fH : (R ⟨T_HEAD, by decide⟩).tf = headTraffic (TrieNative.heads A.m A.steps oldPost writes q.edges) := by
    rw [e3']; exact hRh
  have fV : ExtOf (R ⟨T_VAL, by decide⟩).tf (valTraffic es) := by rw [e4']; exact hextV _
  have fW : (R ⟨T_WALK, by decide⟩).tf = walkTraffic3 (rankWalks [] ws) := by rw [e5']; exact hRw
  have fQ : (R ⟨T_UNIQ, by decide⟩).tf = uniqTraffic (uniqEntries (TrieUniqDup.uniqNative A.m A.steps)) := by
    rw [e6']; exact hRu
  have fU : ExtOf (R ⟨T_UPS, by decide⟩).tf (upsTraffic (UpsRows.viewOf (upsTraceAligned Js) T_UPS (segsOf Js))) := by
    rw [e7']; exact hextU
  have trN : (R ⟨T_NODE, by decide⟩).tr = nodeA7Trace ns T_NODE (selN ns S) := by rw [e2']; rfl
  have trV : (R ⟨T_VAL, by decide⟩).tr = valA7Trace es T_VAL (selV es SV) := by rw [e4']; rfl
  have trU : (R ⟨T_UPS, by decide⟩).tr = upsA7Trace Js T_UPS := by rw [e7']; rfl
  have f0 : (R ⟨0, by decide⟩).tf = shaBinTraffic b0 := by rw [e0]; exact t0
  have f1 : (R ⟨1, by decide⟩).tf = shaBinTraffic b1 := by rw [e1]; exact t1
  obtain ⟨hpT, hpF, hchain⟩ := TrieUpsRoot.root_endpoints_accepted A.hk A.hw A.h A.hm A.hv A.hp A.prepared_lt_P
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · exact (R.balancedAt_trie_core ns _ es _ fN fH fV fQ hP hVP hE hD hU).1
  · exact (R.balancedAt_trie_core ns _ es _ fN fH fV fQ hP hVP hE hD hU).2.1
  · exact (R.balancedAt_trie_core ns _ es _ fN fH fV fQ hP hVP hE hD hU).2.2.1
  · exact (R.balancedAt_trie_core ns _ es _ fN fH fV fQ hP hVP hE hD hU).2.2.2.1
  · exact (R.balancedAt_trie_core ns _ es _ fN fH fV fQ hP hVP hE hD hU).2.2.2.2
  · exact R.balancedAt_edge ns _ (rankWalks [] ws) Js hok fN fH fW fU hedge
  · exact R.balancedAt_bmap ns (rankWalks [] ws) Js hok fN fW fU hbmap
  · exact R.balancedAt_midroot _ Js hok fH fU (fun I hI => (hlens I hI).1) hmid
  · exact R.balancedAt_root _ Js hok fH fU (fun I hI => (hlens I hI).2) _ _ _ _ hpT hpF hroot1 hroot2 hchain
  · exact TrieUpb.RenderBundleV3.balancedAt_upb R ns Js fN fU (hupb rfl hcap)
  · exact TrieUpsMemd.RenderBundleV3.balancedAt_memd R Js hok fU hmemd
  · exact R.balancedAt_rpl ns hn S Js hok trN trU hS
  · exact R.balancedAt_rplv es hval SV Js hok trV trU hSV
  · intro e20
    have hfn : (R ⟨T_NODE, by decide⟩).tf = Traffic.append (nodeTraffic3 ns)
        (traceTraffic UnfoldA7.Node.interactions (nodeA7Trace ns T_NODE (selN ns S)) T_NODE A.pub) := by rw [e2']; rfl
    have hfv : (R ⟨T_VAL, by decide⟩).tf = Traffic.append (valTraffic es)
        (traceTraffic UnfoldA7.Val.interactions (valA7Trace es T_VAL (selV es SV)) T_VAL A.pub) := by rw [e4']; rfl
    have hfs : (R ⟨T_SIZE, by decide⟩).tf = Traffic.append (sizeTraffic (honestSizeV ns es bs))
        (traceTraffic UnfoldA7.Size.interactions (sizeA7Trace A.pub (honestSizeV ns es bs) T_SIZE yN) T_SIZE A.pub) := by
      rw [e21']; rfl
    have hfp : (R.tf T_SRCP).sends B_SIZE = (srcpTraffic bs).sends B_SIZE := by
      have : R.tf T_SRCP = (R ⟨20, by decide⟩).tf := by
        simp only [RenderBundleV3.tf]; rfl
      rw [this, e20]; rfl
    exact R.balancedAt_size ns hn S es hval SV Js hok bs yN hfn hfv trU hfs hfp (by simp [yN, yA7])
      (by simp [yN, yA7]) (by simp [yN, yA7])
  · intro hc hrest
    exact TrieShaBus.RenderBundleV3.balancedAt_bytes R ns es (TrieShaEmpty.nativeShaJobsE ns es) Js hok us receipt source b0 b1
      f0 f1 pb fN fV fU hnat (by rw [← hJs]; exact (hsched (ws.flatMap (·.steps))).1) hc hrest
  · intro hc hrest
    have hnode := TrieDigestTrie.node_head_digests A.hm A.hv hr q q.edges hn
    have hupsD : ((CompactPhysicalDigests.compactGeneratedDigests Js).map Msg.toFp).Perm
        ((Sha.Gen.expectedDigests (schedulerShaJobs 0 us)).map Msg.toFp) := by
      have h := (hsched (ws.flatMap (·.steps))).2
      rw [← hJs]
      exact h
    have htrie := TrieDigestTrie.RenderBundleV3.htrie_of R ns (TrieNative.heads A.m A.steps oldPost writes q.edges)
      Js hok us (TrieShaEmpty.nativeShaJobsE ns es) (ns.flatMap postSlotDigests) fN fH fU hnode hupsD
    exact TrieShaBus.RenderBundleV3.balancedAt_digest R (TrieShaEmpty.nativeShaJobsE ns es) us receipt source b0 b1
      (ns.flatMap postSlotDigests) f0 f1 pd htrie hc hrest
  · intro e17 hviews
    have fA : (R ⟨T_ACCT, by decide⟩).tf = acctV3Traffic A.accts := by
      have e17' : R ⟨T_ACCT, by decide⟩ = A.rcptRenders.acct := e17
      rw [e17']; rfl
    exact R.balancedAt_vslot ns A.accts fN fA (fun msg => TrieShared.vslot_native A.hm hr hkf hviews A.steps q msg)
  · intro e16 e22 hk hf
    exact TrieKeyFinal.keynib_final_accepted A R hvv hvr hws fW e16 e22 hk hf

/-- **The trie side of `CompleteV3Stmt`** (coarse size premise; corollary of `trie_side_exact`). -/
theorem trie_side {cb wb : Bytes} (A : AcceptedV3 cb wb)
    (receipt source : List Sha.Gen.Msg)
    (hrr : (Sha.Gen.honestRows receipt).length ≤ 1373299)
    (hpr : (Sha.Gen.honestRows source).length ≤ 2257792)
    (hsm : ∀ M ∈ source, (Sha.Gen.msgRows M).length ≤ 35)
    (hbr : ∀ M ∈ receipt, ∀ x ∈ M.bytes, x < 256) (hbs : ∀ M ∈ source, ∀ x ∈ M.bytes, x < 256)
    (hovh : ovhNat A.pub + 2000000 + srcpSize (SrcpGen.blocksOfProofs A.srcps) ≤ 8388608) :
    ∃ (writes : List (List Nat × Bytes)) (oldPost : PTrie) (q : UseRequests) (us : List SchedulerUpsertWitness)
      (r0 : TableRenderV3 A.pub 0 (by decide)) (r1 : TableRenderV3 A.pub 1 (by decide))
      (r2 : TableRenderV3 A.pub 2 (by decide)) (r3 : TableRenderV3 A.pub 3 (by decide))
      (r4 : TableRenderV3 A.pub 4 (by decide)) (r5 : TableRenderV3 A.pub 5 (by decide))
      (r6 : TableRenderV3 A.pub 6 (by decide)) (r7 : TableRenderV3 A.pub 7 (by decide))
      (r21 : TableRenderV3 A.pub 21 (by decide)),
      SizedAccountRun A.m.pre writes oldPost ∧ KeysFinal A.k A.w A.m writes oldPost ∧ (∀ u ∈ us, u.Valid) ∧
      ∀ R : RenderBundleV3 A.pub,
        R ⟨0, by decide⟩ = r0 → R ⟨1, by decide⟩ = r1 → R ⟨2, by decide⟩ = r2 → R ⟨3, by decide⟩ = r3 →
        R ⟨4, by decide⟩ = r4 → R ⟨5, by decide⟩ = r5 → R ⟨6, by decide⟩ = r6 → R ⟨7, by decide⟩ = r7 →
        R ⟨21, by decide⟩ = r21 →
        (R.BalancedAt B_PARENT ∧ R.BalancedAt B_VPARENT ∧ R.BalancedAt B_ENT ∧ R.BalancedAt B_DIGS ∧
          R.BalancedAt B_DUP ∧ R.BalancedAt B_EDGE ∧ R.BalancedAt B_BMAP ∧ R.BalancedAt B_MIDROOT ∧
          R.BalancedAt B_ROOT ∧ R.BalancedAt B_UPB ∧ R.BalancedAt B_MEMD ∧ R.BalancedAt B_RPL ∧
          R.BalancedAt B_RPLV) ∧
        (R ⟨20, by decide⟩ = A.rcptRenders.srcp → R.BalancedAt B_SIZE) ∧
        ((∀ m, cnt ((R.tf 11).sends B_BYTES) m = cnt (Sha.Gen.expectedBytes (schedulerSanityJobs 0 us)) m) →
          (∀ m, cnt ((R.tf 16).sends B_BYTES) m + cnt ((R.tf 17).sends B_BYTES) m +
              cnt ((R.tf 20).sends B_BYTES) m + cnt ((R.tf 23).sends B_BYTES) m =
            cnt (Sha.Gen.expectedBytes (receipt ++ source)) m + ZkFormal.V2.pubCount nearAirV3 A.pub B_BYTES false m) →
          R.BalancedAt B_BYTES) ∧
        ((∀ m, cnt ((R.tf 11).recvs B_DIGEST) m = cnt (Sha.Gen.expectedDigests (schedulerSanityJobs 0 us)) m) →
          (∀ m, cnt ((R.tf 16).recvs B_DIGEST) m + cnt ((R.tf 20).recvs B_DIGEST) m +
              cnt ((R.tf 23).recvs B_DIGEST) m +
              cnt ((TrieNative.nodes A.m A.steps oldPost writes q).flatMap postSlotDigests) m =
            cnt (Sha.Gen.expectedDigests (receipt ++ source)) m) →
          R.BalancedAt B_DIGEST) ∧
        (R ⟨17, by decide⟩ = A.rcptRenders.acct →
          nativeAccountViews A.m.pre oldPost (appliedReceipts A.k A.w) = some A.accts → R.BalancedAt B_VSLOT) ∧
        (R ⟨16, by decide⟩ = A.rcptRenders.rcpt → R ⟨22, by decide⟩ = A.rcptRenders.qv →
          TrieKeyFinal.RcptKeys (RcptSkeleton.rcptTrafficB A.pub A.rcptInput) (appliedReceipts A.k A.w) →
          TrieKeyFinal.RcptFinal (RcptSkeleton.rcptTrafficB A.pub A.rcptInput)
            ((A.m.pre, A.m.result.trie) :: A.steps.map (fun s => (s.pre, s.post))) (appliedReceipts A.k A.w) →
          R.BalancedAt B_KEYNIB ∧ R.BalancedAt B_FINAL) := by
  obtain ⟨writes, oldPost, q, us, r0, r1, r2, r3, r4, r5, r6, r7, r21, hr, hkf, hus, -, -, -, hall⟩ :=
    trie_side_exact A receipt source hrr hpr hsm hbr hbs (sizeBudget_of_coarse A hovh)
  exact ⟨writes, oldPost, q, us, r0, r1, r2, r3, r4, r5, r6, r7, r21, hr, hkf, hus, hall⟩

end ZkFormal.NearV3.Assembly.TrieSide
