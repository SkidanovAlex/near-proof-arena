import ZkFormal.NearV3.Assembly.TrieKeyFinal
import ZkFormal.NearV3.Assembly.TrieUpsKeys
import ZkFormal.NearV3.Render.HonestRcptQ
import ZkFormal.NearV3.Candidates.NativeReceiptKeyTraffic
import ZkFormal.NearV3.Candidates.NativeReceiptFinalTraffic
import ZkFormal.NearV3.Candidates.NativeAccountReplayAgreement

/-!
# Receipt-side premises of `TrieSide.trie_side`: VSLOT views, `RcptKeys`, `RcptFinal`

* `AcceptedV3.vslot_views`: for ANY `oldPost` with `SizedAccountRun A.m.pre writes oldPost` and
  `KeysFinal A.k A.w A.m writes oldPost` (both exported by `trie_side`), the native account
  views over `oldPost` are the honest account records `A.accts` (the views read `oldPost` only
  at account keys, where every such `oldPost` agrees with the final trie, hence with `A.replay`).
* `honest_rcpt_keys` / `honest_rcpt_final`: the honest receipt traffic `rcptTrafficB` sends the
  `KEYNIB` key messages of the account and access-key lookup queries and receives their `FINAL`
  results (`NativeReceiptQueryInventory.physical_keys`/`physical_finals` on the routing-patched
  plain honest trace; the patch and the counter ranks change no `KEYNIB`/`FINAL` count).
-/

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3 RcptV3Proof
open ZkFormal.NearV3.Render ZkFormal.NearV3.Candidates

/-- The routing-patched plain honest receipt trace is locally legal. -/
theorem rcptTraceNative_patched_local (pub : List Fp) (x : RcptInput) (ok : RcptOk pub x) :
    TableLocal receiptArithmeticCandidate (RoutingQCandidate.patchTrace (rcptTraceNative pub x) 0) 0 pub :=
  ReceiptCandidateProof.repaired_local_base
    (ReceiptCandidateRouting.patch_local_of_q_bound (rcptTraceNative_local pub x ok)
      (fun r _ hs => booleanReceiptTrace_native_q_bound ok.prep ok.walk ok.witness x.own x.ctx x.lists
        ok.applied x.accountId _ pub (nativeDigests x.ctx x.digests) _ _ 22 r hs))

/-- Off `BND`, the bus counts of the routing-patched plain trace are the honest traffic. -/
theorem patched_counts (pub : List Fp) (x : RcptInput) (ok : RcptOk pub x) (b : Nat) (hb : b ≠ B_BND)
    (m : List Fp) :
    tableBusCount RcptV3.interactions (RoutingQCandidate.patchTrace (rcptTraceNative pub x) 0) 0 pub b true m =
        (((rcptTrafficB pub x).sends b).map Msg.toFp).count m ∧
      tableBusCount RcptV3.interactions (RoutingQCandidate.patchTrace (rcptTraceNative pub x) 0) 0 pub b false m =
        (((rcptTrafficB pub x).recvs b).map Msg.toFp).count m := by
  have hL0 := rcptTraceNative_local pub x ok
  obtain ⟨bs, e, hc⟩ := ReceiptCandidateProof.extract_lists hL0
  have hT := ReceiptCandidateProof.ListChain.view_traffic hL0 hc
  rw [native_chain pub x ok hc] at hT
  obtain ⟨hs, hr⟩ := rcptTrafficB_other pub x b hb
  rw [hs, hr]
  exact ⟨(RoutingQCandidate.patch_busCount _ 0 pub b true m).trans (hT b m).1,
    (RoutingQCandidate.patch_busCount _ 0 pub b false m).trans (hT b m).2⟩

/-- **`RcptKeys`** for the honest receipt traffic. -/
theorem honest_rcpt_keys (pub : List Fp) (x : RcptInput) (ok : RcptOk pub x) :
    TrieKeyFinal.RcptKeys (rcptTrafficB pub x) (x.lists.flatten.map Input.receipt) := by
  have hLP := rcptTraceNative_patched_local pub x ok
  obtain ⟨bs, e, hc⟩ := ReceiptCandidateProof.extract_lists hLP
  have h := NativeReceiptQueryInventory.physical_keys x.own x.ctx x.k x.lists 22
    (depositConstants (depositPlanAccount x.steps) (depositAgeConstants (depositPlanPrevious x.lists) x.constants))
    pub (nativeDigests x.ctx x.digests) x.accountId
    (completeReceiptAux x.ctx x.k x.lists x.accountId x.accessId
      (depositFinalAux (depositPlanPrevious x.lists) (depositPlanAccount x.steps) x.fallback))
    (completeReceiptHeaders (depositHeaderAux x.headerFallback)) ok.wf (by decide) hLP bs e hc
  unfold TrieKeyFinal.RcptKeys
  rw [List.perm_iff_count]
  intro m
  rw [← (patched_counts pub x ok B_KEYNIB (by decide) m).1]
  exact h m

/-- **`RcptFinal`** for the honest receipt traffic, against any query post-state and later
pairs (the receipt `FINAL` results are the pre-state values). -/
theorem honest_rcpt_final (pub : List Fp) (x : RcptInput) (ok : RcptOk pub x)
    {replay : PTrie} {as : List AcctV} (hm : MemOk x replay as) (ha : AkcOk x x.t)
    (queryPost : PTrie) (rest : List (PTrie × PTrie)) :
    TrieKeyFinal.RcptFinal (rcptTrafficB pub x) ((x.t, queryPost) :: rest)
      (x.lists.flatten.map Input.receipt) := by
  have hLP := rcptTraceNative_patched_local pub x ok
  have heq : RoutingQCandidate.patchTrace (rcptTraceNative pub x) 0 =
      RoutingQCandidate.patchTrace (booleanReceiptTrace x.own x.ctx x.lists 22
        (completeReceiptConstants x.ctx x.k
          (NativeReceiptAccountIds.accountId x.t (x.lists.flatten.map Input.receipt))
          (depositConstants (depositPlanAccount x.steps)
            (depositAgeConstants (depositPlanPrevious x.lists) x.constants)))
        pub (nativeDigests x.ctx x.digests)
        (completeReceiptAux x.ctx x.k x.lists
          (NativeReceiptAccountIds.accountId x.t (x.lists.flatten.map Input.receipt))
          (NativeReceiptAccessIds.accessId x.t)
          (depositFinalAux (depositPlanPrevious x.lists) (depositPlanAccount x.steps) x.fallback))
        (completeReceiptHeaders (depositHeaderAux x.headerFallback))) 0 := by
    unfold rcptTraceNative
    rw [hm.acc, ha.access]
    rfl
  obtain ⟨bs, e, hc⟩ := ReceiptCandidateProof.extract_lists hLP
  rw [heq] at hLP hc
  have h := NativeReceiptQueryInventory.physical_finals x.own x.ctx x.k x.lists 22
    (depositConstants (depositPlanAccount x.steps) (depositAgeConstants (depositPlanPrevious x.lists) x.constants))
    pub (nativeDigests x.ctx x.digests)
    (depositFinalAux (depositPlanPrevious x.lists) (depositPlanAccount x.steps) x.fallback)
    (completeReceiptHeaders (depositHeaderAux x.headerFallback)) ok.wf (by decide)
    x.t replay queryPost rest as hm.views hm.vals hLP bs e hc
  unfold TrieKeyFinal.RcptFinal
  rw [List.perm_iff_count]
  intro m
  rw [← (patched_counts pub x ok B_FINAL (by decide) m).2, heq]
  exact h m

end ZkFormal.NearV3.Assembly.RcptSkeleton

namespace ZkFormal.NearV3.Assembly.AcceptedV3
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open ZkFormal.NearV3.Render ZkFormal.NearV3.Candidates RcptSkeleton
open ZkFormal.NearV3.Rcpt.Candidates ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate

variable {cb wb : Bytes} (A : AcceptedV3 cb wb)

/-- **VSLOT premise of `trie_side`**: every old post-trie the trie side may export (any
`SizedAccountRun` + `KeysFinal`) gives the honest account records `A.accts`. -/
theorem vslot_views {writes : List (List Nat × Bytes)} {oldPost : PTrie}
    (hr : SizedAccountRun A.m.pre writes oldPost) (hkf : KeysFinal A.k A.w A.m writes oldPost) :
    nativeAccountViews A.m.pre oldPost (appliedReceipts A.k A.w) = some A.accts := by
  obtain ⟨hmem, -⟩ := A.accts_spec
  obtain ⟨-, state, hup⟩ := hkf
  have hwell : A.m.pre.wf = true := by
    rw [A.hm.pre]
    exact (built_spec A.w.main.values trieFuel A.k.slotB2.prevStateRoot _ A.hm.root_length).2.1
  rw [← A.lists_applied,
    NativeAccountReplayAgreement.native_agreement hr.forget.skeleton hmem.pair _ (fun a =>
      (ZkFormal.NearV3.find_upsert_ne (SizedAccountRun.wf hr hwell) (by decide)
        (by simp [keyBwState, accountKeyPath, nibbles]) hup).symm.trans (hmem.post a).symm)]
  exact hmem.views

/-- **`RcptKeys` premise of `trie_side`.** -/
theorem rcpt_keys : TrieKeyFinal.RcptKeys (rcptTrafficB A.pub A.rcptInput) (appliedReceipts A.k A.w) := by
  have h := honest_rcpt_keys A.pub A.rcptInput A.rcptOk
  have e : A.rcptInput.lists.flatten.map Input.receipt = appliedReceipts A.k A.w := A.lists_applied
  rw [e] at h
  exact h

/-- **`RcptFinal` premise of `trie_side`.** -/
theorem rcpt_final : TrieKeyFinal.RcptFinal (rcptTrafficB A.pub A.rcptInput)
    ((A.m.pre, A.m.result.trie) :: A.steps.map (fun s => (s.pre, s.post))) (appliedReceipts A.k A.w) := by
  have h := honest_rcpt_final A.pub A.rcptInput A.rcptOk A.accts_spec.1 A.akcOk A.m.result.trie
    (A.steps.map (fun s => (s.pre, s.post)))
  have e : A.rcptInput.lists.flatten.map Input.receipt = appliedReceipts A.k A.w := A.lists_applied
  rw [e] at h
  exact h

end ZkFormal.NearV3.Assembly.AcceptedV3
