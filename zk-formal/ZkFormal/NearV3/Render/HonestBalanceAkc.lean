import ZkFormal.NearV3.Render.HonestBalanceMem
import ZkFormal.NearV3.Candidates.NativeAccessKeyPhysical
import ZkFormal.NearV3.Candidates.NativeAccessKeyBalance
import ZkFormal.NearV3.Assembly.RcptCandidateRepairedTable

/-!
# Honest AKC balance (`rcptV3` ↔ `akeyV3`)

With `accessId` pinned to the native access-key value ids (`NativeReceiptAccessIds.accessId
pre`) and the fallback auxiliary cells carrying the native use ranks (`rankAux pre rs`), the
routing-q-patched honest trace's AKC rows are the native access-key events
(`NativeAccessKeyRanks.physical_messages`); the patch does not touch the AKC columns, so the
plain honest trace has the same AKC rows, hence `rcptV3`'s honest AKC traffic is the native
events, and the access-key providers close them (`counter_balance`).
-/

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3 RcptV3Proof
open ZkFormal.NearV3.Render ZkFormal.NearV3.Candidates

/-- The native access-key data the honest AKC balance needs, beyond `RcptOk`. -/
structure AkcOk (x : RcptInput) (pre : PTrie) : Prop where
  access : x.accessId = NativeReceiptAccessIds.accessId pre
  ranks : ∃ fb, x.fallback = NativeAccessKeyRanks.rankAux pre (x.lists.flatten.map Input.receipt) fb

theorem patch_akc_rows (tr : Trace Fp) (q : Nat) (pub : List Fp) (sd : Bool) :
    rowTraffic RcptV3.interactions (RoutingQCandidate.patchTrace tr 0) 0 q pub B_AKC sd =
      rowTraffic RcptV3.interactions tr 0 q pub B_AKC sd := by
  rw [ReceiptCandidateProof.rowT_akc, ReceiptCandidateProof.rowT_akc,
    RoutingQCandidate.patch_other tr 0 q gAK (by decide), RoutingQCandidate.patch_other tr 0 q kF (by decide),
    RoutingQCandidate.patch_other tr 0 q uak (by decide)]

/-- **AKC balances between the honest receipt and access-key tables** (field messages). -/
theorem honest_akc_balance (pub : List Fp) (x : RcptInput) (ok : RcptOk pub x) {pre : PTrie}
    (ha : AkcOk x pre) :
    (((NearV3.akeyTraffic (NativeAccessKeyProviders.providers pre (x.lists.flatten.map Input.receipt))).sends B_AKC ++
        (rcptTraffic3 pub (nativeRcptLists pub x)).sends B_AKC).map Msg.toFp).Perm
      (((rcptTraffic3 pub (nativeRcptLists pub x)).recvs B_AKC ++
        (NearV3.akeyTraffic (NativeAccessKeyProviders.providers pre (x.lists.flatten.map Input.receipt))).recvs B_AKC).map Msg.toFp) := by
  obtain ⟨fb, hfb⟩ := ha.ranks
  -- the patched honest trace is locally legal (same premises as `RcptOk`)
  obtain ⟨mid, so, steps, hmid, hl, -, -, hLP⟩ := booleanReceiptTrace_native_repaired_tableLocal
    ok.prep ok.walk ok.witness x.own x.ctx x.lists ok.source ok.applied ok.wf ok.nonempty ok.named
    ok.flags ok.run ok.gas x.accountId x.accessId x.constants pub (nativeDigests x.ctx x.digests) x.fallback
    x.headerFallback ok.gasPub ok.price ok.finalPub ok.owner
  have hs : x.steps = steps := by
    unfold RcptInput.steps; rw [hmid]; simp only [hl, Option.getD_some]
  have hLP' : TableLocal receiptArithmeticCandidate (RoutingQCandidate.patchTrace (rcptTraceNative pub x) 0) 0 pub := by
    have := ReceiptCandidateProof.repaired_local_base hLP
    unfold rcptTraceNative; rw [hs]; exact this
  obtain ⟨bsP, eP, hcP⟩ := ReceiptCandidateProof.extract_lists hLP'
  have hphys : ∀ sd, (List.range ((RoutingQCandidate.patchTrace (rcptTraceNative pub x) 0).height 0)).flatMap
      (fun pos => rowTraffic RcptV3.interactions (RoutingQCandidate.patchTrace (rcptTraceNative pub x) 0) 0 pos pub B_AKC sd) =
      (NativeAccessKeyRanks.eventMessages pre (x.lists.flatten.map Input.receipt) sd).map Msg.toFp := by
    intro sd
    have h := NativeAccessKeyRanks.physical_messages x.own x.ctx x.k x.lists 22
      (completeReceiptConstants x.ctx x.k x.accountId
        (depositConstants (depositPlanAccount x.steps) (depositAgeConstants (depositPlanPrevious x.lists) x.constants)))
      pub (nativeDigests x.ctx x.digests) x.accountId (depositPlanPrevious x.lists) (depositPlanAccount x.steps)
      fb (completeReceiptHeaders (depositHeaderAux x.headerFallback)) pre ok.wf (by decide)
    simp only at h
    have heq : RoutingQCandidate.patchTrace (rcptTraceNative pub x) 0 =
        RoutingQCandidate.patchTrace (booleanReceiptTrace x.own x.ctx x.lists 22
          (completeReceiptConstants x.ctx x.k x.accountId
            (depositConstants (depositPlanAccount x.steps) (depositAgeConstants (depositPlanPrevious x.lists) x.constants)))
          pub (nativeDigests x.ctx x.digests)
          (completeReceiptAux x.ctx x.k x.lists x.accountId (NativeReceiptAccessIds.accessId pre)
            (depositFinalAux (depositPlanPrevious x.lists) (depositPlanAccount x.steps)
              (NativeAccessKeyRanks.rankAux pre (x.lists.flatten.map Input.receipt) fb)))
          (completeReceiptHeaders (depositHeaderAux x.headerFallback))) 0 := by
      unfold rcptTraceNative; rw [ha.access, hfb]
    rw [heq] at hLP' hcP ⊢
    exact h hLP' bsP eP hcP sd
  -- the plain honest trace has the same AKC rows, and its exact traffic is the native list's
  have hL0 := rcptTraceNative_local pub x ok
  obtain ⟨bs, e, hc⟩ := ReceiptCandidateProof.extract_lists hL0
  have hT := ReceiptCandidateProof.ListChain.view_traffic hL0 hc
  rw [native_chain pub x ok hc] at hT
  have hrows : ∀ sd : Bool, ((if sd = true then (rcptTraffic3 pub (nativeRcptLists pub x)).sends B_AKC
      else (rcptTraffic3 pub (nativeRcptLists pub x)).recvs B_AKC).map Msg.toFp).Perm
      ((NativeAccessKeyRanks.eventMessages pre (x.lists.flatten.map Input.receipt) sd).map Msg.toFp) := by
    intro sd
    rw [← hphys sd, List.perm_iff_count]
    intro m
    have hpatch : (List.range ((RoutingQCandidate.patchTrace (rcptTraceNative pub x) 0).height 0)).flatMap
        (fun pos => rowTraffic RcptV3.interactions (RoutingQCandidate.patchTrace (rcptTraceNative pub x) 0) 0 pos pub B_AKC sd) =
        (List.range ((rcptTraceNative pub x).height 0)).flatMap
        (fun pos => rowTraffic RcptV3.interactions (rcptTraceNative pub x) 0 pos pub B_AKC sd) := by
      rw [RoutingQCandidate.patch_height]
      exact congrArg (fun f => List.flatMap f (List.range ((rcptTraceNative pub x).height 0)))
        (funext fun q => patch_akc_rows _ q pub sd)
    rw [hpatch, nativeRcptLists]
    cases sd
    · have h2 := (hT B_AKC m).2; rw [tableBusCount_eq] at h2
      simp only [Bool.false_eq_true, if_false]; rw [← h2]
    · have h1 := (hT B_AKC m).1; rw [tableBusCount_eq] at h1
      simp only [if_true]; rw [← h1]
  have hS := hrows true
  have hR := hrows false
  simp only [if_true, Bool.false_eq_true, if_false] at hS hR
  have hb := (NativeAccessKeyRanks.counter_balance pre (x.lists.flatten.map Input.receipt)).map Msg.toFp
  simp only [List.map_append] at hb ⊢
  exact ((List.Perm.append_left _ hS).trans hb).trans (List.Perm.append_right _ hR.symm)

end ZkFormal.NearV3.Assembly.RcptSkeleton
