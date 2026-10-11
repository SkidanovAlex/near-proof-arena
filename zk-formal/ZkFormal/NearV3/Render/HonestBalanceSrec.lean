import ZkFormal.NearV3.Render.HonestBalanceSrc
import ZkFormal.NearV3.Assembly.RcptSystemCertificate

/-!
# Honest SREC balance (`rcptV3` internal)

`SREC` is sent and received only by `rcptV3` (signer = receiver test of system receipts).  The
honest trace `rcptTraceNative pub x` is definitionally an instance of the native system
balance certificate's trace (`booleanReceiptTrace_native_systemBalance`): its constants,
auxiliary cells and header cells are the system/character/digest layers over the remaining
(key, routing, gas, deposit) layers.  With the exact traffic of `rcpt_aligned_complete`, the
honest receipt list's `SREC` sends and receives are equal multisets (as field messages, the
form every bus count uses).
-/

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3 RcptV3Proof
open ZkFormal.NearV3.Render

theorem rcptTraceNative_srec (pub : List Fp) (x : RcptInput) (ok : RcptOk pub x) :
    (List.range ((rcptTraceNative pub x).height 0)).flatMap
        (fun pos => rowTraffic RcptV3.interactions (rcptTraceNative pub x) 0 pos pub B_SREC true) =
      (List.range ((rcptTraceNative pub x).height 0)).flatMap
        (fun pos => rowTraffic RcptV3.interactions (rcptTraceNative pub x) 0 pos pub B_SREC false) :=
  booleanReceiptTrace_native_systemBalance ok.prep x.own x.ctx x.lists ok.source ok.wf ok.run ok.gas
    _ pub _ _ _

/-- **SREC balances on the honest receipt list.** -/
theorem honest_srec_balance (pub : List Fp) (x : RcptInput) (ok : RcptOk pub x) :
    (((rcptTraffic3 pub (nativeRcptLists pub x)).sends B_SREC).map Msg.toFp).Perm
      (((rcptTraffic3 pub (nativeRcptLists pub x)).recvs B_SREC).map Msg.toFp) := by
  have hL0 := rcptTraceNative_local pub x ok
  obtain ⟨bs, e, hc⟩ := ReceiptCandidateProof.extract_lists hL0
  have hT := ReceiptCandidateProof.ListChain.view_traffic hL0 hc
  rw [native_chain pub x ok hc] at hT
  have hb := rcptTraceNative_srec pub x ok
  rw [List.perm_iff_count, nativeRcptLists]
  intro m
  have h1 := (hT B_SREC m).1
  have h2 := (hT B_SREC m).2
  rw [tableBusCount_eq] at h1 h2
  rw [← h1, ← h2, hb]

end ZkFormal.NearV3.Assembly.RcptSkeleton
