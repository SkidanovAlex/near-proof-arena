import ZkFormal.NearV3.Render.HonestBalanceBnd
import ZkFormal.NearV3.Assembly.RcptCandidateRoutingPredecessor
import ZkFormal.NearV3.Assembly.RcptCandidateRoutingNative

/-!
# Honest receipt rows for the installed table 16 (`RcptV3.tableQ`, routing-index check)

User decision 2026-10-12: `nearAirV3` table 16 is `RcptV3.tableQ` = `tableR` + `qBoundR`
(`q` equals the seven boolean scratch bits `xb12..18` on first receiver rows).  The honest
ranked receipt trace `rcptTraceB` carries native interval indices `q < 128`
(`booleanReceiptTrace_native_q_bound`); filling the seven scratch cells with the bits of `q`
(`RoutingQCandidate.patchTrace`, which touches nothing else) gives a `tableQ`-legal trace
(`ReceiptCandidateRouting.patch_local_of_q_bound`; the receiver-predecessor premise is derived
from the control constraints) with the same exact traffic (`patch_traffic`, no premise).
-/

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3 RcptV3Proof
open ZkFormal.NearV3.Render RoutingQCandidate

/-- The honest receipt rows of table 16: ranked BND counters, routing-index bits filled. -/
def rcptTraceQ (pub : List Fp) (x : RcptInput) : Trace Fp := patchTrace (rcptTraceB pub x) 0

def rcptTraceAlignedQ (pub : List Fp) (x : RcptInput) : Trace Fp := pinTrace (rcptTraceQ pub x) 0

/-- Honest first-receiver interval indices are below `128`. -/
theorem rcptTraceB_q_bound (pub : List Fp) (x : RcptInput) (ok : RcptOk pub x) :
    ∀ r, r < (rcptTraceB pub x).height 0 → startsReceiver (rcptTraceB pub x) 0 r →
      cv (rcptTraceB pub x) 0 r q < 128 := by
  intro r _ hs
  have hs' : startsReceiver (rcptTraceNative pub x) 0 r := hs
  have h := booleanReceiptTrace_native_q_bound ok.prep ok.walk ok.witness x.own x.ctx x.lists
    ok.applied x.accountId _ pub (nativeDigests x.ctx x.digests) _ _ 22 r hs'
  exact h

/-- **Completeness of the installed receipt table** (`tableQ`): local legality, the exact
honest traffic `rcptTrafficB`, aligned height. -/
theorem rcpt_aligned_completeQ (pub : List Fp) (x : RcptInput) (ok : RcptOk pub x) (t : Nat) :
    TableLocal RcptV3.tableQ (rcptTraceAlignedQ pub x) t pub ∧
      TableTraffic RcptV3.interactions (rcptTraceAlignedQ pub x) t pub (rcptTrafficB pub x) ∧
      (rcptTraceAlignedQ pub x).log t % 3 = 1 := by
  have hL : TableLocal RcptV3.tableQ (rcptTraceQ pub x) 0 pub :=
    ReceiptCandidateRouting.patch_local_of_q_bound (rcptTraceB_local pub x ok)
      (rcptTraceB_q_bound pub x ok)
  have hT : TableTraffic RcptV3.interactions (rcptTraceQ pub x) 0 pub (rcptTrafficB pub x) :=
    patch_traffic (rcptTraceB_traffic pub x ok)
  refine ⟨tableLocal_pin t hL, tableTraffic_pin t hT, ?_⟩
  have h22 : (rcptTraceB pub x).log 0 = 22 := rfl
  show (rcptTraceB pub x).log 0 % 3 = 1
  rw [h22]

theorem rcptTraceAlignedQ_log (pub : List Fp) (x : RcptInput) (t : Nat) :
    (rcptTraceAlignedQ pub x).log t = 22 := rfl

end ZkFormal.NearV3.Assembly.RcptSkeleton
