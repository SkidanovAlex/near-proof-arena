import ZkFormal.NearV3.Assembly.RcptCandidateNativeTable
import ZkFormal.NearV3.Assembly.RcptReceiptRepaired
import ZkFormal.NearV3.Assembly.RcptCandidateTableTraffic
import ZkFormal.NearV3.Assembly.RcptCandidateListChain
import ZkFormal.NearV3.Render.ColAgree

/-!
# Honest generator for the repaired receipt table (`nearAirV3` table 16)

The honest receipt rows are the candidate renderer's native trace
(`booleanReceiptTrace … 22 …`, `RcptCandidateNativeTable.lean`): built from the successful
native execution of the applied source lists (`applyNewChunk`), its deposit ledger and the
prepared public bytes.  Its height is always `2^22` (`22 % 3 = 1`, already roll-aligned).
`booleanReceiptTrace_native_candidate_tableLocal` proves `TableLocal` for the repaired table
(`RcptV3.tableR = receiptArithmeticCandidate`), and the soundness extraction
(`extract_lists`, `ListChain.view_traffic`) gives its exact traffic as the traffic of its
list view.  The trace is pinned to one table index so it can sit at index 16.
-/

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3 Sched
open RoutingBoundedLayout ZkFormal.NearV3.Render

/-- The native data of the honest receipt table. -/
structure RcptInput where
  cb : Bytes
  bs : Bytes
  hint : Hint
  p : Prep
  k : WalkD0
  w : StateWitness
  own : Nat
  ctx : ApplyCtx
  lists : List (List Input)
  t : PTrie
  out : MainOut
  accountId : ReceiptPlan → Nat
  accessId : ReceiptPlan → Option Nat
  constants : ReceiptPlan → Nat → Fp
  digests : ReceiptPlan → Nat → List Fp
  fallback : ReceiptPlan → Coord → Nat → Fp
  headerFallback : ListPlan → Coord → Nat → Fp

/-- **The honest hypothesis** `RcptOk pub x`: successful preparation, walk and witness
decoding; the applied source lists are `appliedReceipts` (well-formed, named receivers,
native refund flags); the native chunk application succeeds within the D0 gas limit; and the
public gas-price, final (outcome/refund/token) and owner bytes are the prepared ones. -/
structure RcptOk (pub : List Fp) (x : RcptInput) : Prop where
  prep : prepD0 x.cb x.hint = .ok x.p
  walk : walkD0 x.cb = .ok x.k
  witness : decodeStateWitness x.bs = .ok x.w
  source : x.lists.length = x.p.lists.length
  applied : x.lists.flatten.map Input.receipt = appliedReceipts x.k x.w
  wf : ∀ xs ∈ x.lists, ∀ y ∈ xs, y.receipt.wf = true
  nonempty : x.lists ≠ []
  named : ∀ xs ∈ x.lists, ∀ y ∈ xs, AccountId.isNamed y.receipt.receiverId = true
  flags : ∀ xs ∈ x.lists, ∀ y ∈ xs, y.refund = nativeRefund x.ctx y.receipt
  run : applyNewChunk prims x.ctx x.t (x.lists.flatten.map Input.receipt) = .ok x.out
  gas : x.ctx.gasLimit ≤ maxGasLimitD0
  gasPub : GasPublicBytes x.ctx pub
  price : x.ctx.gasPrice < 256 ^ 16
  finalPub : FinalPublicBytes x.lists x.out pub
  owner : ∀ j, j < 8 → pub.getD (PH_OWN + j) 0 = Fp.ofNat (((u64 x.own).getD j 0).toNat)

/-- The native deposit ledger of the input (executable). -/
def RcptInput.steps (x : RcptInput) : List NativeDepositStep :=
  match schedStep prims x.ctx x.t with
  | .ok (mid, _) => (nativeDepositLedger x.ctx ⟨mid, [], [], 0, 0⟩ (x.lists.flatten.map Input.receipt)).getD []
  | .error _ => []

def rcptTraceNative (pub : List Fp) (x : RcptInput) : Trace Fp :=
  booleanReceiptTrace x.own x.ctx x.lists 22
    (completeReceiptConstants x.ctx x.k x.accountId
      (depositConstants (depositPlanAccount x.steps) (depositAgeConstants (depositPlanPrevious x.lists) x.constants)))
    pub x.digests
    (completeReceiptAux x.ctx x.k x.lists x.accountId x.accessId
      (depositFinalAux (depositPlanPrevious x.lists) (depositPlanAccount x.steps) x.fallback))
    (completeReceiptHeaders (depositHeaderAux x.headerFallback))

/-- The honest receipt table, pinned to its rows at index `0`. -/
def rcptTraceAligned (pub : List Fp) (x : RcptInput) : Trace Fp := pinTrace (rcptTraceNative pub x) 0

theorem rcptTraceNative_local (pub : List Fp) (x : RcptInput) (ok : RcptOk pub x) :
    TableLocal receiptArithmeticCandidate (rcptTraceNative pub x) 0 pub := by
  obtain ⟨mid, so, steps, hmid, hl, -, -, hL⟩ := booleanReceiptTrace_native_candidate_tableLocal
    ok.prep ok.walk ok.witness x.own x.ctx x.lists ok.source ok.applied ok.wf ok.nonempty ok.named
    ok.flags ok.run ok.gas x.accountId x.accessId x.constants pub x.digests x.fallback
    x.headerFallback ok.gasPub ok.price ok.finalPub ok.owner
  have hs : x.steps = steps := by
    unfold RcptInput.steps
    rw [hmid]
    simp only [hl, Option.getD_some]
  unfold rcptTraceNative
  rw [hs]
  exact hL

/-- **Repaired receipt table completeness** at its (aligned) height `2^22`: the honest rows
satisfy every constraint of `RcptV3.tableR` and have exactly the traffic `rcptTraffic3 pub ls`
of their list view `ls`. -/
theorem rcpt_aligned_complete (pub : List Fp) (x : RcptInput) (ok : RcptOk pub x) (t : Nat) :
    ∃ ls, TableLocal RcptV3.tableR (rcptTraceAligned pub x) t pub ∧
      TableTraffic RcptV3.interactions (rcptTraceAligned pub x) t pub (rcptTraffic3 pub ls) ∧
      (rcptTraceAligned pub x).log t % 3 = 1 := by
  have hL : TableLocal receiptArithmeticCandidate (rcptTraceAligned pub x) t pub :=
    tableLocal_pin t (rcptTraceNative_local pub x ok)
  obtain ⟨bs, e, hc⟩ := ReceiptCandidateProof.extract_lists hL
  refine ⟨_, hL, ReceiptCandidateProof.ListChain.view_traffic hL hc, ?_⟩
  have h22 : (rcptTraceNative pub x).log 0 = 22 := rfl
  show (rcptTraceNative pub x).log 0 % 3 = 1
  rw [h22]

end ZkFormal.NearV3.Assembly.RcptSkeleton
