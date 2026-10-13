import ZkFormal.NearV3.Assembly.RcptCandidateNativeTable
import ZkFormal.NearV3.Assembly.RcptCandidateTableTraffic
import ZkFormal.NearV3.Assembly.RcptCandidateListChain
import ZkFormal.NearV3.Render.ColAgree
import ZkFormal.NearV3.Assembly.RcptUnpatchedViews
import ZkFormal.NearV3.Assembly.RcptNativePeo
import ZkFormal.NearV3.Rcpt.Tables.RcptR

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
    pub (nativeDigests x.ctx x.digests)
    (completeReceiptAux x.ctx x.k x.lists x.accountId x.accessId
      (depositFinalAux (depositPlanPrevious x.lists) (depositPlanAccount x.steps) x.fallback))
    (completeReceiptHeaders (depositHeaderAux x.headerFallback))

/-- The honest receipt table, pinned to its rows at index `0`. -/
def rcptTraceAligned (pub : List Fp) (x : RcptInput) : Trace Fp := pinTrace (rcptTraceNative pub x) 0

theorem rcptTraceNative_local (pub : List Fp) (x : RcptInput) (ok : RcptOk pub x) :
    TableLocal receiptArithmeticCandidate (rcptTraceNative pub x) 0 pub := by
  obtain ⟨mid, so, steps, hmid, hl, -, -, hL⟩ := booleanReceiptTrace_native_candidate_tableLocal
    ok.prep ok.walk ok.witness x.own x.ctx x.lists ok.source ok.applied ok.wf ok.nonempty ok.named
    ok.flags ok.run ok.gas x.accountId x.accessId x.constants pub (nativeDigests x.ctx x.digests) x.fallback
    x.headerFallback ok.gasPub ok.price ok.finalPub ok.owner
  have hs : x.steps = steps := by
    unfold RcptInput.steps
    rw [hmid]
    simp only [hl, Option.getD_some]
  unfold rcptTraceNative
  rw [hs]
  exact hL

/-! ## The native list view -/

/-- The receipt shapes at the head of an entity list, and the rest. -/
def collectReceipts : List DecodedEntity → List RcptV3Proof.RS × List DecodedEntity
  | .receipt y :: ds => ((collectReceipts ds).1.cons y, (collectReceipts ds).2)
  | ds => ([], ds)

def blocksFuel : Nat → List DecodedEntity → List RcptV3Proof.ListBlock
  | 0, _ => []
  | n + 1, .header s :: ds => ⟨s, (collectReceipts ds).1⟩ :: blocksFuel n (collectReceipts ds).2
  | _ + 1, _ => []

/-- Group a header/receipt entity sequence into list blocks. -/
def blocksOfEntities (ds : List DecodedEntity) : List RcptV3Proof.ListBlock := blocksFuel ds.length ds

/-- **The native list blocks** of the planned receipt layout. -/
def nativeBlocks (lists : List (List Input)) : List RcptV3Proof.ListBlock :=
  blocksOfEntities (nativeEntities 0 (entityPlans lists))

/-- **The honest receipt list view**: the native list blocks read on the honest rows. -/
def nativeRcptLists (pub : List Fp) (x : RcptInput) : RcptV3Vs :=
  (nativeBlocks x.lists).map (RcptV3Proof.ListBlock.view (rcptTraceNative pub x) 0)

theorem collectReceipts_append (ys : List RcptV3Proof.RS) (rest : List DecodedEntity)
    (hr : ∀ y ds, rest ≠ .receipt y :: ds) :
    collectReceipts (ys.map DecodedEntity.receipt ++ rest) = (ys, rest) := by
  induction ys with
  | nil =>
    cases rest with
    | nil => rfl
    | cons d ds =>
      cases d with
      | header s => rfl
      | receipt y => exact absurd rfl (hr y ds)
  | cons y ys ih => simp only [List.map_cons, List.cons_append, collectReceipts, ih]

theorem blocksFuel_entities (bs : List RcptV3Proof.ListBlock) (n : Nat)
    (hn : (bs.flatMap ListBlock.entities).length ≤ n) :
    blocksFuel n (bs.flatMap ListBlock.entities) = bs := by
  induction bs generalizing n with
  | nil => cases n <;> rfl
  | cons B bs ih =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by simp [ListBlock.entities] at hn; omega⟩
    have hr : ∀ y ds, bs.flatMap ListBlock.entities ≠ .receipt y :: ds := by
      intro y ds h
      cases bs with
      | nil => simp at h
      | cons C cs => simp [ListBlock.entities] at h
    simp only [List.flatMap_cons, ListBlock.entities, List.cons_append, blocksFuel,
      collectReceipts_append _ _ hr]
    rw [ih m (by simp [ListBlock.entities] at hn ⊢; omega)]

theorem blocksOfEntities_entities (bs : List RcptV3Proof.ListBlock) :
    blocksOfEntities (bs.flatMap ListBlock.entities) = bs :=
  blocksFuel_entities bs _ (Nat.le_refl _)

/-- The extracted list chain of the honest rows is the native one. -/
theorem native_chain (pub : List Fp) (x : RcptInput) (ok : RcptOk pub x)
    {bs : List RcptV3Proof.ListBlock} {e : Nat} (hc : RcptV3Proof.ListChain (rcptTraceNative pub x) 0 0 bs e) :
    bs = nativeBlocks x.lists := by
  have hL := rcptTraceNative_local pub x ok
  have he := decoded_native_sequenceU x.own x.ctx x.lists 22 _ pub _ _ _ ok.wf (by decide) hL
    _ e (ListChain.decoded hc) (ReceiptCandidateProof.ListChain.end_padding hc).2
  rw [nativeBlocks, ← he, blocksOfEntities_entities]

/-- The flat native view is the honest rows read at the native receipt locations. -/
theorem nativeRcptLists_flat (pub : List Fp) (x : RcptInput) (ok : RcptOk pub x) :
    flatR (nativeRcptLists pub x) = locatedViews (rcptTraceNative pub x) x.lists := by
  have hL := rcptTraceNative_local pub x ok
  obtain ⟨bs, e, hc⟩ := ReceiptCandidateProof.extract_lists hL
  have h := canonical_native_viewsU x.own x.ctx x.lists 22 _ pub _ _ _ ok.wf (by decide) hL bs e hc
  rw [nativeRcptLists, ← native_chain pub x ok hc]
  exact h

/-- **Repaired receipt table completeness** at its (aligned) height `2^22`: the honest rows
(native digest streams `nativeDigests`) satisfy every constraint of `RcptV3.tableR` and have
exactly the traffic of the native list view `nativeRcptLists pub x`. -/
theorem rcpt_aligned_complete (pub : List Fp) (x : RcptInput) (ok : RcptOk pub x) (t : Nat) :
    TableLocal RcptV3.tableR (rcptTraceAligned pub x) t pub ∧
      TableTraffic RcptV3.interactions (rcptTraceAligned pub x) t pub
        (rcptTraffic3 pub (nativeRcptLists pub x)) ∧
      (rcptTraceAligned pub x).log t % 3 = 1 := by
  have hL0 := rcptTraceNative_local pub x ok
  obtain ⟨bs, e, hc⟩ := ReceiptCandidateProof.extract_lists hL0
  have hT := ReceiptCandidateProof.ListChain.view_traffic hL0 hc
  rw [native_chain pub x ok hc] at hT
  refine ⟨tableLocal_pin t hL0, tableTraffic_pin t hT, ?_⟩
  have h22 : (rcptTraceNative pub x).log 0 = 22 := rfl
  show (rcptTraceNative pub x).log 0 % 3 = 1
  rw [h22]

end ZkFormal.NearV3.Assembly.RcptSkeleton
