import ZkFormal.NearV3.Assembly.RenderV3RcptTables
import ZkFormal.NearV3.Assembly.NativeTrace
import ZkFormal.NearV3.Assembly.NativePrepared
import ZkFormal.NearV3.Assembly.ClaimFacts
import ZkFormal.NearV3.Assembly.RoutingBoundedLayout
import ZkFormal.NearV3.Assembly.RoutingBoundedRender
import ZkFormal.NearV3.Assembly.RoutingPhysicalProviders
import ZkFormal.NearV3.Render.AcceptedRcpt
import ZkFormal.NearV3.Render.AcceptedMem
import ZkFormal.NearV3.Render.AcceptedSrcp
import ZkFormal.NearV3.Render.AcceptedQv
import ZkFormal.NearV3.Render.HonestBalanceAkc

/-!
# Receipt-side renders of `nearAirV3` from acceptance alone (tables 16–20, 22)

`AcceptedV3 cb wb` bundles the native data of an accepted witness (`checkD0a B0 cb wb = .ok ()`):
the walk `k`, the decoded witness `w` (with its raw bytes), the native main execution `m`, the
implicit steps and the native prepared statement `p` (hint `nativeHint k w m`), with the proofs
relating them.  `acceptedV3_nonempty` constructs one from acceptance.

From any `A : AcceptedV3 cb wb`, with `pub := A.pub = pubOf (preparedBytes A.p 0)`, this module
builds **unconditional** `TableRenderV3 A.pub t` instances for the receipt-side tables:

* 16 `rcptAcc` — the native receipt input `A.rcptInput` (`accountId` = native account slots,
  `accessId` = native access ids, `fallback` = native access-key ranks), `rcptOk_of_accept`;
* 17 `acctAcc` — the native account views of `memOk_of_accept` (empty allowed, `AcctV3OkE`);
* 18 `akeyAcc` — the native access-key providers (`akeyOk_of_accept`);
* 19 `bndAcc` — `boundaryEntries` over the **bounded** layout intervals and the physical
  routing keys of the honest receipt trace (rows `≤ 65·65 ≤ 2^13`, `physical_rows_fit`);
* 20 `srcpAcc` — `acceptedSrcpInputs` (`acceptedSrcp_ok_of_accept`, `acceptedSrcp_depth`);
* 22 `qvAcc` — the native queue values of `qvNativeOk_of_accept`.
-/

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open ZkFormal.NearV3.Render ZkFormal.NearV3.Assembly.RcptSkeleton ZkFormal.NearV3.Candidates

/-- The native data of an accepted witness. -/
structure AcceptedV3 (cb wb : Bytes) where
  k : WalkD0
  w : StateWitness
  raw : Bytes
  codes : List Bytes
  m : MainExecutionV3
  steps : List ImplicitStepV3
  last : Bytes
  p : Prep
  hk : walkD0 cb = .ok k
  hw : decodeW wb = .ok w
  hf : decodeWitnessFile wb = .ok (raw, codes)
  hd : decodeStateWitness raw = .ok w
  h : checkD0a B0 cb wb = .ok ()
  hm : m.NativeValid k w
  hv : ImplicitTraceValid k m.result.trie.hashOf (k.implicitBlks.zip w.implicit) steps last
  hp : prepD0 cb (nativeHint k w m) = .ok p

/-- **Every accepted witness has its native data.** -/
theorem acceptedV3_nonempty {cb wb : Bytes} (h : checkD0a B0 cb wb = .ok ()) :
    Nonempty (AcceptedV3 cb wb) := by
  have hrel : RelD0a B0 cb wb := (relD0a_iff B0 cb wb).mpr h
  obtain ⟨k, w, hk, hw, -, -⟩ := relD0a_sources_verified hrel
  obtain ⟨m, steps, last, hm, ht, hv, -⟩ := checkD0a_native_trace hk hw h
  have hc := h
  unfold checkD0a at hc
  obtain ⟨u, hc, _⟩ := ReexecV3D0.bind_ok' hc
  cases u
  obtain ⟨raw, codes, hf, hd, -⟩ := checkD0_witness_fields hk hw hc
  obtain ⟨pc, hpc⟩ := checkD0a_prepClaim_exists hk hw h
  have hh := checkD0_header_of_trace hk hw hc hm ht
  have hg : k.slotB2.gasLimit ≤ maxGasLimitD0 := by
    simpa only [a1, hk, decide_eq_true_eq] using hrel.2.1
  obtain ⟨p, hp, -⟩ := prepD0_native_success hpc hk hm hh hd hg
  exact ⟨⟨k, w, raw, codes, m, steps, last, p, hk, hw, hf, hd, h, hm, hv, hp⟩⟩

namespace AcceptedV3

variable {cb wb : Bytes} (A : AcceptedV3 cb wb)

/-- The public vector of the certificate (`preparedBytes p 0`). -/
def pub : List Fp := ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes A.p 0)

theorem rel (A : AcceptedV3 cb wb) : RelD0a B0 cb wb := (relD0a_iff B0 cb wb).mpr A.h

/-- The authenticated source lists in applied order. -/
def lists : List (List Input) := sourceInputLists (A.m.ctx A.k) A.p.lists A.w.entries

theorem lists_applied : A.lists.flatten.map Input.receipt = appliedReceipts A.k A.w :=
  (ReceiptSourceInputs.admitted (A.m.ctx A.k) A.rel A.hp A.hk A.hw A.hd).2.1

/-- The native access-key rank fallback (any base). -/
def fallback : ReceiptPlan → Coord → Nat → Fp :=
  NativeAccessKeyRanks.rankAux A.m.pre (A.lists.flatten.map Input.receipt) (fun _ _ _ => 0)

/-- **The honest receipt input** (native account slots, access ids and key ranks). -/
def rcptInput : RcptInput :=
  acceptedRcptInput cb A.raw A.k A.w A.m A.p (nativeAccountId A.m.pre A.lists)
    (NativeReceiptAccessIds.accessId A.m.pre) (fun _ _ => 0) (fun _ _ => [])
    A.fallback (fun _ _ _ => 0)

theorem rcptOk : RcptOk A.pub A.rcptInput :=
  rcptOk_of_accept A.hk A.hw A.h A.hm A.hd A.hp 0 _ _ _ _ _ _

theorem akcOk : AkcOk A.rcptInput A.m.pre := ⟨rfl, ⟨_, rfl⟩⟩

theorem memOk_exists : ∃ replay as, MemOk A.rcptInput replay as ∧
    as.length ≤ 4481 ∧ (as = [] ∨ AcctWf as) ∧ (∀ a ∈ as, ∀ b ∈ a.pre ++ a.post, b < 256) :=
  memOk_of_accept A.hk A.hw A.h A.hm A.hv A.hd A.hp _ _ _ _ _

/-- The replayed old-record tree of the account views. -/
noncomputable def replay : PTrie := Classical.choose A.memOk_exists

/-- The native account views. -/
noncomputable def accts : List AcctV := Classical.choose (Classical.choose_spec A.memOk_exists)

theorem accts_spec : MemOk A.rcptInput A.replay A.accts ∧
    A.accts.length ≤ 4481 ∧ (A.accts = [] ∨ AcctWf A.accts) ∧
    (∀ a ∈ A.accts, ∀ b ∈ a.pre ++ a.post, b < 256) :=
  Classical.choose_spec (Classical.choose_spec A.memOk_exists)

theorem acctOk : AcctV3OkE A.accts :=
  acctV3OkE_of_views A.accts A.accts_spec.2.1 A.accts_spec.2.2.1 A.accts_spec.2.2.2

/-- The native access-key providers of the applied receipts. -/
def akeys : List AkeyE :=
  NativeAccessKeyProviders.providers A.m.pre (A.rcptInput.lists.flatten.map Input.receipt)

theorem akeyOk : AkeyOk A.akeys := by
  have hgas := (ReceiptSourceInputs.gas A.rel A.hp A.hk A.hm).1
  have h := akeyOk_of_accept A.hm hgas
  have he : A.rcptInput.lists.flatten.map Input.receipt = appliedReceipts A.k A.w := A.lists_applied
  unfold akeys
  rw [he]
  exact h

/-- The bounded routing intervals of the own shard. -/
def bounds : List (Option Bytes × Option Bytes) :=
  (RoutingBoundedLayout.boundedPrep A.p A.k.L A.k.H.shardId).bnds

/-- The boundary rows: every bounded interval's 65 positions, counted against the physical
routing keys of the honest receipt trace. -/
def bnds : List BndE :=
  RoutingBoundedLayout.boundaryEntries A.bounds
    (RoutingQCandidate.physicalBoundaryKeys (rcptTraceNative A.pub A.rcptInput) 0)

theorem bnds_rows : A.bnds.length ≤ 2 ^ BndV3.maxLog := by
  have hg := (prepD0_guards A.hp A.hk).layout
  have hfit := (RoutingBoundedLayout.physical_rows_fit A.k.L A.k.H.shardId hg.2).1
  unfold bnds bounds
  rw [RoutingBoundedLayout.boundaryEntries_length]
  change 65 * (RoutingBoundedLayout.boundedIntervals A.k.L A.k.H.shardId).length ≤ 2 ^ 13
  omega

/-- The honest source-proof inputs. -/
def srcps : List SrcpGen.ProofInput := acceptedSrcpInputs A.p A.w

theorem srcpOk : SrcpGen.ProofInputsOk A.srcps :=
  acceptedSrcp_ok_of_accept A.rel A.hp A.hk A.hw A.hf A.hd

theorem srcpDepth : ∀ x ∈ A.srcps, x.entry.proof.path.length ≤ NearSpecV3.Dp0 :=
  acceptedSrcp_depth A.rel A.hp A.hk A.hw

theorem qvOk_exists : ∃ v : Qv.MainValues,
    QvNativeOk A.m.pre v (A.steps.map ImplicitStepV3.pre) A.pub :=
  qvNativeOk_of_accept A.hk A.hw A.h A.hm A.hv A.hp 0

/-- The native main queue values. -/
noncomputable def qvVals : Qv.MainValues := Classical.choose A.qvOk_exists

theorem qvOk : QvNativeOk A.m.pre A.qvVals (A.steps.map ImplicitStepV3.pre) A.pub :=
  Classical.choose_spec A.qvOk_exists

/-! ## The six receipt-side table renders -/

/-- Table 16 from acceptance. -/
def rcptAcc : TableRenderV3 A.pub 16 (by decide) := rcptRenderV3 A.pub A.rcptInput A.rcptOk

/-- Table 17 from acceptance (the empty chunk included). -/
noncomputable def acctAcc : TableRenderV3 A.pub 17 (by decide) :=
  acctRenderV3 A.pub A.accts A.acctOk

/-- Table 18 from acceptance. -/
def akeyAcc : TableRenderV3 A.pub 18 (by decide) := akeyRenderV3 A.pub A.akeys A.akeyOk

/-- Table 19 from acceptance. -/
def bndAcc : TableRenderV3 A.pub 19 (by decide) := bndRenderV3 A.pub A.bnds A.bnds_rows

/-- Table 20 from acceptance. -/
def srcpAcc : TableRenderV3 A.pub 20 (by decide) where
  tr := srcpTraceAligned (SrcpGen.blocksOfProofs A.srcps)
  tf := srcpTraffic (SrcpGen.blocksOfProofs A.srcps)
  loc := (srcp_proofs_aligned_complete A.srcps A.srcpOk A.srcpDepth 20 A.pub).1
  traffic := (srcp_proofs_aligned_complete A.srcps A.srcpOk A.srcpDepth 20 A.pub).2.1
  aligned := (srcp_proofs_aligned_complete A.srcps A.srcpOk A.srcpDepth 20 A.pub).2.2

/-- Table 22 from acceptance. -/
noncomputable def qvAcc : TableRenderV3 A.pub 22 (by decide) :=
  qvRenderV3 A.pub A.m.pre A.qvVals (A.steps.map ImplicitStepV3.pre) A.qvOk

theorem rcptAcc_tf : A.rcptAcc.tf = rcptTrafficB A.pub A.rcptInput := rfl
theorem acctAcc_tf : A.acctAcc.tf = acctV3Traffic A.accts := rfl
theorem akeyAcc_tf : A.akeyAcc.tf = akeyTraffic A.akeys := rfl
theorem bndAcc_tf : A.bndAcc.tf = bndTraffic A.bnds := rfl
theorem srcpAcc_tf : A.srcpAcc.tf = srcpTraffic (SrcpGen.blocksOfProofs A.srcps) := rfl
theorem qvAcc_tf : A.qvAcc.tf = qvNativeTraffic A.m.pre A.qvVals (A.steps.map ImplicitStepV3.pre) := rfl

end AcceptedV3

end ZkFormal.NearV3.Assembly
