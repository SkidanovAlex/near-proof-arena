import ZkFormal.NearV3.Assembly.RenderV3RcptBnd

/-!
# The receipt side of `CompleteV3Stmt` from acceptance, in one place

For an accepted witness (`A : AcceptedV3 cb wb`, `acceptedV3_nonempty`), with
`A.pub = pubOf (preparedBytes A.p 0)`:

* `A.rcptRenders : RcptRendersV3 A.pub` — the honest renders of tables 16 (`rcptV3`), 17
  (`acctV3`, empty chunk included), 18 (`akeyV3`), 19 (`bndV3`), 20 (`srcpV3`) and 22 (`qvV3`),
  premise-free (table 21 = `sizeA7` belongs to the trie side);
* `A.pubFit`, `A.prepared_lt_P` — the public fit and packed-size conjuncts of
  `RenderWitnessV3` (A12);
* **`rcpt_side_balanced`**: in any bundle whose tables 16–20, 22 are these renders and whose
  table 24 carries the sort traffic of the applied receipt ids (`sortRenderV3` with
  `lists := A.rcptInput.lists`), the buses SREC, RCL, AKC, RIDS, MEM, QVC, QSH, SRC, BNDP and BND
  balance (`BusBalanced`, the bundle balance on that bus, public messages included).
-/

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near
open ZkFormal.NearV3.Render RcptSkeleton RcptBal

/-- The receipt-side table renders over one public vector. -/
structure RcptRendersV3 (pub : List Fp) where
  rcpt : TableRenderV3 pub 16 (by decide)
  acct : TableRenderV3 pub 17 (by decide)
  akey : TableRenderV3 pub 18 (by decide)
  bnd : TableRenderV3 pub 19 (by decide)
  srcp : TableRenderV3 pub 20 (by decide)
  qv : TableRenderV3 pub 22 (by decide)

namespace AcceptedV3

variable {cb wb : Bytes} (A : AcceptedV3 cb wb)

/-- **The receipt-side renders of an accepted witness** (no premises). -/
noncomputable def rcptRenders : RcptRendersV3 A.pub :=
  ⟨A.rcptAcc, A.acctAcc, A.akeyAcc, A.bndAcc, A.srcpAcc, A.qvAcc⟩

end AcceptedV3

theorem bundle_tf_eq {pub : List Fp} (R : RenderBundleV3 pub) (t : Nat) (ht : t < nearAirV3.tables.length)
    {X : TableRenderV3 pub t ht} (h : R ⟨t, ht⟩ = X) : R.tf t = X.tf := by
  simp only [RenderBundleV3.tf, ht, ↓reduceDIte, h]

/-- **All receipt-side bus balances of an accepted witness**, in the bundle's form. -/
theorem rcpt_side_balanced {cb wb : Bytes} (A : AcceptedV3 cb wb) (R : RenderBundleV3 A.pub)
    (h16 : R ⟨16, by decide⟩ = A.rcptRenders.rcpt) (h17 : R ⟨17, by decide⟩ = A.rcptRenders.acct)
    (h18 : R ⟨18, by decide⟩ = A.rcptRenders.akey) (h19 : R ⟨19, by decide⟩ = A.rcptRenders.bnd)
    (h20 : R ⟨20, by decide⟩ = A.rcptRenders.srcp) (h22 : R ⟨22, by decide⟩ = A.rcptRenders.qv)
    (h24 : R.tf 24 = sortTraffic (Candidates.NativeSortIds.input
      (A.rcptInput.lists.flatten.map Input.receipt))) :
    BusBalanced R B_SREC ∧ BusBalanced R B_RCL ∧ BusBalanced R B_AKC ∧ BusBalanced R B_RIDS ∧
      BusBalanced R B_MEM ∧ BusBalanced R ZkFormal.NearV3.Qv.Candidates.ValueTable.B_QVC ∧
      BusBalanced R B_QSH ∧ BusBalanced R B_SRC ∧ BusBalanced R B_BNDP ∧ BusBalanced R B_BND := by
  have t16 : R.tf 16 = rcptTrafficB A.pub A.rcptInput := bundle_tf_eq R 16 _ h16
  have t17 : R.tf 17 = acctV3Traffic A.accts := bundle_tf_eq R 17 _ h17
  have t18 : R.tf 18 = akeyTraffic A.akeys := bundle_tf_eq R 18 _ h18
  have t19 : R.tf 19 = bndTraffic A.bnds := bundle_tf_eq R 19 _ h19
  have t20 : R.tf 20 = srcpTraffic (SrcpGen.blocksOfProofs A.srcps) := bundle_tf_eq R 20 _ h20
  have t22 : R.tf 22 = qvNativeTraffic A.m.pre A.qvVals (A.steps.map ImplicitStepV3.pre) :=
    bundle_tf_eq R 22 _ h22
  exact ⟨srec_balanced A R t16, rcl_balanced A R t16 t20, akc_balanced A R t16 t18,
    rids_balanced A R t16 h24, mem_balanced A R t16 t17, qvc_balanced A R t22, qsh_balanced A R t22,
    src_balanced_accepted A R t20, bndp_balanced_accepted A R t19, bnd_balanced_accepted A R t16 t19⟩

/-- **The receipt side of the completeness obligation from acceptance**: every accepted witness
has native data `A` whose receipt-side renders exist, whose public statement fits, and whose
receipt-side buses balance in every bundle that uses these renders (and the honest sort traffic). -/
theorem rcpt_side_of_accept {cb wb : Bytes} (h : checkD0a B0 cb wb = .ok ()) :
    ∃ A : AcceptedV3 cb wb,
      ZkFormal.V2.pubFit nearAirV3 A.pub = true ∧
      (ZkFormal.NearV3.Public.preparedBytes A.p 0).length < ZkFormal.Algebra.P ∧
      ∀ R : RenderBundleV3 A.pub,
        R ⟨16, by decide⟩ = A.rcptRenders.rcpt → R ⟨17, by decide⟩ = A.rcptRenders.acct →
        R ⟨18, by decide⟩ = A.rcptRenders.akey → R ⟨19, by decide⟩ = A.rcptRenders.bnd →
        R ⟨20, by decide⟩ = A.rcptRenders.srcp → R ⟨22, by decide⟩ = A.rcptRenders.qv →
        R.tf 24 = sortTraffic (Candidates.NativeSortIds.input
          (A.rcptInput.lists.flatten.map Input.receipt)) →
        BusBalanced R B_SREC ∧ BusBalanced R B_RCL ∧ BusBalanced R B_AKC ∧ BusBalanced R B_RIDS ∧
          BusBalanced R B_MEM ∧ BusBalanced R ZkFormal.NearV3.Qv.Candidates.ValueTable.B_QVC ∧
          BusBalanced R B_QSH ∧ BusBalanced R B_SRC ∧ BusBalanced R B_BNDP ∧ BusBalanced R B_BND := by
  obtain ⟨A⟩ := acceptedV3_nonempty h
  exact ⟨A, A.pubFit, A.prepared_lt_P, fun R h16 h17 h18 h19 h20 h22 h24 =>
    rcpt_side_balanced A R h16 h17 h18 h19 h20 h22 h24⟩

end ZkFormal.NearV3.Assembly
