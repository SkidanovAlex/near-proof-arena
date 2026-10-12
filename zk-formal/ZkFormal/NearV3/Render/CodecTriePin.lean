import ZkFormal.NearV3.Render.CodecSanity
import ZkFormal.NearV3.Assembly.RenderV3RcptTrieSide

/-!
# Table 11 on an accepted witness, pinned to the trie side's scheduler upsert witnesses

`codec_on`: for `A : AcceptedV3 cb wb`, the `PriorCore` blocks built on `A`'s own native trace
(`A.m`, `A.steps`) render table 11 with no residual premise, and their scheduler calls are the trace's
calls.  `codec_premises`: for any `us` with `CallPin A.k A.m A.steps us` (as exported by
`rcpt_trie_side`), the codec's `BYTES` sends / `DIGEST` receives are those of
`schedulerSanityJobs 0 us` — exactly the codec premises of `rcpt_trie_side`.
-/
namespace ZkFormal.NearV3.Render.CdcGrant
open NearSpec NearSpecV3 ZkFormal.NearV3.Candidates ZkFormal.NearV3.Sched
open ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Assembly ZkFormal.NearV3.Assembly.CodecDigest
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Render.Cdc

theorem trace_length {k : WalkD0} {root : Bytes} {pairs : List (NearSpecV3.Blk × Transition)}
    {steps : List ImplicitStepV3} {last : Bytes} (h : ImplicitTraceValid k root pairs steps last) :
    steps.length = pairs.length := by
  induction h with
  | nil => rfl
  | cons _ _ _ _ _ _ _ _ _ _ ih => simp [ih]

theorem steps_bounds {cb wb : Bytes} (A : AcceptedV3 cb wb) :
    A.steps.length = A.k.implicitBlks.length ∧ A.steps.length ≤ 31 := by
  obtain ⟨m, steps, last, -, -, hv, hlen, h31, -⟩ := checkD0a_native_trace A.hk A.hw A.h
  have h1 := trace_length hv
  have h2 := trace_length A.hv
  omega

/-- **Table 11 on `A`'s trace**, with the blocks' calls. -/
theorem codec_on {cb wb : Bytes} (A : AcceptedV3 cb wb) (pub : List Fp) :
    ∃ bs : List NativeBlock, PriorCore A.p B0 bs ∧ (∀ b ∈ bs, GrantWit b) ∧ (∀ b ∈ bs, NatRes b) ∧
      bs.map (fun b => (b.witness.ctx, b.witness.pre)) =
        (A.m.ctx A.k, A.m.pre) :: A.steps.map (fun e => (implicitCtx A.k e, e.pre)) ∧
      ∃ R : TableRenderV3 pub 11 (by decide), R.tr = codecTrace (allDescs (bs.map blkOf)) ∧
        R.tf = rowsTraffic Codec.table.interactions (codecCell (bs.map blkOf)) 22 11 pub := by
  obtain ⟨hl, h31⟩ := steps_bounds A
  obtain ⟨bs, hc, hg, hctx⟩ := prior_core_on A.hp A.hk A.hw A.h (by decide) A.hm A.hv hl h31
  have hres : ∀ b ∈ bs, NatRes b := fun b hb => natRes_block A.hp (by decide) hc b hb (hg b hb)
  refine ⟨bs, hc, hg, hres, hctx, ?_⟩
  have hok : ∀ B ∈ bs.map blkOf, B.Ok := by
    intro B hB
    simp only [List.mem_map] at hB
    obtain ⟨b, hb, rfl⟩ := hB
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hb
    obtain ⟨⟨hsch, hrun⟩, _, _⟩ := hc.indexed i b hi
    have hil : i < bs.length := (List.getElem?_eq_some_iff.mp hi).1
    exact blkOf_ok b (hc.valid b hb).2 i (by have := hc.length; omega) hrun
      (prepD0_sched A.hp b.pub (List.mem_of_getElem? hsch)) (hres b hb)
  have hcap : (allDescs (bs.map blkOf)).length < 2 ^ 22 := by
    have := blocks_length bs (fun b hb => (hc.valid b hb).2)
    have := hc.length
    omega
  exact ⟨codecRenderV3 pub (bs.map blkOf) hok hcap, rfl, rfl⟩

theorem calls_of_pairs (bs : List NativeBlock) {k : WalkD0} {m : MainExecutionV3}
    {steps : List ImplicitStepV3}
    (h : bs.map (fun b => (b.witness.ctx, b.witness.pre)) =
      (m.ctx k, m.pre) :: steps.map (fun e => (implicitCtx k e, e.pre))) :
    CallPin k m steps (bs.map NativeBlock.witness) := by
  have := congrArg (List.map fun q => (q.1, schedRead q.2)) h
  simp only [List.map_map, List.map_cons, Function.comp_def] at this
  simpa only [CallPin, callList, List.map_map, Function.comp_def] using this

/-- **The codec premises of `rcpt_trie_side`** for its pinned `us`. -/
theorem codec_premises {cb wb : Bytes} (A : AcceptedV3 cb wb) (pub : List Fp)
    (us : List SchedulerUpsertWitness) (hpin : CallPin A.k A.m A.steps us) :
    ∃ bs : List NativeBlock, PriorCore A.p B0 bs ∧ (∀ b ∈ bs, GrantWit b) ∧ (∀ b ∈ bs, NatRes b) ∧
      bs.map (fun b => (b.witness.ctx, b.witness.pre)) =
        (A.m.ctx A.k, A.m.pre) :: A.steps.map (fun e => (implicitCtx A.k e, e.pre)) ∧
      ∃ R : TableRenderV3 pub 11 (by decide), R.tr = codecTrace (allDescs (bs.map blkOf)) ∧
        R.tf = rowsTraffic Codec.table.interactions (codecCell (bs.map blkOf)) 22 11 pub ∧
        (∀ m, Assembly.cnt (R.tf.sends B_BYTES) m = Assembly.cnt (Sha.Gen.expectedBytes (schedulerSanityJobs 0 us)) m) ∧
        (∀ m, Assembly.cnt (R.tf.recvs B_DIGEST) m = Assembly.cnt (Sha.Gen.expectedDigests (schedulerSanityJobs 0 us)) m) := by
  obtain ⟨bs, hc, hg, hres, hctx, R, htr, htf⟩ := codec_on A pub
  have hp : us.map schedulerWitnessSanity = (bs.map NativeBlock.witness).map schedulerWitnessSanity := by
    rw [hpin.sanity, (calls_of_pairs bs hctx).sanity]
  obtain ⟨h1, h2⟩ := codec_sha_counts_pinned hc pub us hp
  refine ⟨bs, hc, hg, hres, hctx, R, htr, htf, fun m => ?_, fun m => ?_⟩
  · rw [htf]; simpa only [ZkFormal.Near.cnt, Assembly.cnt] using h1 m
  · rw [htf]; simpa only [ZkFormal.Near.cnt, Assembly.cnt] using h2 m


end ZkFormal.NearV3.Render.CdcGrant

namespace ZkFormal.NearV3.Assembly.RcptTrieSide
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3 ZkFormal.NearV3.Assembly
  Render Rcpt.Candidates Rcpt.Candidates.NodePostUpdate RcptSkeleton RcptBal ZkFormal.NearV3.UnfoldA7 TrieA7
open ZkFormal.NearV3.Assembly.CodecDigest ZkFormal.NearV3.Render.Cdc ZkFormal.NearV3.Render.CdcGrant

/-- **`rcpt_trie_side` with table 11 (the codec on the same trace): `BYTES` and `DIGEST` balance
unconditionally.** -/
theorem rcpt_trie_codec {cb wb : Bytes} (A : AcceptedV3 cb wb)
    (hovh : TrieSide.SizeBudget A) :
    ∃ (writes : List (List Nat × Bytes)) (oldPost : PTrie) (q : UseRequests) (us : List SchedulerUpsertWitness)
      (r0 : TableRenderV3 A.pub 0 (by decide)) (r1 : TableRenderV3 A.pub 1 (by decide))
      (r2 : TableRenderV3 A.pub 2 (by decide)) (r3 : TableRenderV3 A.pub 3 (by decide))
      (r4 : TableRenderV3 A.pub 4 (by decide)) (r5 : TableRenderV3 A.pub 5 (by decide))
      (r6 : TableRenderV3 A.pub 6 (by decide)) (r7 : TableRenderV3 A.pub 7 (by decide))
      (r21 : TableRenderV3 A.pub 21 (by decide))
      (r11 : TableRenderV3 A.pub 11 (by decide)) (bs : List NativeBlock),
      SizedAccountRun A.m.pre writes oldPost ∧ KeysFinal A.k A.w A.m writes oldPost ∧ (∀ u ∈ us, u.Valid) ∧
      CallPin A.k A.m A.steps us ∧
      (∃ (Js : List UpsInst) (hok : UpsRenderOk Js), r7 = upsRenderV3 A.pub Js hok ∧
        ExtOf r7.tf (upsTraffic (UpsRows.viewOf (upsTraceAligned Js) T_UPS (UpsGen.segsOf Js))) ∧
        Js.map (fun I => (I.tau, I.v)) = us.mapIdx (fun i u => (i, u.value.map UInt8.toNat)) ∧
        Js.map Assembly.UpsS0F.s0fOf = (A.m.pre :: A.steps.map ImplicitStepV3.pre).mapIdx
          (fun i t => Assembly.UpsS0F.s0fPair ((A.m.pre :: A.steps.map ImplicitStepV3.pre).take i) t)) ∧
      -- lane v3-render-vbytes: the value render's base traffic (for `VBYTES`)
      ExtOf r4.tf (valTraffic (TrieNative.vals A.m A.steps)) ∧
      PriorCore A.p NearSpecV3.B0 bs ∧ (∀ b ∈ bs, GrantWit b) ∧ (∀ b ∈ bs, NatRes b) ∧
      bs.map (fun b => (b.witness.ctx, b.witness.pre)) =
        (A.m.ctx A.k, A.m.pre) :: A.steps.map (fun e => (implicitCtx A.k e, e.pre)) ∧
      r11.tr = codecTrace (allDescs (bs.map blkOf)) ∧
      r11.tf = rowsTraffic Sched.Codec.table.interactions (codecCell (bs.map blkOf)) 22 11 A.pub ∧
      ∀ R : RenderBundleV3 A.pub,
        R ⟨0, by decide⟩ = r0 → R ⟨1, by decide⟩ = r1 → R ⟨2, by decide⟩ = r2 → R ⟨3, by decide⟩ = r3 →
        R ⟨4, by decide⟩ = r4 → R ⟨5, by decide⟩ = r5 → R ⟨6, by decide⟩ = r6 → R ⟨7, by decide⟩ = r7 →
        R ⟨16, by decide⟩ = A.rcptRenders.rcpt → R ⟨17, by decide⟩ = A.rcptRenders.acct →
        R ⟨18, by decide⟩ = A.rcptRenders.akey → R ⟨19, by decide⟩ = A.rcptRenders.bnd →
        R ⟨20, by decide⟩ = A.rcptRenders.srcp → R ⟨21, by decide⟩ = r21 →
        R ⟨22, by decide⟩ = A.rcptRenders.qv → R ⟨23, by decide⟩ = A.mrkAcc →
        R ⟨11, by decide⟩ = r11 →
        R.tf 24 = sortTraffic (Candidates.NativeSortIds.input (A.rcptInput.lists.flatten.map Input.receipt)) →
        -- receipt-side buses
        (BusBalanced R B_SREC ∧ BusBalanced R B_RCL ∧ BusBalanced R B_AKC ∧ BusBalanced R B_RIDS ∧
          BusBalanced R B_MEM ∧ BusBalanced R ZkFormal.NearV3.Qv.Candidates.ValueTable.B_QVC ∧
          BusBalanced R B_QSH ∧ BusBalanced R B_SRC ∧ BusBalanced R B_BNDP ∧ BusBalanced R B_BND) ∧
        -- trie-side buses
        (R.BalancedAt B_PARENT ∧ R.BalancedAt B_VPARENT ∧ R.BalancedAt B_ENT ∧ R.BalancedAt B_DIGS ∧
          R.BalancedAt B_DUP ∧ R.BalancedAt B_EDGE ∧ R.BalancedAt B_BMAP ∧ R.BalancedAt B_MIDROOT ∧
          R.BalancedAt B_ROOT ∧ R.BalancedAt B_UPB ∧ R.BalancedAt B_MEMD ∧ R.BalancedAt B_RPL ∧
          R.BalancedAt B_RPLV) ∧
        -- shared buses
        R.BalancedAt B_SIZE ∧ R.BalancedAt B_VSLOT ∧ R.BalancedAt B_KEYNIB ∧ R.BalancedAt B_FINAL ∧
        R.BalancedAt B_BYTES ∧ R.BalancedAt B_DIGEST := by
  obtain ⟨writes, oldPost, q, us, r0, r1, r2, r3, r4, r5, r6, r7, r21, hr, hkf, hus, hpin, hups, hval, hall⟩ :=
    rcpt_trie_side A hovh
  obtain ⟨bs, hc, hg, hres, hctx, r11, htr, htf, hb, hd⟩ := codec_premises A A.pub us hpin
  refine ⟨writes, oldPost, q, us, r0, r1, r2, r3, r4, r5, r6, r7, r21, r11, bs, hr, hkf, hus, hpin, hups, hval, hc, hg, hres,
    hctx, htr, htf, ?_⟩
  intro R e0 e1 e2 e3 e4 e5 e6 e7 h16 h17 h18 h19 h20 e21 h22 h23 e11 h24
  obtain ⟨hrc, htrie, hsz, hvs, hkn, hfin, hB, hD⟩ :=
    hall R e0 e1 e2 e3 e4 e5 e6 e7 h16 h17 h18 h19 h20 e21 h22 h23 h24
  have t11 : R.tf 11 = r11.tf := bundle_tf_eq R 11 _ e11
  exact ⟨hrc, htrie, hsz, hvs, hkn, hfin, hB (by rw [t11]; exact hb), hD (by rw [t11]; exact hd)⟩

end ZkFormal.NearV3.Assembly.RcptTrieSide
