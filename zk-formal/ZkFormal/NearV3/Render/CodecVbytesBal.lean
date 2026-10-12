import ZkFormal.NearV3.Render.VbytesNative
import ZkFormal.NearV3.Render.MposBal

/-!
# `VBYTES` (bus 21) balance of the honest render; `rcpt_trie_vbytes`

Senders: codec (11, a present prior's bytes at its value id), account (17, the written account
values, one per distinct key), access key (18, one per distinct key), queue values (22, the queue
providers); receiver: the value table (4, every non-empty value occurrence of the pre forest, duplicate
contents included).  No public messages.

* **`RenderBundleV3.balancedAt_vbytes`**: from `VbytesPart.vbytes_native` (the native partition) and
  `CdcGrant.codec_vbytes_native` (the codec's closed form).
* **`RcptTrieSide.rcpt_trie_vbytes`**: `rcpt_trie_sched` with `VBYTES` and `MPOS` balanced as well.
-/
namespace ZkFormal.NearV3.Assembly
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.NearV3.Render
open ZkFormal.NearV3.Assembly.CodecDigest ZkFormal.NearV3.Render.Cdc ZkFormal.NearV3.Render.CdcGrant RcptSkeleton
open ZkFormal.NearV3.Rcpt.Candidates ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate

theorem covers_vbytes_send :
    Covers B_VBYTES true (fun t => t == 11 || t == 17 || t == 18 || t == 22) = true := by decide +kernel
theorem covers_vbytes_recv : Covers B_VBYTES false (fun t => t == 4) = true := by decide +kernel
theorem pub_vbytes (s : Bool) (pub m : List Fp) : pubCount nearAirV3 pub B_VBYTES s m = 0 :=
  pub_off _ _ (by cases s <;> decide +kernel) pub m

namespace RenderBundleV3

/-- **`VBYTES` balances** on every bundle carrying the honest value (4), codec (11), account (17),
access-key (18) and queue (22) renders of an accepted witness. -/
theorem balancedAt_vbytes {cb wb : NearSpec.Bytes} (A : AcceptedV3 cb wb) (R : RenderBundleV3 A.pub)
    {writes : List (List Nat × NearSpec.Bytes)} {oldPost : NearSpec.PTrie}
    (hr : SizedAccountRun A.m.pre writes oldPost) (hkf : KeysFinal A.k A.w A.m writes oldPost)
    {B : Nat} {bs : List NativeBlock} (hc : PriorCore A.p B bs) (hres : ∀ b ∈ bs, NatRes b)
    (hctx : bs.map (fun b => (b.witness.ctx, b.witness.pre)) =
      (A.m.ctx A.k, A.m.pre) :: A.steps.map (fun e => (implicitCtx A.k e, e.pre)))
    (h11 : R.tf 11 = rowsTraffic Sched.Codec.table.interactions (codecCell (bs.map blkOf)) 22 11 A.pub)
    (h4 : ExtOf (R ⟨4, by decide⟩).tf (valTraffic (TrieNative.vals A.m A.steps)))
    (h17 : R ⟨17, by decide⟩ = A.rcptRenders.acct) (h18 : R ⟨18, by decide⟩ = A.rcptRenders.akey)
    (h22 : R ⟨22, by decide⟩ = A.rcptRenders.qv) :
    R.BalancedAt B_VBYTES := by
  intro m
  rw [R.sum_tables true _ m _ covers_vbytes_send, R.sum_tables false _ m _ covers_vbytes_recv,
    pub_vbytes, pub_vbytes]
  have e4 := R.tf_ext 4 (by decide) h4 B_VBYTES (by decide) (by decide) (by decide)
  have hf1 : (List.range 25).filter (fun t => t == 11 || t == 17 || t == 18 || t == 22) = [11, 17, 18, 22] := by
    decide
  have hf2 : (List.range 25).filter (fun t => t == 4) = [4] := by decide
  have t17 : R.tf 17 = acctV3Traffic A.accts := bundle_tf_eq R 17 _ h17
  have t18 : R.tf 18 = akeyTraffic A.akeys := bundle_tf_eq R 18 _ h18
  have t22 : R.tf 22 = qvNativeTraffic A.m.pre A.qvVals (A.steps.map ImplicitStepV3.pre) :=
    bundle_tf_eq R 22 _ h22
  have hs : (R.tf 11).sends B_VBYTES = natMsgs (bs.flatMap priorMsgs) := by
    rw [h11]
    unfold rowsTraffic
    dsimp only
    rw [codec_vbytes_native A hc hres hctx 11 A.pub]
  have hF : bs.map (·.witness.pre) = A.m.pre :: A.steps.map ImplicitStepV3.pre := by
    have h := congrArg (List.map Prod.snd) hctx
    simpa [List.map_map, Function.comp_def] using h
  have key := VbytesPart.vbytes_native A hr hkf hc hF m
  rw [hf1, hf2]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, sel, ite_true,
    Bool.false_eq_true, ite_false, t17, t18, t22, e4.2, Nat.add_zero, hs]
  simp only [acctV3Traffic, akeyTraffic, valTraffic]
  simp only [ZkFormal.Near.cnt, ZkFormal.NearV3.Assembly.cnt, natMsgs_toFp] at key ⊢
  omega

end RenderBundleV3
end ZkFormal.NearV3.Assembly

namespace ZkFormal.NearV3.Assembly.RcptTrieSide
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3 ZkFormal.NearV3.Assembly
  Render Rcpt.Candidates Rcpt.Candidates.NodePostUpdate RcptSkeleton RcptBal ZkFormal.NearV3.UnfoldA7 TrieA7
open ZkFormal.NearV3.Assembly.CodecDigest ZkFormal.NearV3.Render.Cdc ZkFormal.NearV3.Render.CdcGrant

/-- **`rcpt_trie_sched` plus `VBYTES` (21) and `MPOS` (9).** Same hypotheses and witnesses as
`rcpt_trie_sched`. -/
theorem rcpt_trie_vbytes {cb wb : Bytes} (A : AcceptedV3 cb wb)
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
        ((-- receipt-side buses
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
        R.BalancedAt B_BYTES ∧ R.BalancedAt B_DIGEST) ∧
        R.BalancedAt ZkFormal.NearV3.B_SPLEN ∧ R.BalancedAt ZkFormal.NearV3.B_SPOST ∧
        R.BalancedAt ZkFormal.NearV3.B_S0F) ∧
        R.BalancedAt B_VBYTES ∧ R.BalancedAt B_MPOS := by
  obtain ⟨writes, oldPost, q, us, r0, r1, r2, r3, r4, r5, r6, r7, r21, r11, bs, hr, hkf, hus, hpin, hups, hval,
    hc, hg, hres, hctx, htr, htf, hall⟩ := rcpt_trie_sched A hovh
  refine ⟨writes, oldPost, q, us, r0, r1, r2, r3, r4, r5, r6, r7, r21, r11, bs, hr, hkf, hus, hpin, hups, hval,
    hc, hg, hres, hctx, htr, htf, ?_⟩
  intro R e0 e1 e2 e3 e4 e5 e6 e7 h16 h17 h18 h19 h20 e21 h22 h23 e11 h24
  refine ⟨hall R e0 e1 e2 e3 e4 e5 e6 e7 h16 h17 h18 h19 h20 e21 h22 h23 e11 h24, ?_, ?_⟩
  · have h11 : R.tf 11 = rowsTraffic Sched.Codec.table.interactions (codecCell (bs.map blkOf)) 22 11 A.pub := by
      rw [bundle_tf_eq R 11 _ e11, htf]
    have h4 : ExtOf (R ⟨4, by decide⟩).tf (valTraffic (TrieNative.vals A.m A.steps)) := by rw [e4]; exact hval
    exact R.balancedAt_vbytes A hr hkf hc hres hctx h11 h4 h17 h18 h22
  · exact R.balancedAt_mpos A h16 h23

end ZkFormal.NearV3.Assembly.RcptTrieSide
