import ZkFormal.NearV3.Render.CodecScmp
import ZkFormal.NearV3.Render.SchedScmp

/-!
# `B_SCMP` balanced on one block list

`codec_cmps_ok`: the repaired codec's comparisons of `GrantWit` blocks are valid.  `sched_renders_on`: tables
12–15 rendered on a GIVEN `PriorCore` block list (as `sched_renders_accepted`, same proof).
**`balancedAt_scmp`**: a bundle whose tables 11–15 are the codec, scan/distribute, process, memory and comparator
renders of the same blocks of `A`'s trace balances `B_SCMP`.
-/
namespace ZkFormal.NearV3.Render
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Assembly
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen NearSpec NearSpecV3
open ZkFormal.NearV3.Assembly.CodecDigest ZkFormal.NearV3.Candidates

theorem codec_cmps_ok {cb : Bytes} {hint : Hint} {p : Prep} (hp : prepD0 cb hint = .ok p) {B : Nat}
    {bs : List NativeBlock} (hc : PriorCore p B bs) (hg : ∀ b ∈ bs, CdcGrant.GrantWit b) :
    ∀ b ∈ bs, ∀ q ∈ b.output.cmps, Complete.CmpOk q := by
  intro b hb
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hb
  obtain ⟨⟨hsch, hr⟩, -, -⟩ := hc.indexed i b hi
  have hval := (hc.valid b hb).1
  have hs := prepD0_sched hp b.pub (List.mem_of_getElem? hsch)
  have ha := (ProcActualPublic.schedPub_fields b.witness.ctx b.pub hval.2.2.1).1
  obtain ⟨cv, st, rs, ev, sord, rord, hprefix, hgd⟩ := hg b hb
  exact ProcCodecComparisonValidNative.native b.pub hs ha b.old i cv rs st ev b.run b.grants sord rord
    hprefix hr hgd b.prior.isSome b.vid b.forwarded b.output hval.2.2.2.2

/-- Tables 12–15 on a given block list. -/
theorem sched_renders_on {cb : Bytes} {hint : Hint} {p : Prep} (hp : prepD0 cb hint = .ok p)
    (pub : List Fp) (bs : List NativeBlock) (hc : PriorCore p B0 bs)
    (hcodec : ∀ b ∈ bs, ∀ q ∈ b.output.cmps, Complete.CmpOk q) :
    ∃ (R12 : TableRenderV3 pub 12 (by decide)) (R13 : TableRenderV3 pub 13 (by decide))
        (R14 : TableRenderV3 pub 14 (by decide)) (R15 : TableRenderV3 pub 15 (by decide)),
      R12.tr = ProcScanDistPhases.trace bs ∧
      R12.tf = rowsTraffic ScanDist.table.interactions (Ssd.ssdCell bs) 22 12 pub ∧
      R13.tr = procTraceV3 (bs.map NativeBlock.run) ∧
      R13.tf = rowsTraffic Proc.tableB.interactions (procCell (bs.map NativeBlock.run)) 22 13 pub ∧
      R14.tr = MemConcatCells.trace (bs.map NativeBlock.run) ∧
      R14.tf = rowsTraffic Mem.table.interactions (memAllCell (bs.map NativeBlock.run)) 22 14 pub ∧
      R15.tr = cmpTraceAligned (ProcNativeOldComparisonCapacity.requests bs) ∧
      R15.tf = cmpTraffic (ProcNativeOldComparisonCapacity.requests bs) := by
  have hok := old_requests_ok hp bs hc hcodec
  have hlen := (ProcNativeOldComparisonCapacity.native_bound hp bs hc).1
  refine ⟨ssdRenderV3 pub hp bs hc, ?_, memAllRenderV3 pub hp bs hc,
    cmpRenderV3 pub _ hok (by omega), rfl, rfl, ?_⟩
  · refine procRenderV3 pub (bs.map NativeBlock.run) ?_ ?_ ?_ (prior_run_capacities hp _ bs hc).2
    · intro R hR
      obtain ⟨sp, prev, hs, hr, _⟩ := prior_run_data hp _ bs hc R hR
      exact ⟨ProcPreparedSequence.input sp prev, hs.params, hr⟩
    · intro R rest he
      exact prior_run_index p _ bs hc 0 R (by rw [he]; rfl)
    · intro pre R S post he
      have hR : R.tau = pre.length := prior_run_index p _ bs hc pre.length R (by
        rw [he, List.getElem?_append_right (by omega)]
        simp)
      have hS : S.tau = pre.length + 1 := prior_run_index p _ bs hc (pre.length + 1) S (by
        rw [he, List.getElem?_append_right (by omega)]
        simp)
      omega
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end ZkFormal.NearV3.Render

namespace ZkFormal.NearV3.Assembly
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.NearV3.Render

open ZkFormal.NearV3.Assembly.CodecDigest ZkFormal.NearV3.Render.Cdc ZkFormal.NearV3.Render.CdcGrant
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Candidates

theorem covers_scmp_send : Covers Sched.B_SCMP true (fun t => t == 11 || t == 12 || t == 13 || t == 14) = true := by
  decide +kernel
theorem covers_scmp_recv : Covers Sched.B_SCMP false (fun t => t == 15) = true := by decide +kernel
theorem pub_scmp (s : Bool) (pub m : List Fp) : pubCount nearAirV3 pub Sched.B_SCMP s m = 0 :=
  pub_off _ _ (by cases s <;> decide +kernel) pub m

namespace RenderBundleV3

/-- **`B_SCMP` balance** of a bundle whose tables 11–15 render the same blocks of `A`'s trace. -/
theorem balancedAt_scmp {cb wb : NearSpec.Bytes} (A : AcceptedV3 cb wb) (R : RenderBundleV3 A.pub)
    {bs : List NativeBlock} (hc : PriorCore A.p NearSpecV3.B0 bs)
    (hctx : bs.map (fun b => (b.witness.ctx, b.witness.pre)) =
      (A.m.ctx A.k, A.m.pre) :: A.steps.map (fun e => (implicitCtx A.k e, e.pre)))
    (h11 : R.tf 11 = rowsTraffic Sched.Codec.table.interactions (codecCell (bs.map blkOf)) 22 11 A.pub)
    (h12 : (R ⟨12, by decide⟩).tr = ProcScanDistPhases.trace bs)
    (h13 : (R ⟨13, by decide⟩).tr = procTraceV3 (bs.map NativeBlock.run))
    (h14 : (R ⟨14, by decide⟩).tr = MemConcatCells.trace (bs.map NativeBlock.run))
    (h15 : (R ⟨15, by decide⟩).tr = cmpTraceAligned (ProcNativeOldComparisonCapacity.requests bs)) :
    R.BalancedAt Sched.B_SCMP := by
  intro m
  rw [R.sum_tables true _ m _ covers_scmp_send, R.sum_tables false _ m _ covers_scmp_recv, pub_scmp, pub_scmp]
  have hf1 : (List.range 25).filter (fun t => t == 11 || t == 12 || t == 13 || t == 14) = [11, 12, 13, 14] := by
    decide
  have hf2 : (List.range 25).filter (fun t => t == 15) = [15] := by decide
  rw [hf1, hf2]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
  rw [R.cnt_tf 12 (by decide) true, R.cnt_tf 13 (by decide) true, R.cnt_tf 14 (by decide) true,
    R.cnt_tf 15 (by decide) false, h12, h13, h14, h15]
  have hs : sel true (R.tf 11) Sched.B_SCMP =
      natMsgs ((bs.flatMap fun b => b.output.cmps).map Sched.Complete.cmpMsg) := by
    rw [h11]
    simp only [sel, ite_true]
    unfold rowsTraffic
    dsimp only
    rw [CdcScmp.codec_scmp_native A hc hctx 11 A.pub]
  rw [hs]
  have hcore := scmp_balance_core A.hp bs hc 12 13 14 15 A.pub m
  unfold cnt
  rw [natMsgs_toFp]
  have i12 : nearAirV3.tables[12].interactions = ScanDist.table.interactions := rfl
  have i13 : nearAirV3.tables[13].interactions = Proc.tableB.interactions := rfl
  have i14 : nearAirV3.tables[14].interactions = Mem.interactions := rfl
  have i15 : nearAirV3.tables[15].interactions = (Cmp.table B_SCMP).interactions := rfl
  rw [i12, i13, i14, i15]
  omega

end RenderBundleV3
end ZkFormal.NearV3.Assembly
