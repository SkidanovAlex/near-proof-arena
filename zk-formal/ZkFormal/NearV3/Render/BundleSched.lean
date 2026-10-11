import ZkFormal.NearV3.Assembly.RenderV3Bundle
import ZkFormal.NearV3.Render.PaddedSha
import ZkFormal.NearV3.Render.PaddedChacha
import ZkFormal.NearV3.Render.PaddedSched
import ZkFormal.NearV3.Render.PaddedProc
import ZkFormal.NearV3.Render.PaddedMrk
import ZkFormal.NearV3.Render.PaddedSort
import ZkFormal.NearV3.Render.PaddedUpsNative
import ZkFormal.NearV3.Assembly.SchedulerRunProcessLocal

/-!
# `TableRenderV3` instances of this lane's renders (tables 0, 1, 7, 8–10, 13–15, 23, 24)

Each instance packages an aligned render (`Render/Padded*.lean`) at its fixed `nearAirV3` index
under the render's explicit honest-input hypotheses.  Discharging those hypotheses from
`checkD0a B0` acceptance is done per table where available (`SortV3.sort_v3_accepted`); the
rest are the render premises listed in each constructor.
-/
namespace ZkFormal.NearV3.Render
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Assembly
open ZkFormal.NearV3.Sched NearSpec NearSpecV3

/-- Table 0 / 1: SHA-256. -/
def shaRenderV3 (pub : List Fp) (t : Nat) (ht : t < nearAirV3.tables.length) (h01 : t = 0 ∨ t = 1)
    (msgs : List Sha.Gen.Msg) (hok : Sha.MsgsOk msgs) : TableRenderV3 pub t ht where
  tr := shaTraceAligned msgs
  tf := shaBinTraffic msgs
  loc := by
    have h := (sha_aligned_complete msgs hok t pub).1
    rcases h01 with rfl | rfl <;> exact h
  traffic := by
    have h := (sha_aligned_complete msgs hok t pub).2.1
    rcases h01 with rfl | rfl <;> exact h
  aligned := (sha_aligned_complete msgs hok t pub).2.2

/-- Table 7: `upsV3`, from native instance data. -/
def upsRenderV3 (pub : List Fp) (ds : List UpsGen.UpsNativeData) (hok : ∀ d ∈ ds, UpsGen.UpsNativeOk d)
    (hpos : 0 < ds.length) (hcap : UpsGen.R (ds.map UpsGen.UpsNativeData.inst) + 1 ≤ 2 ^ 22) :
    TableRenderV3 pub 7 (by decide) where
  tr := upsTraceAligned (ds.map UpsGen.UpsNativeData.inst)
  tf := upsTraffic (UpsRows.viewOf (upsTraceAligned (ds.map UpsGen.UpsNativeData.inst)) 7
    (UpsGen.segsOf (ds.map UpsGen.UpsNativeData.inst)))
  loc := (UpsGen.ups_native_aligned_complete ds hok hpos hcap 7 pub).1
  traffic := (UpsGen.ups_native_aligned_complete ds hok hpos hcap 7 pub).2.1
  aligned := (UpsGen.ups_native_aligned_complete ds hok hpos hcap 7 pub).2.2

/-- Table 8: ChaCha20 blocks. -/
def chachaRenderV3 (pub : List Fp) (reqs : List Chacha.Gen.Req) (hok : ∀ R ∈ reqs, Chacha.Gen.ReqOk R)
    (hrows : 86 * reqs.length ≤ 2 ^ 22) : TableRenderV3 pub 8 (by decide) where
  tr := chachaTraceAligned reqs
  tf := chachaTraffic reqs
  loc := (chacha_v3_aligned_complete reqs hok hrows 8 pub).1
  traffic := (chacha_v3_aligned_complete reqs hok hrows 8 pub).2.1
  aligned := (chacha_v3_aligned_complete reqs hok hrows 8 pub).2.2

/-- Table 9: the RNG / `gen_index` table. -/
def rngRenderV3 (pub : List Fp) (calls : List Chacha.Rng.Gen.Call)
    (hok : ∀ C ∈ calls, Chacha.Rng.Gen.CallOk C) (hrows : rngRows calls ≤ 2 ^ 22) :
    TableRenderV3 pub 9 (by decide) where
  tr := rngTraceAligned calls
  tf := rngTraffic calls
  loc := (rng_v3_aligned_complete calls hok hrows 9 pub).1
  traffic := (rng_v3_aligned_complete calls hok hrows 9 pub).2.1
  aligned := (rng_v3_aligned_complete calls hok hrows 9 pub).2.2

/-- Table 10: the shuffle table. -/
def shufRenderV3 (pub : List Fp) (insts : List Chacha.Shuffle.Gen.SInst)
    (hok : ∀ I ∈ insts, Chacha.Shuffle.Complete.InstOk I) (hrows : shufRows insts ≤ 2 ^ 22) :
    TableRenderV3 pub 10 (by decide) where
  tr := shufTraceAligned insts
  tf := shufTraffic insts
  loc := (shuf_aligned_complete22 insts hok hrows 10 pub).1
  traffic := (shuf_aligned_complete22 insts hok hrows 10 pub).2.1
  aligned := (shuf_aligned_complete22 insts hok hrows 10 pub).2.2

/-- Table 13: the boundary-repaired process table over all runs. -/
def procRenderV3 (pub : List Fp) (rs : List Gen.Run)
    (hr : ∀ R ∈ rs, ∃ I : Gen.Input,
      NearSpecV3.Scheduler.Params.calculate NearSpecV3.Scheduler.Config.pv86 I.ids.length = some I.p ∧
      Gen.ActualRun.run I R.tau = .ok R)
    (hfirst : ∀ R rest, rs = R :: rest → R.tau = 0)
    (ht : ∀ pre R S post, rs = pre ++ R :: S :: post → S.tau = R.tau + 1)
    (hcap : (ZkFormal.NearV3.Candidates.ProcConcatGeometry.rows rs).length + 1 ≤ 2 ^ 22) :
    TableRenderV3 pub 13 (by decide) where
  tr := procTraceV3 rs
  tf := rowsTraffic Proc.tableB.interactions (procCell rs) 22 13 pub
  loc := (proc_v3_aligned_complete rs hr hfirst ht hcap 13 pub).1
  traffic := (proc_v3_aligned_complete rs hr hfirst ht hcap 13 pub).2.1
  aligned := (proc_v3_aligned_complete rs hr hfirst ht hcap 13 pub).2.2

/-- Table 14: scheduler memory. -/
def memRenderV3 (pub : List Fp) (R : Gen.Run) (hg : ∀ g ∈ R.segs, Complete.SegOk g)
    (hrows : (Complete.memVs R.segs).length + 1 ≤ 2 ^ 22) : TableRenderV3 pub 14 (by decide) where
  tr := memTraceAligned R
  tf := memTraffic R
  loc := (mem_aligned_complete R hg hrows 14 pub).1
  traffic := (mem_aligned_complete R hg hrows 14 pub).2.1
  aligned := (mem_aligned_complete R hg hrows 14 pub).2.2

/-- Table 15: the comparator. -/
def cmpRenderV3 (pub : List Fp) (cmps : List (Nat × Nat × Nat)) (hok : ∀ q ∈ cmps, Complete.CmpOk q)
    (hrows : cmps.length ≤ 2 ^ 22) : TableRenderV3 pub 15 (by decide) where
  tr := cmpTraceAligned cmps
  tf := cmpTraffic cmps
  loc := (cmp_aligned_complete cmps hok hrows 15 pub).1
  traffic := (cmp_aligned_complete cmps hok hrows 15 pub).2.1
  aligned := (cmp_aligned_complete cmps hok hrows 15 pub).2.2

/-- Table 23: the outcome Merkle tree (empty tree included). -/
def mrkRenderV3 (pub : List Fp) (os : List NearSpec.Outcome) (hn : os.length ≤ 4481)
    (hp : ∀ i < 4, pub.getD (ZkFormal.NearV3.PH_N + i) 0 = Fp.ofNat (os.length / 256 ^ i % 256))
    (ho : ∀ i < 32, pub.getD (ZkFormal.NearV3.PH_OUT + i) 0 =
      Fp.ofNat (((NearSpec.outcomeRoot os).getD i 0).toNat)) :
    TableRenderV3 pub 23 (by decide) where
  tr := mrkTraceV3 os pub
  tf := mrkTrafficE pub (decide (os = [])) (Candidates.MerkleRender.generatedView os.length (mrkLevels os))
  loc := by
    have h := (mrk_v3_aligned_complete os pub hn hp ho).1
    exact ⟨h.log_ge, h.log_le, fun r hr e he => h.constr r hr e he, fun r hr i hi b hb => h.bits r hr i hi b hb⟩
  traffic := by
    have h := (mrk_v3_aligned_complete os pub hn hp ho).2.1
    exact fun b m => h b m
  aligned := (mrk_v3_aligned_complete os pub hn hp ho).2.2

/-- Table 24: receipt-id sort, from acceptance (receipt lane's RIDS traffic). -/
def sortRenderV3 (pub : List Fp) {cb wb raw : NearSpec.Bytes} {k : NearSpecV3.WalkD0}
    {w : NearSpecV3.StateWitness} {m : MainExecutionV3}
    (hk : NearSpecV3.walkD0 cb = .ok k) (hw : NearSpecV3.decodeW wb = .ok w)
    (hr : NearSpecV3.decodeStateWitness raw = .ok w)
    (hc : NearSpecV3.checkD0a NearSpecV3.B0 cb wb = .ok ()) (hm : m.NativeValid k w)
    (lists : List (List RcptSkeleton.Input))
    (hls : lists.flatten.map RcptSkeleton.Input.receipt = appliedReceipts k w) :
    TableRenderV3 pub 24 (by decide) where
  tr := SortV3.sortTraceV3 (lists.flatten.map RcptSkeleton.Input.receipt)
  tf := sortTraffic (Candidates.NativeSortIds.input (lists.flatten.map RcptSkeleton.Input.receipt))
  loc := (SortV3.sort_v3_accepted hk hw hr hc hm lists hls 24 pub).1
  traffic := (SortV3.sort_v3_accepted hk hw hr hc hm lists hls 24 pub).2.1
  aligned := (SortV3.sort_v3_accepted hk hw hr hc hm lists hls 24 pub).2.2

end ZkFormal.NearV3.Render

namespace ZkFormal.NearV3.Render
open ZkFormal.Near ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Assembly
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen NearSpec NearSpecV3
open ZkFormal.NearV3.Assembly.CodecDigest

/-- **Table 13 from acceptance.** For an accepted witness the native scheduler blocks of
`accepted_prior_core` supply every premise of the process render (native runs, `τ = index`,
capacity); the rendered runs are `bs.map NativeBlock.run`. -/
theorem procRender_accepted {cb wb : Bytes} {hint : Hint} {p : Prep} (hp : prepD0 cb hint = .ok p)
    {k : WalkD0} {w : StateWitness} (hk : walkD0 cb = .ok k) (hw : decodeW wb = .ok w)
    (h : checkD0a B0 cb wb = .ok ()) (pub : List Fp) :
    ∃ bs : List NativeBlock, ∃ R : TableRenderV3 pub 13 (by decide),
      R.tr = procTraceV3 (bs.map NativeBlock.run) ∧
      R.tf = rowsTraffic Proc.tableB.interactions (procCell (bs.map NativeBlock.run)) 22 13 pub := by
  obtain ⟨bs, hc⟩ := accepted_prior_core hp hk hw h (by decide)
  refine ⟨bs, procRenderV3 pub (bs.map NativeBlock.run) ?_ ?_ ?_ (prior_run_capacities hp _ bs hc).2,
    rfl, rfl⟩
  · intro R hR
    obtain ⟨sp, prev, hs, hr, _⟩ := prior_run_data hp _ bs hc R hR
    exact ⟨ZkFormal.NearV3.Candidates.ProcPreparedSequence.input sp prev, hs.params, hr⟩
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

end ZkFormal.NearV3.Render
