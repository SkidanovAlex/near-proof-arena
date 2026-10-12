import ZkFormal.NearV3.Render.SchedBusSA0
import ZkFormal.NearV3.Render.SchedBusSDL
import ZkFormal.NearV3.Render.SchedBusSPAR
import ZkFormal.NearV3.Render.SchedBusSPUSH
import ZkFormal.NearV3.Render.SchedBusSINC
import ZkFormal.NearV3.Render.SchedBusSFIN
import ZkFormal.NearV3.Render.SchedBusSOP
import ZkFormal.NearV3.Render.SchedBusSPUBB
import ZkFormal.NearV3.Render.SchedBusSDLX
import ZkFormal.NearV3.Render.SchedBusSDG
import ZkFormal.NearV3.Render.SchedBusPackaging

/-!
# All remaining scheduler buses balance on the honest render

**`sched_buses_balanced`**: a bundle whose table 11 is the codec render and whose tables 12–14 are the
scan/distribute, process and memory renders of the `PriorCore` blocks of `A`'s trace (exactly what
`rcpt_trie_sched` and `sched_renders_on` provide) balances `SOP` (41), `SFIN` (42), `SINC` (43),
`SPUSH` (44), `SPUBB` (51), `SPAR` (52), `SDL` (56), `SDLX` (57), `SDG` (58) and `SA0` (62).  With
`balancedAt_scmp` (40) and the codec ↔ ups buses of `rcpt_trie_sched` (59–61) every scheduler bus is
covered; ChaCha (45–50) is lane v3-render-chacha's.
-/
set_option autoImplicit false
namespace ZkFormal.NearV3.Assembly
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.NearV3.Render
open ZkFormal.NearV3.Assembly.CodecDigest ZkFormal.NearV3.Candidates NearSpec NearSpecV3

namespace RenderBundleV3

/-- **The scheduler buses 41–44, 51, 52, 56–58, 62 balance** on the honest render of `A`. -/
theorem sched_buses_balanced {cb wb : Bytes} (A : AcceptedV3 cb wb) (R : RenderBundleV3 A.pub)
    {bs : List NativeBlock} (hc : PriorCore A.p B0 bs) (hg : ∀ b ∈ bs, CdcGrant.GrantWit b)
    (hctx : bs.map (fun b => (b.witness.ctx, b.witness.pre)) =
      (A.m.ctx A.k, A.m.pre) :: A.steps.map (fun e => (implicitCtx A.k e, e.pre)))
    (hfw : ∀ b, bs[0]? = some b → b.forwarded = fwdLinks (A.m.ctx A.k) A.m.result.outgoing)
    (h11 : R.tf 11 = rowsTraffic Sched.Codec.table.interactions (Cdc.codecCell (bs.map Cdc.blkOf)) 22 11 A.pub)
    (h12 : (R ⟨12, by decide⟩).tr = ProcScanDistPhases.trace bs)
    (h13 : (R ⟨13, by decide⟩).tr = procTraceV3 (bs.map NativeBlock.run))
    (h14 : (R ⟨14, by decide⟩).tr = MemConcatCells.trace (bs.map NativeBlock.run)) :
    R.BalancedAt Sched.B_SOP ∧ R.BalancedAt Sched.B_SFIN ∧ R.BalancedAt Sched.B_SINC ∧
      R.BalancedAt Sched.B_SPUSH ∧ R.BalancedAt Sched.B_SPUBB ∧ R.BalancedAt Sched.B_SPAR ∧
      R.BalancedAt Sched.B_SDL ∧ R.BalancedAt Sched.B_SDLX ∧ R.BalancedAt Sched.B_SDG ∧
      R.BalancedAt Sched.B_SA0 := by
  have hlen : bs.length = A.steps.length + 1 := by
    have := congrArg List.length hctx; simpa using this
  exact ⟨R.balancedAt_sop A hc hctx h11 h12 h13 h14, R.balancedAt_sfin A.hp hc h11 h12 h14,
    R.balancedAt_sinc A.hp hc h12 h13, R.balancedAt_spush A.hp hc h12 h13,
    R.balancedAt_spubb A hc hlen hfw h11 h13, R.balancedAt_spar A hc hlen h11 h12,
    R.balancedAt_sdl A hc hlen h11, R.balancedAt_sdlx A hc h12, R.balancedAt_sdg A hc hg h11 h12,
    R.balancedAt_sa0 hc h11⟩

end RenderBundleV3

/-- **The scheduler side of the honest render, packaged**: given the `PriorCore` blocks and the codec
render `r11` exported by `rcpt_trie_sched`, the renders of tables 12–15 exist and every bundle carrying
`r11 … r15` balances all eleven scheduler buses 40–44, 51, 52, 56–58, 62. -/
theorem sched_side {cb wb : Bytes} (A : AcceptedV3 cb wb)
    {bs : List NativeBlock} (hc : PriorCore A.p B0 bs) (hg : ∀ b ∈ bs, CdcGrant.GrantWit b)
    (hctx : bs.map (fun b => (b.witness.ctx, b.witness.pre)) =
      (A.m.ctx A.k, A.m.pre) :: A.steps.map (fun e => (implicitCtx A.k e, e.pre)))
    (hfw : ∀ b, bs[0]? = some b → b.forwarded = fwdLinks (A.m.ctx A.k) A.m.result.outgoing)
    (r11 : TableRenderV3 A.pub 11 (by decide))
    (htf : r11.tf = rowsTraffic Sched.Codec.table.interactions (Cdc.codecCell (bs.map Cdc.blkOf)) 22 11 A.pub) :
    ∃ (r12 : TableRenderV3 A.pub 12 (by decide)) (r13 : TableRenderV3 A.pub 13 (by decide))
      (r14 : TableRenderV3 A.pub 14 (by decide)) (r15 : TableRenderV3 A.pub 15 (by decide)),
      ∀ R : RenderBundleV3 A.pub, R ⟨11, by decide⟩ = r11 → R ⟨12, by decide⟩ = r12 →
        R ⟨13, by decide⟩ = r13 → R ⟨14, by decide⟩ = r14 → R ⟨15, by decide⟩ = r15 →
        R.BalancedAt Sched.B_SCMP ∧ R.BalancedAt Sched.B_SOP ∧ R.BalancedAt Sched.B_SFIN ∧
        R.BalancedAt Sched.B_SINC ∧ R.BalancedAt Sched.B_SPUSH ∧ R.BalancedAt Sched.B_SPUBB ∧
        R.BalancedAt Sched.B_SPAR ∧ R.BalancedAt Sched.B_SDL ∧ R.BalancedAt Sched.B_SDLX ∧
        R.BalancedAt Sched.B_SDG ∧ R.BalancedAt Sched.B_SA0 := by
  obtain ⟨r12, r13, r14, r15, h12, -, h13, -, h14, -, h15, -⟩ :=
    sched_renders_on A.hp A.pub bs hc (codec_cmps_ok A.hp hc hg)
  refine ⟨r12, r13, r14, r15, fun R e11 e12 e13 e14 e15 => ?_⟩
  have f11 : R.tf 11 = rowsTraffic Sched.Codec.table.interactions (Cdc.codecCell (bs.map Cdc.blkOf)) 22 11 A.pub := by
    rw [bundle_tf_eq R 11 _ e11, htf]
  have f12 : (R ⟨12, by decide⟩).tr = ProcScanDistPhases.trace bs := by rw [e12, h12]
  have f13 : (R ⟨13, by decide⟩).tr = procTraceV3 (bs.map NativeBlock.run) := by rw [e13, h13]
  have f14 : (R ⟨14, by decide⟩).tr = MemConcatCells.trace (bs.map NativeBlock.run) := by rw [e14, h14]
  have f15 : (R ⟨15, by decide⟩).tr = cmpTraceAligned (ProcNativeOldComparisonCapacity.requests bs) := by
    rw [e15, h15]
  exact ⟨R.balancedAt_scmp A hc hctx f11 f12 f13 f14 f15,
    R.sched_buses_balanced A hc hg hctx hfw f11 f12 f13 f14⟩

end ZkFormal.NearV3.Assembly
