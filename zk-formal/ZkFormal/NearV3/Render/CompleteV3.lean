import ZkFormal.NearV3.Render.CodecVbytesBal
import ZkFormal.NearV3.Render.SchedBusAll
import ZkFormal.NearV3.Render.SchedBusPackaging
import ZkFormal.NearV3.Render.BundleSched
import ZkFormal.NearV3.Assembly.RenderV3Header
import ZkFormal.NearV3.Assembly.SizeBudgetAccepted

/-!
# Completeness of the D0a certificate: `CompleteV3Stmt` from the ChaCha side

The full 25-table honest render of an accepted witness, assembled from the per-side results:

* tables 0–7, 21 (trie), 11 (codec), 16–20, 22 (receipt), 23 (`mrkAcc`) and the balances of every
  receipt, trie, shared and codec ↔ ups bus, plus `VBYTES` and `MPOS`: `RcptTrieSide.rcpt_trie_vbytes`
  (with `AcceptedV3.sizeBudget`);
* tables 12–15 (`sched_renders_on` on the same `PriorCore` blocks) and the eleven scheduler buses 40–44,
  51, 52, 56–58, 62: `balancedAt_scmp`, `sched_buses_balanced`;
* table 24: `sortRenderV3` over the applied receipts (`AcceptedV3.lists_applied`);
* tables 8, 9, 10 and the ChaCha buses 45–50 (and the RNG word bound `rngRows calls ≤ W0` that the
  table-9 render needs): **`ChachaSideV3`**, the single open piece (lane v3-render-chacha).

Every used bus (`usedBuses`) is then balanced, so the bundle is `Balanced` (`balanced_of_used`); the
header is admissible because table 16 is the honest receipt render (`bundle_headerOk_rcpt`); the hint
bounds are `AcceptedV3.hint_bounds`.

* **`ChachaSideV3`** — the ChaCha obligation, stated over the `PriorCore` blocks of an accepted
  witness: renders of tables 8, 9, 10 exist such that every bundle carrying them and the process render
  of the blocks' runs at table 13 balances buses 45–50.
* **`completeV3_of_chacha : ChachaSideV3 → CompleteV3Stmt`**.
* **`nearV3_admission_of_chacha`** — the admission statement from `ExtractV3Stmt`, `ChachaSideV3` and
  the implementation connection.
-/
set_option autoImplicit false
namespace ZkFormal.NearV3.Assembly
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.NearV3.Render
open ZkFormal.NearV3.Assembly.CodecDigest ZkFormal.NearV3.Render.Cdc ZkFormal.NearV3.Render.CdcGrant RcptSkeleton
open ZkFormal.NearV3.Rcpt.Candidates ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate
open ZkFormal.NearV3.Candidates NearSpec NearSpecV3

/-- The certificate's auxiliary-group parameter (`g = 2`, as in `RenderV3Bundle.lean`). -/
local instance : ZkFormal.Prover.Np.G.AuxG := ⟨2, by decide⟩

/-- **The ChaCha side of the honest render (lane v3-render-chacha).** For the native scheduler blocks
`bs` of an accepted witness (`PriorCore` on its trace, with their grant witnesses, native residues,
contexts and instance-0 forwarding), renders of table 8 (ChaCha20), 9 (RNG, A9 word counter: needs
`rngRows calls ≤ W0`) and 10 (shuffle) exist such that every bundle carrying them, whose table 13 is
the process render of the blocks' runs, balances `SSIN` (45), `SSOUT` (46), `SSMEM` (47), `SGEN` (48),
`SSHUF` (49) and `SCHACHA` (50).  These buses are used only by tables 8, 9, 10 and 13. -/
def ChachaSideV3 : Prop :=
  ∀ {cb wb : Bytes} (A : AcceptedV3 cb wb) (bs : List NativeBlock),
    PriorCore A.p B0 bs → (∀ b ∈ bs, GrantWit b) → (∀ b ∈ bs, NatRes b) →
    bs.map (fun b => (b.witness.ctx, b.witness.pre)) =
      (A.m.ctx A.k, A.m.pre) :: A.steps.map (fun e => (implicitCtx A.k e, e.pre)) →
    (∀ b, bs[0]? = some b → b.forwarded = fwdLinks (A.m.ctx A.k) A.m.result.outgoing) →
    ∃ (r8 : TableRenderV3 A.pub 8 (by decide)) (r9 : TableRenderV3 A.pub 9 (by decide))
      (r10 : TableRenderV3 A.pub 10 (by decide)),
      ∀ R : RenderBundleV3 A.pub,
        R ⟨8, by decide⟩ = r8 → R ⟨9, by decide⟩ = r9 → R ⟨10, by decide⟩ = r10 →
        (R ⟨13, by decide⟩).tr = procTraceV3 (bs.map NativeBlock.run) →
        R.BalancedAt Sched.B_SSIN ∧ R.BalancedAt Sched.B_SSOUT ∧ R.BalancedAt Sched.B_SSMEM ∧
          R.BalancedAt Sched.B_SGEN ∧ R.BalancedAt Sched.B_SSHUF ∧ R.BalancedAt Sched.B_SCHACHA

/-- The bundle with one given render per table index. -/
def bundleOf {pub : List Fp}
    (r0 : TableRenderV3 pub 0 (by decide)) (r1 : TableRenderV3 pub 1 (by decide))
    (r2 : TableRenderV3 pub 2 (by decide)) (r3 : TableRenderV3 pub 3 (by decide))
    (r4 : TableRenderV3 pub 4 (by decide)) (r5 : TableRenderV3 pub 5 (by decide))
    (r6 : TableRenderV3 pub 6 (by decide)) (r7 : TableRenderV3 pub 7 (by decide))
    (r8 : TableRenderV3 pub 8 (by decide)) (r9 : TableRenderV3 pub 9 (by decide))
    (r10 : TableRenderV3 pub 10 (by decide)) (r11 : TableRenderV3 pub 11 (by decide))
    (r12 : TableRenderV3 pub 12 (by decide)) (r13 : TableRenderV3 pub 13 (by decide))
    (r14 : TableRenderV3 pub 14 (by decide)) (r15 : TableRenderV3 pub 15 (by decide))
    (r16 : TableRenderV3 pub 16 (by decide)) (r17 : TableRenderV3 pub 17 (by decide))
    (r18 : TableRenderV3 pub 18 (by decide)) (r19 : TableRenderV3 pub 19 (by decide))
    (r20 : TableRenderV3 pub 20 (by decide)) (r21 : TableRenderV3 pub 21 (by decide))
    (r22 : TableRenderV3 pub 22 (by decide)) (r23 : TableRenderV3 pub 23 (by decide))
    (r24 : TableRenderV3 pub 24 (by decide)) : RenderBundleV3 pub
  | ⟨0, _⟩ => r0 | ⟨1, _⟩ => r1 | ⟨2, _⟩ => r2 | ⟨3, _⟩ => r3 | ⟨4, _⟩ => r4
  | ⟨5, _⟩ => r5 | ⟨6, _⟩ => r6 | ⟨7, _⟩ => r7 | ⟨8, _⟩ => r8 | ⟨9, _⟩ => r9
  | ⟨10, _⟩ => r10 | ⟨11, _⟩ => r11 | ⟨12, _⟩ => r12 | ⟨13, _⟩ => r13 | ⟨14, _⟩ => r14
  | ⟨15, _⟩ => r15 | ⟨16, _⟩ => r16 | ⟨17, _⟩ => r17 | ⟨18, _⟩ => r18 | ⟨19, _⟩ => r19
  | ⟨20, _⟩ => r20 | ⟨21, _⟩ => r21 | ⟨22, _⟩ => r22 | ⟨23, _⟩ => r23 | ⟨24, _⟩ => r24
  | ⟨n + 25, h⟩ => absurd h (by change ¬ n + 25 < 25; omega)

/-- **The full honest render of an accepted witness is balanced**, given the ChaCha side. -/
theorem accepted_render_balanced (hch : ChachaSideV3) {cb wb : Bytes} (A : AcceptedV3 cb wb) :
    ∃ R : RenderBundleV3 A.pub, R.Balanced ∧ R ⟨16, by decide⟩ = A.rcptRenders.rcpt := by
  obtain ⟨writes, oldPost, q, us, r0, r1, r2, r3, r4, r5, r6, r7, r21, r11, bs, hr, hkf, hus, hpin, hups, hval,
    hc, hg, hres, hctx, hfw, htr, htf, hall⟩ := RcptTrieSide.rcpt_trie_vbytes A A.sizeBudget
  obtain ⟨r12, r13, r14, r15, h12, -, h13, -, h14, -, h15, -⟩ :=
    sched_renders_on A.hp A.pub bs hc (codec_cmps_ok A.hp hc hg)
  obtain ⟨r8, r9, r10, hcha⟩ := hch A bs hc hg hres hctx hfw
  let r24 := sortRenderV3 A.pub A.hk A.hw A.hd A.h A.hm A.rcptInput.lists A.lists_applied
  let R : RenderBundleV3 A.pub := bundleOf r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15
    A.rcptRenders.rcpt A.rcptRenders.acct A.rcptRenders.akey A.rcptRenders.bnd A.rcptRenders.srcp r21
    A.rcptRenders.qv A.mrkAcc r24
  refine ⟨R, ?_, rfl⟩
  have h24 : R.tf 24 = sortTraffic (Candidates.NativeSortIds.input
      (A.rcptInput.lists.flatten.map Input.receipt)) := bundle_tf_eq R 24 _ rfl
  obtain ⟨⟨⟨⟨bSREC, bRCL, bAKC, bRIDS, bMEM, bQVC, bQSH, bSRC, bBNDP, bBND⟩,
      ⟨bPARENT, bVPARENT, bENT, bDIGS, bDUP, bEDGE, bBMAP, bMIDROOT, bROOT, bUPB, bMEMD, bRPL, bRPLV⟩,
      bSIZE, bVSLOT, bKEYNIB, bFINAL, bBYTES, bDIGEST⟩, bSPLEN, bSPOST, bS0F⟩, bVBYTES, bMPOS⟩ :=
    hall R rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl h24
  have f11 : R.tf 11 = rowsTraffic Sched.Codec.table.interactions (codecCell (bs.map blkOf)) 22 11 A.pub := by
    rw [bundle_tf_eq R 11 _ rfl, htf]
  have f12 : (R ⟨12, by decide⟩).tr = ProcScanDistPhases.trace bs := h12
  have f13 : (R ⟨13, by decide⟩).tr = procTraceV3 (bs.map NativeBlock.run) := h13
  have f14 : (R ⟨14, by decide⟩).tr = MemConcatCells.trace (bs.map NativeBlock.run) := h14
  have f15 : (R ⟨15, by decide⟩).tr = cmpTraceAligned (ProcNativeOldComparisonCapacity.requests bs) := h15
  have bSCMP := R.balancedAt_scmp A hc hctx f11 f12 f13 f14 f15
  obtain ⟨bSOP, bSFIN, bSINC, bSPUSH, bSPUBB, bSPAR, bSDL, bSDLX, bSDG, bSA0⟩ :=
    R.sched_buses_balanced A hc hg hctx hfw f11 f12 f13 f14
  obtain ⟨bSSIN, bSSOUT, bSSMEM, bSGEN, bSSHUF, bSCHACHA⟩ := hcha R rfl rfl rfl f13
  apply R.balanced_of_used
  simp only [usedBuses, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, forall_const, and_true]
  exact ⟨bBYTES, bDIGEST, bPARENT, bVSLOT, bEDGE, bKEYNIB, bFINAL, bMEM, bRIDS, bMPOS, bROOT, bBMAP, bSRC, bBND,
    bSREC, bDIGS, bSIZE, bDUP, bENT, bVBYTES, bVPARENT, bMEMD, bMIDROOT, bUPB, bRCL, bAKC, bBNDP, bQSH,
    bSCMP, bSOP, bSFIN, bSINC, bSPUSH, bSSIN, bSSOUT, bSSMEM, bSGEN, bSSHUF, bSCHACHA, bSPUBB, bSPAR,
    bSDL, bSDLX, bSDG, bS0F, bSPOST, bSPLEN, bSA0, bQVC, bRPL, bRPLV⟩

/-- **Completeness of the D0a certificate from the ChaCha side.** -/
theorem completeV3_of_chacha (hch : ChachaSideV3) : CompleteV3Stmt := by
  intro cb wb h
  obtain ⟨A⟩ := acceptedV3_nonempty h
  obtain ⟨R, hbal, h16⟩ := accepted_render_balanced hch A
  obtain ⟨hn, hb, he⟩ := A.hint_bounds
  exact ⟨nativeHint A.k A.w A.m, A.p, A.hp, hn, hb, he, A.prepared_lt_P, A.pubFit, R, hbal,
    bundle_headerOk_rcpt A R h16⟩

/-- **The v3 admission certificate from soundness and the ChaCha side** (`nearV3_admission_of` with
`completeV3_of_chacha`). -/
theorem nearV3_admission_of_chacha (hext : ExtractV3Stmt) (hch : ChachaSideV3)
    (art : ArenaCore.ArtifactDescription) (pub : List UInt8) (hpub : sha256 pub = art.publicDigest)
    (himpl : art.impl.Connection challengeParamsD0a.verifyFuel
      (ZkFormal.Prover.Np.G.npVerifierP challengeSpecD0a nearAirV3 split prepV3b).toVerifier) :
    ArenaCore.AdmissionStatement challengeParamsD0a art :=
  nearV3_admission_of hext (completeV3_of_chacha hch) art pub hpub himpl

end ZkFormal.NearV3.Assembly
