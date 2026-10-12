import ZkFormal.NearV3.Render.SchedBusSOP
import ZkFormal.NearV3.Rcpt.Link.PrepFwd

/-!
# `SPUBB` (bus 51): public scheduler bytes balance

The public statement sends, per instance, the 16 ChaCha key limbs (received by the process key rows,
13) and the 32 `sha256(all_shards)` bytes (received by the codec `kA` rows, 11), and for instance 0 the
forwarding demand of every link (received at the codec record ends of instance 0).  The demands of the
prepared statement are the main execution's (`p.fwd = fwdLinks ctx outgoing`), which instance 0's
codec block forwards.  **`RenderBundleV3.balancedAt_spubb`**.
-/
set_option linter.unusedSimpArgs false
set_option autoImplicit false
namespace ZkFormal.NearV3.Render.SsdBus
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.NearV3.Candidates ZkFormal.NearV3.Assembly.CodecDigest NearSpecV3.Scheduler
open ZkFormal.NearV3.Assembly (recF)

theorem key_msgs (b : NativeBlock) (tau : Nat)
    (hr : ActualRun.run (ProcPreparedSequence.input b.pub b.old) tau = .ok b.run) :
    ProcBus.keyL b.run = recF (keyRecs b.run.tau (instOf b.pub).seed) := by
  obtain ⟨-, -, -, -, hseed, -⟩ := ProcActualRunProjection.run_fields _ tau b.run hr
  simp only [ProcBus.keyL, recF, keyRecs, List.map_map, hseed]
  rfl

theorem codec_spubb (b : NativeBlock) (tau : Nat) (fwd : List (Nat × Nat)) (hn64 : b.run.n ≤ 64)
    (hr : ActualRun.run (ProcPreparedSequence.input b.pub b.old) tau = .ok b.run)
    (hfw : b.run.tau = 0 → b.forwarded = fwd) :
    (Cdc.blkOf b).descs.flatMap Cdc.spubbT =
      (if b.run.tau = 0 then recF (fwdRecs (instOf b.pub) fwd) else []) ++
        recF (ashRecs b.run.tau (instOf b.pub).ash) := by
  obtain ⟨-, hnI, -⟩ := ProcActualRunProjection.run_fields _ tau b.run hr
  have hn : (instOf b.pub).n = b.run.n := by rw [hnI]; rfl
  rw [Cdc.blk_spubb]
  refine app_congr ?_ ?_
  · simp only [Cdc.blkOf]
    by_cases h0 : b.run.tau = 0
    · simp only [h0, ite_true, hfw h0]
      unfold fwdRecs recF
      rw [hn, List.map_map]
      apply List.map_congr_left
      intro l hl
      have hl' := List.mem_range.mp hl
      have : b.run.n * b.run.n ≤ 4096 := by have := Nat.mul_le_mul hn64 hn64; omega
      simp only [Function.comp_apply, Cdc.demand, b2, b3, TAG_FWD, List.cons_append, List.nil_append,
        List.map_cons, List.map_nil]
      rw [Nat.mod_eq_of_lt (by omega : l / 256 < 256)]
      rfl
    · simp only [h0, ite_false]
  · unfold ashRecs recF
    rw [List.map_map]
    apply List.map_congr_left
    intro j _
    simp only [Function.comp_apply, Cdc.blkOf, getD_toNat, TAG_ASH, List.map_cons, List.map_nil, instOf,
      ProcPreparedSequence.input]
    rfl

end ZkFormal.NearV3.Render.SsdBus

namespace ZkFormal.NearV3.Assembly
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.NearV3.Render
open ZkFormal.NearV3.Render.SsdBus ZkFormal.NearV3.Sched
open ZkFormal.NearV3.Assembly.CodecDigest ZkFormal.NearV3.Candidates NearSpec NearSpecV3

/-- The prepared forwarding demands are the main execution's. -/
theorem prep_fwd {cb wb : Bytes} (A : AcceptedV3 cb wb) :
    A.p.fwd = fwdLinks (A.m.ctx A.k) A.m.result.outgoing := by
  obtain ⟨pc, refunds, hpc, hf⟩ := ZkFormal.NearV3.RcptLink.prepD0_fwd A.hp
  have hctx := (prepClaim_native_context hpc A.hk A.hm).ctx
  have hg : A.k.slotB2.gasLimit ≤ maxGasLimitD0 := by
    simpa only [a1, A.hk, decide_eq_true_eq] using A.rel.2.1
  have hbody := A.hm.body_decodes A.hd hg
  have hb := hf.body
  simp only [nativeHint] at hb
  rw [hbody] at hb
  simp only [Except.ok.injEq] at hb
  rw [hf.fwd, hctx, ← hb]

theorem covers_spubb_send : Covers Sched.B_SPUBB true (fun _ => false) = true := by decide +kernel
theorem covers_spubb_recv : Covers Sched.B_SPUBB false (fun t => t == 11 || t == 13) = true := by decide +kernel
theorem pub_spubb_recv (pub m : List Fp) : pubCount nearAirV3 pub Sched.B_SPUBB false m = 0 :=
  pub_off _ _ (by decide +kernel) pub m

theorem flatMap_first {α : Type} (bs : List NativeBlock) (X : NativeBlock → List α) (b0 : NativeBlock)
    (hb0 : bs[0]? = some b0) (ht : ∀ i (b : NativeBlock), bs[i]? = some b → b.run.tau = i) :
    bs.flatMap (fun (b : NativeBlock) => if b.run.tau = 0 then X b else []) = X b0 := by
  cases bs with
  | nil => simp at hb0
  | cons b rest =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hb0
    subst hb0
    have h0 : b.run.tau = 0 := ht 0 b rfl
    have hz : rest.flatMap (fun (b : NativeBlock) => if b.run.tau = 0 then X b else []) = [] := by
      apply List.flatMap_eq_nil_iff.mpr
      intro x hx
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hx
      have := ht (i + 1) x (by simpa using hi)
      simp [this]
    simp [h0, hz]

namespace RenderBundleV3

/-- **`SPUBB` balance**: the codec (11) and process (13) renders of the `PriorCore` blocks of `A`'s
trace receive exactly the public scheduler bytes. -/
theorem balancedAt_spubb {cb wb : Bytes} (A : AcceptedV3 cb wb) (R : RenderBundleV3 A.pub)
    {bs : List NativeBlock} (hc : PriorCore A.p NearSpecV3.B0 bs) (hlen : bs.length = A.steps.length + 1)
    (hfw : ∀ b, bs[0]? = some b → b.forwarded = fwdLinks (A.m.ctx A.k) A.m.result.outgoing)
    (h11 : R.tf 11 = rowsTraffic Sched.Codec.table.interactions (Cdc.codecCell (bs.map Cdc.blkOf)) 22 11 A.pub)
    (h13 : (R ⟨13, by decide⟩).tr = procTraceV3 (bs.map NativeBlock.run)) :
    R.BalancedAt Sched.B_SPUBB := by
  intro m
  rw [R.sum_tables true _ m _ covers_spubb_send, R.sum_tables false _ m _ covers_spubb_recv, pub_spubb_recv]
  have hf0 : (List.range 25).filter (fun _ => false) = [] := by decide
  have hf : (List.range 25).filter (fun t => t == 11 || t == 13) = [11, 13] := by decide
  rw [hf0, hf]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, Nat.zero_add]
  rw [h11, R.cnt_tf 13 (by decide) false, h13]
  have e1 := codec_sel A.pub _ (Cdc.prior_cap hc) _ false Cdc.spubbT (Cdc.rt_spubb · · 11 A.pub) m
  have i13 : nearAirV3.tables[13].interactions = Proc.tableB.interactions := rfl
  have hcap := (prior_run_capacities A.hp _ bs hc).2
  rw [i13, e1, ProcBus.count_key _ (by omega)]
  obtain ⟨p1, -, -, -⟩ := sched_pub_counts A m
  rw [p1]
  have hpubs := prior_pubs A hc hlen
  have hne : bs ≠ [] := by intro h; rw [h] at hlen; simp at hlen
  obtain ⟨b0, rest, hbs⟩ : ∃ b0 rest, bs = b0 :: rest := by
    cases bs with
    | nil => exact absurd rfl hne
    | cons b0 rest => exact ⟨b0, rest, rfl⟩
  have hb0 : bs[0]? = some b0 := by rw [hbs]; rfl
  have hPs : A.p.sched.map Sched.instOf = [] ++ bs.map (fun b => instOf b.pub) := by
    rw [← hpubs, List.map_map]; rfl
  have hpubb : (Public.schedulerRecords A.p).pubb =
      bs.flatMap (fun b => keyRecs b.run.tau (instOf b.pub).seed ++ ashRecs b.run.tau (instOf b.pub).ash) ++
        fwdRecs (instOf b0.pub) A.p.fwd := by
    have h := flatMap_instAt (fun τ P => keyRecs τ P.seed ++ ashRecs τ P.ash) (fun b => instOf b.pub) bs []
      (fun i b hi => by simpa using Cdc.prior_tau hc i b hi)
    rw [← hPs] at h
    simp only [List.length_nil] at h
    have hL : (A.p.sched.map Sched.instOf).length = bs.length := by rw [List.length_map, sched_length A, hlen]
    have h0 : instAt (A.p.sched.map Sched.instOf) 0 = instOf b0.pub := by
      rw [hPs, hbs]; rfl
    have hrender : (Public.schedulerRecords A.p).pubb =
        (List.range' 0 bs.length).flatMap (fun τ => keyRecs τ (instAt (A.p.sched.map Sched.instOf) τ).seed ++
          ashRecs τ (instAt (A.p.sched.map Sched.instOf) τ).ash) ++
          fwdRecs (instAt (A.p.sched.map Sched.instOf) 0) A.p.fwd := by
      show ((List.range (A.p.sched.map Sched.instOf).length).flatMap _) ++ _ = _
      rw [hL, List.range_eq_range']
      rfl
    rw [hrender, h, h0]
  rw [hpubb]
  -- codec per block
  have hcod : (bs.map Cdc.blkOf).flatMap (fun B => B.descs.flatMap Cdc.spubbT) =
      bs.flatMap (fun b => (if b.run.tau = 0 then recF (fwdRecs (instOf b.pub) A.p.fwd) else []) ++
        recF (ashRecs b.run.tau (instOf b.pub).ash)) := by
    rw [List.flatMap_map]
    apply Cdc.flatMap_congr''
    intro b hb
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hb
    have hr := (hc.indexed i b hi).1.2
    refine codec_spubb b i A.p.fwd (hc.valid b hb).2 hr (fun h0 => ?_)
    have hi0 : i = 0 := by rw [← (hc.indexed i b hi).2.1]; exact h0
    subst hi0
    rw [hfw b hi, prep_fwd A]
  have hkey : (bs.map NativeBlock.run).flatMap ProcBus.keyL =
      bs.flatMap (fun b => recF (keyRecs b.run.tau (instOf b.pub).seed)) := by
    rw [List.flatMap_map]
    apply Cdc.flatMap_congr''
    intro b hb
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hb
    exact key_msgs b i (hc.indexed i b hi).1.2
  rw [hcod, hkey]
  have hfirst := flatMap_first bs (fun b => recF (fwdRecs (instOf b.pub) A.p.fwd)) b0 hb0
    (fun i b hi => (hc.indexed i b hi).2.1)
  have c1 := congrArg (List.count m) hfirst
  rw [count_flatMap_app2]
  simp only [recF, List.map_append, List.map_flatMap, List.count_append] at c1 ⊢
  rw [count_flatMap_app2]
  omega

end RenderBundleV3
end ZkFormal.NearV3.Assembly
