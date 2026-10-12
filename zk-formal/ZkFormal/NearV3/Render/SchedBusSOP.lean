import ZkFormal.NearV3.Render.SchedBusSFIN

/-!
# `SOP` (bus 41): memory operations balance

Senders: the codec (11) sends one INIT per link `(16384τ + l, 0, INIT, al, a2, g2, 0, 1)`, the scan rows
(12) one READ per converted request and the distribute shard rows one INIT per shard and side, the
process rows (13) three GRANTs per entry; the memory (14) receives every segment's INIT and op log.
Per run these are the same multiset (`SchedRun.run_sop_fp`); the codec's link pass agrees with the
native one (`a1 = min(a0 + fair, MA)`, with the source-map allowances of a canonical prior).
**`RenderBundleV3.balancedAt_sop`**.
-/
set_option linter.unusedSimpArgs false
set_option autoImplicit false
namespace ZkFormal.NearV3.Render.SsdBus
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.NearV3.Candidates ZkFormal.NearV3.Render.Ssd ZkFormal.NearV3.Assembly.CodecDigest
open NearSpecV3.Scheduler

set_option maxHeartbeats 400000 in
theorem run_keys (I : Input) (tau : Nat) (R : Run) (h : ActualRun.run I tau = .ok R) :
    ∀ c ∈ R.conv, c.key = (SchedRun.lpOf I).a2[c.link]! := by
  have key : ∀ cv : Array CReq, ProcActualInitialPush.Facts I cv →
      ∀ c ∈ cv.toList, c.key = (SchedRun.lpOf I).a2[c.link]! := by
    intro cv hf c hc
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hc
    have hi' : i < cv.size := by simpa using hi
    have := (hf i hi').2.1
    rw [getElem!_pos cv i hi'] at this
    simp only [List.getElem_toArray, Array.getElem_toList] at this ⊢
    exact this
  unfold ActualRun.run at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat first | cases h | split at h
  all_goals
    exact key _ (ProcActualInitialPush.loop_facts I _ (by assumption))

theorem lp_sb (I : Input) (x : Nat) (hx : x < I.ids.length) :
    (SchedRun.lpOf I).sb[x]! = I.p.maxShardBandwidth - I.p.base * cntS I.ids.length I.allowed x := by
  simp [SchedRun.lpOf, linkPass, cntS, hx]

theorem lp_rb (I : Input) (x : Nat) (hx : x < I.ids.length) :
    (SchedRun.lpOf I).rb[x]! = I.p.maxShardBandwidth - I.p.base * cntR I.ids.length I.allowed x := by
  simp [SchedRun.lpOf, linkPass, cntR, hx]

theorem lp_a2 (I : Input) (l : Nat) (hl : l < I.ids.length * I.ids.length) :
    (SchedRun.lpOf I).a2[l]! =
      (if I.allowed[l]! then Nat.min ((ProcActualInput.allowances I.ids I.prev)[l]! + I.p.maxShardBandwidth / I.ids.length)
          I.p.maxAllowance - I.p.base
        else Nat.min ((ProcActualInput.allowances I.ids I.prev)[l]! + I.p.maxShardBandwidth / I.ids.length)
          I.p.maxAllowance) := by
  simp [SchedRun.lpOf, linkPass, hl]

theorem lp_g2 (I : Input) (l : Nat) (hl : l < I.ids.length * I.ids.length) :
    (SchedRun.lpOf I).g2[l]! = if I.allowed[l]! then I.p.base else 0 := by
  simp [SchedRun.lpOf, linkPass, hl]

theorem a1v_min (I : Cdc.Inst) (R : Cdc.Rec) : Cdc.a1v I R = Nat.min (R.a0s + I.fair) Codec.MA := by
  unfold Cdc.a1v Cdc.bigRv Cdc.cbv Cdc.apRv Codec.MA
  rw [show Nat.min (R.a0s + I.fair) 4500000 = if R.a0s + I.fair ≤ 4500000 then R.a0s + I.fair else 4500000 from
    Nat.min_def ..]
  by_cases hb : 16777216 ≤ R.a0s
  · simp only [hb, ite_true]; split <;> omega
  · simp only [hb, ite_false, Nat.mod_eq_of_lt (by omega : R.a0s < 16777216)]
    by_cases h1 : 4500000 ≤ R.a0s + I.fair
    · simp only [h1, ite_true]
      by_cases h2 : R.a0s + I.fair ≤ 4500000
      · simp only [h2, ite_true]; simp; omega
      · simp only [h2, ite_false]; simp
    · simp only [h1, ite_false]
      have h2 : R.a0s + I.fair ≤ 4500000 := by omega
      simp only [h2, ite_true]; simp

theorem allowances_initial (ids : List Nat) (k : Nat) :
    (ProcActualInput.allowances ids NearSpec.Bandwidth.State.initial)[k]! = 0 := by
  simp only [ProcActualInput.allowances, NearSpec.Bandwidth.State.initial, List.foldl_nil]
  by_cases hk : k < ids.length * ids.length
  · simp [hk]
  · rw [getElem!_neg _ _ (by simpa using hk)]; rfl

/-- The codec's link INITs are the native link pass. -/
theorem codec_sop (b : NativeBlock) (tau : Nat)
    (hr : ActualRun.run (ProcPreparedSequence.input b.pub b.old) tau = .ok b.run)
    (hpar : Params.calculate Config.pv86 b.pub.ids.length = some b.pub.params)
    (ha : ∀ kk < b.pub.ids.length * b.pub.ids.length,
      ((Cdc.blkOf b).recs kk).a0s = (ProcActualInput.allowances b.pub.ids b.old)[kk]!) :
    (Cdc.blkOf b).descs.flatMap Cdc.sopT =
      (List.range (b.pub.ids.length * b.pub.ids.length)).map (fun l => ProcBus.nf [addrOf b.run.tau 0 l, 0, OP_INIT,
        b2n (ProcPreparedSequence.input b.pub b.old).allowed[l]!,
        (SchedRun.lpOf (ProcPreparedSequence.input b.pub b.old)).a2[l]!,
        (SchedRun.lpOf (ProcPreparedSequence.input b.pub b.old)).g2[l]!, 0, 1]) := by
  obtain ⟨-, hnI, -⟩ := ProcActualRunProjection.run_fields _ tau b.run hr
  have hN : (Cdc.blkOf b).I.N = b.pub.ids.length * b.pub.ids.length := by
    simp only [Cdc.blkOf]; rw [hnI]; rfl
  have hMA : b.pub.params.maxAllowance = 4500000 := by rw [lp_calc hpar]
  rw [Cdc.blk_sop, hN]
  apply List.map_congr_left
  intro l hl
  have hl' := List.mem_range.mp hl
  have hI : (ProcPreparedSequence.input b.pub b.old).ids = b.pub.ids := rfl
  rw [lp_a2 _ l (by rw [hI]; exact hl'), lp_g2 _ l (by rw [hI]; exact hl'), a1v_min, ha l hl']
  simp only [ProcBus.nf, addrOf, List.map_cons, List.map_nil, Cdc.blkOf, hMA, hnI, Codec.MA, OP_INIT,
    ProcPreparedSequence.input]
  have ht : b.run.tau * 16384 + 0 * 4096 + l = 16384 * b.run.tau + l := by omega
  rw [ht]
  by_cases hal : b.pub.allowed[l]! = true
  · simp [b2n, hal]; exact ⟨rfl, rfl⟩
  · simp [b2n, hal]; exact ⟨rfl, rfl⟩

theorem init_side (I : Input) (R : Run) (sd : Nat) (hsd : sd = 0 ∨ sd = 1) (hn : R.n = I.ids.length) :
    ((List.range R.n).map (fun i => F (initMsg I R sd i))).Perm
      ((List.range R.n).map (fun x => ProcBus.nf [addrOf R.tau (sd + 1) x, 0, OP_INIT, 0,
        if sd = 0 then (SchedRun.lpOf I).sb[x]! else (SchedRun.lpOf I).rb[x]!, 0, 0, 0])) := by
  let key := fun x => if sd = 0 then ProcDistShardRow.average (cntS R.n I.allowed x) R.fin.sb[x]!
    else ProcDistShardRow.average (cntR R.n I.allowed x) R.fin.rb[x]!
  have hP : ∀ x, sd = 0 → budget0 ⟨I.ids, I.p, I.allowed, I.raw, I.seed, I.ash⟩ sd x =
      I.p.maxShardBandwidth - I.p.base * cntS I.ids.length I.allowed x := by
    intro x h; simp [budget0, h, InstPub.n]
  have hQ : ∀ x, sd = 1 → budget0 ⟨I.ids, I.p, I.allowed, I.raw, I.seed, I.ash⟩ sd x =
      I.p.maxShardBandwidth - I.p.base * cntR I.ids.length I.allowed x := by
    intro x h; simp [budget0, h, InstPub.n]
  refine List.Perm.trans (List.Perm.of_eq ?_) ((sorted_map key R.n
    (fun x => ProcBus.nf [addrOf R.tau (sd + 1) x, 0, OP_INIT, 0,
      budget0 ⟨I.ids, I.p, I.allowed, I.raw, I.seed, I.ash⟩ sd x, 0, 0, 0])).trans (List.Perm.of_eq ?_))
  · apply List.map_congr_left
    intro i _
    rcases hsd with rfl | rfl
    · simp only [F, initMsg, ProcBus.nf, sX, sB, ProcDistShardRow.nativeX, key, ite_true, addrOf, OP_INIT]
      congr 2; omega
    · simp only [F, initMsg, ProcBus.nf, sX, sB, ProcDistShardRow.nativeX, key, ite_false, addrOf, OP_INIT,
        show (1 : Nat) ≠ 0 by decide]
      congr 2; omega
  · apply List.map_congr_left
    intro x hx
    have hx' : x < I.ids.length := by rw [← hn]; exact List.mem_range.mp hx
    rcases hsd with rfl | rfl
    · simp only [hP x rfl, ite_true, lp_sb I x hx']
    · simp only [hQ x rfl, show (1 : Nat) ≠ 0 by decide, ite_false, lp_rb I x hx']

theorem read_msgs (b : NativeBlock) (tau : Nat)
    (hr : ActualRun.run (ProcPreparedSequence.input b.pub b.old) tau = .ok b.run) :
    b.run.conv.map (fun c => F (readMsg b.run c)) =
      (b.run.conv.map (SchedRun.readMsg tau (SchedRun.lpOf (ProcPreparedSequence.input b.pub b.old)).a2)).map
        ProcBus.nf := by
  have ht := (ProcActualRunProjection.run_fields _ tau b.run hr).1
  rw [List.map_map]
  apply List.map_congr_left
  intro c hc
  simp only [F, readMsg, Function.comp_apply, SchedRun.readMsg, ProcBus.nf, addrOf, OP_READ, ht,
    ← run_keys _ _ _ hr c hc]
  congr 2; omega

theorem dist_sop (b : NativeBlock) :
    distPart (fun row => sopM (fx row)) b =
      (List.range b.run.n).map (fun i => F (initMsg (ProcPreparedSequence.input b.pub b.old) b.run 0 i)) ++
      (List.range b.run.n).map (fun i => F (initMsg (ProcPreparedSequence.input b.pub b.old) b.run 1 i)) :=
  (dist_ops (ProcPreparedSequence.input b.pub b.old) b.run).1

theorem allow_eq {cb wb : NearSpec.Bytes} (A : Assembly.AcceptedV3 cb wb) {B : Nat} {bs : List NativeBlock}
    (hc : PriorCore A.p B bs)
    (hctx : bs.map (fun b => (b.witness.ctx, b.witness.pre)) =
      (A.m.ctx A.k, A.m.pre) :: A.steps.map (fun e => (Assembly.implicitCtx A.k e, e.pre))) :
    ∀ b ∈ bs, ∀ kk < b.pub.ids.length * b.pub.ids.length,
      ((Cdc.blkOf b).recs kk).a0s = (ProcActualInput.allowances b.pub.ids b.old)[kk]! := by
  intro b hb kk hk
  cases hp : b.prior.isSome
  · have hnone : b.prior = none := by simpa using hp
    have hold : b.old = NearSpec.Bandwidth.State.initial := by
      have hd := (hc.valid b hb).1.2.2.2.1
      rw [hnone] at hd
      simp only [Option.some.injEq] at hd
      exact hd.symm
    rw [hold, allowances_initial]
    simp only [Cdc.blkOf, hp]
    split <;> simp
  · exact CdcGrant.a0s_accepted A hc hctx b hb hp kk hk

end ZkFormal.NearV3.Render.SsdBus

namespace ZkFormal.NearV3.Assembly
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.NearV3.Render
open ZkFormal.NearV3.Render.SsdBus ZkFormal.NearV3.Sched
open ZkFormal.NearV3.Assembly.CodecDigest ZkFormal.NearV3.Candidates NearSpec

theorem covers_sop_send : Covers Sched.B_SOP true (fun t => t == 11 || t == 12 || t == 13) = true := by decide +kernel
theorem covers_sop_recv : Covers Sched.B_SOP false (fun t => t == 14) = true := by decide +kernel
theorem pub_sop (s : Bool) (pub m : List Fp) : pubCount nearAirV3 pub Sched.B_SOP s m = 0 :=
  pub_off _ _ (by cases s <;> decide +kernel) pub m

theorem count_flatMap_app4 {α β : Type} [BEq β] (l : List α) (f g h k : α → List β) (m : β) :
    (l.flatMap (fun a => f a ++ g a ++ h a ++ k a)).count m =
      (l.flatMap f).count m + (l.flatMap g).count m + (l.flatMap h).count m + (l.flatMap k).count m := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.flatMap_cons, List.count_append] at *; omega

namespace RenderBundleV3

/-- **`SOP` balance**: tables 11–14 of the `PriorCore` blocks of `A`'s trace. -/
theorem balancedAt_sop {cb wb : Bytes} (A : AcceptedV3 cb wb) (R : RenderBundleV3 A.pub)
    {bs : List NativeBlock} (hc : PriorCore A.p NearSpecV3.B0 bs)
    (hctx : bs.map (fun b => (b.witness.ctx, b.witness.pre)) =
      (A.m.ctx A.k, A.m.pre) :: A.steps.map (fun e => (implicitCtx A.k e, e.pre)))
    (h11 : R.tf 11 = rowsTraffic Sched.Codec.table.interactions (Cdc.codecCell (bs.map Cdc.blkOf)) 22 11 A.pub)
    (h12 : (R ⟨12, by decide⟩).tr = ProcScanDistPhases.trace bs)
    (h13 : (R ⟨13, by decide⟩).tr = procTraceV3 (bs.map NativeBlock.run))
    (h14 : (R ⟨14, by decide⟩).tr = MemConcatCells.trace (bs.map NativeBlock.run)) :
    R.BalancedAt Sched.B_SOP := by
  intro m
  rw [R.sum_tables true _ m _ covers_sop_send, R.sum_tables false _ m _ covers_sop_recv, pub_sop, pub_sop]
  have hf1 : (List.range 25).filter (fun t => t == 11 || t == 12 || t == 13) = [11, 12, 13] := by decide
  have hf2 : (List.range 25).filter (fun t => t == 14) = [14] := by decide
  rw [hf1, hf2]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
  rw [R.cnt_tf 12 (by decide) true, R.cnt_tf 13 (by decide) true, R.cnt_tf 14 (by decide) false, h12, h13, h14, h11]
  have i12 : nearAirV3.tables[12].interactions = ScanDist.table.interactions := rfl
  have i13 : nearAirV3.tables[13].interactions = Proc.tableB.interactions := rfl
  have i14 : nearAirV3.tables[14].interactions = Mem.interactions := rfl
  have hcap := prior_run_capacities A.hp _ bs hc
  have hd := prior_run_data A.hp _ bs hc
  have ht : ∀ R ∈ bs.map NativeBlock.run, ∀ g ∈ R.segs, ProcActualMemoryTagSegments.SegTag g := by
    intro R hR
    obtain ⟨sp, prev, hs, hr, _⟩ := hd R hR
    exact ProcActualMemoryTagSegments.run _ _ R hr
  have e1 := codec_sel A.pub _ (Cdc.prior_cap hc) _ true Cdc.sopT (Cdc.rt_sop · · 11 A.pub) m
  rw [i12, i13, i14, e1, ssd_count A.hp bs hc _ true sopM row_sop (by simp [sopM, fp_01, fp_add0]) 12 A.pub m,
    ssd_blocks bs (fun b hb => (hc.valid b hb).2), ProcBus.count_sop _ (by omega), MemBus.count_sop _ hcap.1 ht]
  simp only [List.flatMap_map]
  have hperm : (bs.flatMap fun b => (Cdc.blkOf b).descs.flatMap Cdc.sopT ++ scanPart (fun row => sopM (fx row)) b ++
      distPart (fun row => sopM (fx row)) b ++ ProcBus.sopL b.run).Perm (MemBus.sopML (bs.map NativeBlock.run)) := by
    unfold MemBus.sopML
    rw [List.flatMap_map]
    apply Cdc.flatMap_perm'
    intro b hb
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hb
    have hr := (hc.indexed i b hi).1.2
    have hs := prepD0_sched A.hp b.pub (List.mem_iff_getElem?.mpr ⟨i, (hc.indexed i b hi).1.1⟩)
    obtain ⟨ht', hnI, -⟩ := ProcActualRunProjection.run_fields _ i b.run hr
    have hpar := (ProcPreparedSequence.input_bounds b.pub b.old hs).1
    rw [codec_sop b i hr hpar (allow_eq A hc hctx b hb), scan_sop, read_msgs b i hr,
      dist_sop]
    have p0 := init_side (ProcPreparedSequence.input b.pub b.old) b.run 0 (Or.inl rfl) hnI
    have p1 := init_side (ProcPreparedSequence.input b.pub b.old) b.run 1 (Or.inr rfl) hnI
    have hrun := SchedRun.run_sop_fp _ _ _ hr
    refine List.Perm.trans ?_ hrun.symm
    rw [List.perm_iff_count]
    intro a
    have c0 := p0.count_eq a
    have c1 := p1.count_eq a
    have hI : (ProcPreparedSequence.input b.pub b.old).ids = b.pub.ids := rfl
    rw [hI] at hnI
    simp only [List.count_append, List.map_append, List.map_map, Function.comp_def, ite_true,
      show (1 : Nat) ≠ 0 by decide, ite_false, ↓reduceIte, hI, hnI, ht', Nat.zero_add,
      show (1 : Nat) + 1 = 2 from rfl] at c0 c1 ⊢
    omega
  have h := hperm.count_eq m
  rw [count_flatMap_app4] at h
  rw [List.count_append]
  omega

end RenderBundleV3
end ZkFormal.NearV3.Assembly
