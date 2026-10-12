import ZkFormal.NearV3.Render.ChachaLane
import ZkFormal.NearV3.Candidates.ProcActualNativeResult
import ZkFormal.NearV3.Assembly.SchedulerPriorCore
import ZkFormal.NearV3.Assembly.SchedulerSanityPin
import ZkFormal.NearV3.Assembly.NativeUnfold
import ZkFormal.NearV3.Assembly.RenderV3RcptAccepted
import ZkFormal.NearV3.Assembly.SchedulerRunComparisonTraffic

/-!
# ZkFormal.NearV3.Render.ChachaWords — RelD0a A9 on the native runs (`hW`)

* `coreMidW`, `runMid_stW` (as lane v3-link's `A9Words.coreMid` / `runMid_st`), `coreMid_proc`: the
  spec's `runMid` state is the repaired process's `processRequests` result;
* **`block_words`**: the words drawn by a block's scheduler call (`schedWords`) are its native run's
  `kfin` (`run_rounds`: `kfin = rngPos fin.rng`);
* **`schedIns_native`**: `schedInsD0` of the accepted claim is the list of the native trace's
  scheduler inputs;
* **`kfin_sum`**: `Σ kfin = chachaWords cb wb`; **`kfin_W0`**: `≤ W0` (A9);
* **`runOk_all`**: every native run of the accepted trace is `ChachaLane.RunOk`.
-/

namespace ZkFormal.NearV3.Render.ChachaBus
open NearSpec NearSpecV3 NearSpecV3.Scheduler ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.NearV3.Candidates ZkFormal.NearV3.Assembly ZkFormal.NearV3.Assembly.CodecDigest

/-- `coreOf` up to and including `processRequests` (as lane v3-link's `A9Words.coreMid`). -/
def coreMidW (ids : List Nat) (p : Params) (allowed : Array Bool) (reqs : List Req) (seed : NearSpec.Bytes)
    (prevState : Option NearSpec.Bytes) : Option St := do
  let prev ← match prevState with
    | none => some NearSpec.Bandwidth.State.initial
    | some b => NearSpec.Bandwidth.State.decode b
  let n := ids.length
  let links := List.range (n * n)
  let allow0 := prev.links.foldl (fun (a : Array Nat) la =>
      match indexOf ids la.sender, indexOf ids la.receiver with
      | some s, some r => a.set! (s * n + r) la.allowance
      | _, _ => a) (Array.replicate (n * n) 0)
  let st : St := ⟨Array.replicate n p.maxShardBandwidth, Array.replicate n p.maxShardBandwidth,
    allow0, Array.replicate (n * n) 0, Rng.ofSeed seed⟩
  let fair := p.maxShardBandwidth / n
  let st := { st with allowance := st.allowance.map fun a => Nat.min (Nat.min (a + fair) u64Max) p.maxAllowance }
  let st := links.foldl (fun st l => (tryGrant n allowed st l p.base).2) st
  processRequests n allowed st reqs

/-- `runMid`'s state is `coreMidW` of its claim-only part (lane v3-link's `A9Words.runMid_st`). -/
theorem runMid_stW {cfg : Config} {cc : CongestionConfig} {ids : List Nat} {prev : Option NearSpec.Bytes}
    {cong : List (Nat × CongestionInfo × Nat)} {req : List (Nat × List BandwidthRequest)}
    {seed : NearSpec.Bytes} {sp : SchedPub} (hp : pubOf cfg cc ids cong req seed = some sp) :
    (runMid cfg cc ids prev cong req seed).map Mid.st =
      coreMidW sp.ids sp.params sp.allowed (convertRaw sp.values sp.params.base sp.ids sp.raw) sp.seed prev := by
  unfold pubOf at hp
  by_cases hn : ids.length = 0
  · simp [hn] at hp
  · cases hpc : Params.calculate cfg ids.length with
    | none => simp [hn, hpc] at hp
    | some p =>
      simp only [hn, hpc, Option.bind, ↓reduceIte, bind, Option.some.injEq] at hp
      subst hp
      show _ = coreMidW ids p _ (convertRequests p ids req) seed prev
      unfold runMid coreMidW
      cases prev with
      | none =>
        simp only [hn, hpc, Option.bind, ↓reduceIte, bind]
        generalize processRequests _ _ _ _ = r
        cases r <;> rfl
      | some b =>
        cases hd : NearSpec.Bandwidth.State.decode b with
        | none => simp only [hn, hpc, hd, Option.bind, ↓reduceIte, bind]; rfl
        | some st =>
          simp only [hn, hpc, hd, Option.bind, ↓reduceIte, bind]
          generalize processRequests _ _ _ _ = r
          cases r <;> rfl

/-- `coreMidW` is the repaired process's `processRequests` from its initial state. -/
theorem coreMid_proc (sp : SchedPub) (hs : SchedPubOk sp) (ha : sp.allowed.size = sp.ids.length * sp.ids.length)
    (hval : sp.values = requestValues sp.params) (prevB : Option NearSpec.Bytes) (old : NearSpec.Bandwidth.State)
    (hdec : ProcActualCore.decodePrevious prevB = some old) (st : St)
    (h : coreMidW sp.ids sp.params sp.allowed (convertRaw sp.values sp.params.base sp.ids sp.raw) sp.seed prevB = some st) :
    processRequests sp.ids.length sp.allowed (ProcNativeGrant.native (ProcActualInput.initial (ProcPreparedSequence.input sp old)))
      (convRaw sp.params sp.ids.length (ZkFormal.NearV3.Sched.instOf sp).raw) = some st := by
  have hconv : convertRaw sp.values sp.params.base sp.ids sp.raw =
      convRaw sp.params sp.ids.length (ZkFormal.NearV3.Sched.instOf sp).raw := by
    rw [hval, ProcActualCore.conversion sp.ids sp.params hs.n1 hs.params, convRaw_instOf]
  unfold coreMidW at h
  unfold ProcActualCore.decodePrevious at hdec
  cases prevB <;> dsimp only at h hdec
  all_goals
    obtain ⟨prev, hprev, hrest⟩ := Option.bind_eq_some_iff.mp h
    rw [hdec, Option.some.injEq] at hprev
    subst hprev
    rw [hconv] at hrest
    rw [← ProcActualInput.initial_native (ProcPreparedSequence.input sp old) hs.n1 hs.params ha]
    exact hrest


/-- The scheduler input of a transition with context `ctx` on pre-trie `pre` (as `schedInsD0`). -/
def schedInOf (ctx : ApplyCtx) (pre : PTrie) : SchedIn :=
  ⟨ctx.layout.shardIds, ctx.own, (pre.find keyBwState).getD none, ctx.statuses, ctx.requests, ctx.prevBlockHash⟩

theorem rngWords_pos (r : NearSpecV3.Rng) : rngWords r = rngPos r := by
  unfold rngWords rngPos; rw [Nat.mul_comm]

/-- **The words drawn by a block's scheduler run** are its native run's final stream position. -/
theorem block_words (b : NativeBlock) (hb : b.Valid) (hs : SchedPubOk b.pub) {tau : Nat}
    (hrun : ActualRun.run (ProcPreparedSequence.input b.pub b.old) tau = .ok b.run) :
    schedWords (schedInOf b.witness.ctx b.witness.pre) = b.run.kfin := by
  obtain ⟨hv, hr, hp, hd, -⟩ := hb
  obtain ⟨so, hstep, -⟩ := hv.2
  have hfind : (b.witness.pre.find keyBwState).getD none = b.prior := by
    unfold readKey at hr
    cases hf : b.witness.pre.find keyBwState with
    | none => rw [hf] at hr; cases hr
    | some x => rw [hf] at hr; cases hr; rfl
  -- the spec scheduler call succeeded
  have hsched : ∃ o, prims.sched (schedInOf b.witness.ctx b.witness.pre) = some o := by
    unfold schedStep at hstep
    unfold schedInOf
    rw [hfind]
    simp only [bind, Except.bind, hr] at hstep
    split at hstep
    · exact ⟨_, ‹_›⟩
    · cases hstep
  obtain ⟨o, ho⟩ := hsched
  rw [prims_sched_eq_mid] at ho
  cases hmid : runMid Config.pv86 CongestionConfig.pv86 (schedInOf b.witness.ctx b.witness.pre).shardIds
      (schedInOf b.witness.ctx b.witness.pre).prev
      ((schedInOf b.witness.ctx b.witness.pre).statuses.map fun (s, c, m) => (s, toCI c, m))
      ((schedInOf b.witness.ctx b.witness.pre).requests.map fun (s, rs) => (s, rs.map fun r => ⟨r.toShard, r.bitmap⟩))
      (schedInOf b.witness.ctx b.witness.pre).prevBlockHash with
  | none => rw [hmid] at ho; cases ho
  | some mid =>
    have hw : schedWords (schedInOf b.witness.ctx b.witness.pre) = rngWords mid.st.rng := by
      unfold schedWords wordsDrawn; rw [hmid]
    rw [hw]
    have hst := runMid_stW (prev := (schedInOf b.witness.ctx b.witness.pre).prev) hp
    unfold schedInOf at hmid hst
    rw [hmid] at hst
    have hcore := coreMid_proc b.pub hs (ProcActualPublic.schedPub_fields _ _ hp).1
      (ProcActualPublic.schedPub_fields _ _ hp).2 _ b.old (by rw [hfind]; exact hd) mid.st hst.symm
    obtain ⟨st, rs, hpr, hnat⟩ := ProcActualInput.prepared_process_exists b.pub hs
      (ProcActualPublic.schedPub_fields _ _ hp).1 b.old mid.st hcore
    obtain ⟨⟨rs', hpr'⟩, hk, -⟩ := run_rounds _ _ _ hrun
    rw [hpr] at hpr'
    cases hpr'
    rw [← hnat, hk, rngWords_pos]
    rfl


/-! ## `schedInsD0` on the accepted trace -/

theorem implicit_ins {k : WalkD0} {root : Bytes} {pairs : List (Blk × Transition)} {steps : List ImplicitStepV3}
    {last : Bytes} (hv : ImplicitTraceValid k root pairs steps last) :
    ((pairs.map fun (M, _) => blockCtx k.L k.H.shardId k.slotB2.gasLimit M M.hdr.nextGasPrice).zip
        (unfoldedPairs steps)).map (fun (ctx, pre, _) =>
          (⟨ctx.layout.shardIds, ctx.own, (pre.find keyBwState).getD none, ctx.statuses, ctx.requests,
            ctx.prevBlockHash⟩ : SchedIn)) =
      steps.map fun e => schedInOf (implicitCtx k e) e.pre := by
  induction hv with
  | nil => rfl
  | cons root b t rest steps post last run rootChecked tail ih =>
    simp only [List.map_cons, unfoldedPairs, List.zip_cons_cons] at ih ⊢
    rw [ih]
    rfl

/-- **The scheduler inputs of the accepted claim** are those of the native trace's transitions. -/
theorem schedIns_native {cb wb : Bytes} (A : AcceptedV3 cb wb) :
    schedInsD0 cb wb = .ok (((A.m.ctx A.k, A.m.pre) :: A.steps.map fun e => (implicitCtx A.k e, e.pre)).map
      fun p => schedInOf p.1 p.2) := by
  have ht := triesD0_native_result A.hk A.hw A.hm A.hv
  unfold schedInsD0
  simp only [A.hk, A.hw, A.hm.block, A.hm.previous, ht, bind, Except.bind, pure, Except.pure]
  congr 1
  simp only [List.zip_cons_cons, List.map_cons, List.map_map]
  congr 1
  exact implicit_ins A.hv


theorem kst_le_ok {key : List Nat} {nc : Nat} {rd : Gen.RoundD} (h : RoundOk key nc rd) : rd.kst ≤ rd.kend := by
  obtain ⟨hd, -, hk⟩ := replay_inst 0 key rd.kst _ _ _ h.replay
  have hL : 0 < (sinstOf 0 key rd.kst (rd.entries.map (·.ein))).L := by
    have := h.L_pos
    simp only [sinstOf, ZkFormal.Chacha.Shuffle.Gen.SInst.L, List.length_map, h.len]
    omega
  rw [hk]; exact (kBefore_le hd hL).1

theorem le_sum_of_mem {l : List Nat} {x : Nat} (h : x ∈ l) : x ≤ l.sum := by
  induction l with
  | nil => cases h
  | cons y l ih =>
    rcases List.mem_cons.mp h with rfl | h
    · simp
    · have := ih h; simp only [List.sum_cons]; omega

theorem procVs_le_rows {rs : List Run} {R : Run} (h : R ∈ rs) :
    (Sched.Complete.procVs R).length ≤ (ProcConcatGeometry.rows rs).length := by
  unfold ProcConcatGeometry.rows
  rw [List.length_flatMap]
  exact le_sum_of_mem (List.mem_map.mpr ⟨R, h, rfl⟩)

section
variable {cb wb : Bytes} (A : AcceptedV3 cb wb) {bs : List NativeBlock}
  (hc : PriorCore A.p NearSpecV3.B0 bs)
  (hctx : bs.map (fun b => (b.witness.ctx, b.witness.pre)) =
    (A.m.ctx A.k, A.m.pre) :: A.steps.map (fun e => (implicitCtx A.k e, e.pre)))
include hc hctx

/-- **The native runs draw exactly the claim's ChaCha words** (`chachaWords`, RelD0a A9). -/
theorem kfin_sum : ((bs.map NativeBlock.run).map Run.kfin).sum = chachaWords cb wb := by
  unfold chachaWords
  rw [schedIns_native A, ← hctx, List.map_map, List.map_map]
  simp only [List.map_map]
  congr 1
  apply List.map_congr_left
  intro b hb
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hb
  obtain ⟨⟨hsch, hrun⟩, -, -⟩ := hc.indexed i b hi
  have hs := prepD0_sched A.hp b.pub (List.mem_of_getElem? hsch)
  exact (block_words b (hc.valid b hb).1 hs hrun).symm

/-- **A9 on the native runs**: at most `W0` words in total. -/
theorem kfin_W0 : ((bs.map NativeBlock.run).map Run.kfin).sum ≤ NearSpecV3.W0 := by
  rw [kfin_sum A hc hctx]
  have hh := (relD0a_iff NearSpecV3.B0 cb wb).mpr A.h
  simpa only [a9, decide_eq_true_eq] using hh.2.2.2.2.2.2.1

/-- **Every native run of the accepted trace is `RunOk`.** -/
theorem runOk_all : ∀ R ∈ bs.map NativeBlock.run, RunOk R := by
  have hW := kfin_W0 A hc hctx
  have hcap := (prior_run_capacities A.hp _ bs hc).2
  intro R hR
  obtain ⟨sp, prev, hs, hrun, hconv⟩ := prior_run_data A.hp _ bs hc R hR
  obtain ⟨-, hk, hkey, hchain, hrds⟩ := run_rounds _ _ _ hrun
  have hseed := (ProcActualRunProjection.run_fields _ _ _ hrun).2.2.2.2.1
  have h8 := ProcActualRunProjection.run_seed_words _ _ _ hrun
  have hshape := ProcActualReplayShape.run_shapes _ _ _ hrun
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hR
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hb
  obtain ⟨-, htau, -⟩ := hc.indexed i b hi
  have hilt : i < bs.length := (List.getElem?_eq_some_iff.mp hi).1
  have hlen := hc.length
  have hkf : b.run.kfin ≤ NearSpecV3.W0 :=
    Nat.le_trans (le_sum_of_mem (l := (bs.map NativeBlock.run).map Run.kfin)
      (List.mem_map.mpr ⟨b.run, hR, rfl⟩)) hW
  have hrows := procVs_le_rows hR
  obtain ⟨T, Kq, zq, hst⟩ := hchain
  refine ⟨by rw [hkey, hseed], by rw [hseed]; exact h8, hconv, by unfold NearSpecV3.W0 at hkf; omega,
    ⟨T, Kq, zq, hst⟩, fun rd hrd => ⟨hrds rd hrd, ?_, ?_⟩⟩
  · intro j hj
    obtain ⟨-, hsz, hx⟩ := hshape rd hrd
    exact hx j (by simpa using hj)
  · have hT := round_T hst (fun rd hrd => kst_le_ok (hrds rd hrd)) (fun rd hrd => (hrds rd hrd).len) rd hrd
    unfold lidOf T0 at *
    rw [htau]
    omega

end
end ZkFormal.NearV3.Render.ChachaBus
