import ZkFormal.NearV3.Render.CodecCanon
import ZkFormal.NearV3.Render.CodecSpost
import ZkFormal.NearV3.Candidates.ProcCodecComparisonAppend
import ZkFormal.NearV3.Candidates.ProcCodecComparisonTotal

/-!
# Codec (table 11) `B_SCMP` sends

Per row: only record rows `(f, gg) = (2, 2)` (always: `(apR + fair, MA, cb)`) and `(2, 7)` (instance 0:
`(gfin + gb, ft, 1)`) send.
-/
namespace ZkFormal.NearV3.Render.Cdc
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.Near ZkFormal.NearV3.Candidates.SchedSetAll ZkFormal.NearV3.Sched.Codec ZkFormal.Chacha.Table.E

set_option maxRecDepth 65536 in
theorem bus_scmp (d : Desc) (r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow d r) t r pub Sched.B_SCMP true =
      List.replicate (if cv d cg = 1 then 1 else 0) [cv d cx, cv d cy, cv d cbit] := by
  simp only [rowTraffic, Codec.table, interactions, List.flatMap_cons, List.flatMap_nil,
    ZkFormal.NearV3.B_S0F, Sched.B_S0F, ZkFormal.NearV3.B_SPLEN, ZkFormal.NearV3.B_SPOST,
    ZkFormal.NearV3.B_VBYTES, Sched.B_SPOST, ZkFormal.Near.B_BYTES,
    ZkFormal.Near.B_DIGEST, Sched.B_SPLEN, Sched.B_SPAR, Sched.B_SDL, Sched.B_SPUBB, Sched.B_SOP,
    Sched.B_SFIN, Sched.B_SDG, Sched.B_SA0, Sched.B_SCMP]
  simp only [Nat.reduceEqDiff, Bool.false_eq_true, and_false, and_true, false_and, true_and,
    ite_false, ite_true, List.append_nil, List.nil_append]
  simp only [Interaction.multNat, mult1, Interaction.msgVal, List.map_cons, List.map_nil]
  rfl

/-- The record rows' `SCMP` messages. -/
def scmpRec (I : Inst) (R : Rec) (f gg : Nat) : List (List Fp) :=
  if f = 2 ∧ gg = 2 then [[Fp.ofNat (apRv R + I.fair), Fp.ofNat MA, Fp.ofNat (cbv I R)]]
  else if f = 2 ∧ gg = 7 ∧ I.tv = 0 then [[Fp.ofNat (R.gfin + R.gb), Fp.ofNat R.ft, 1]]
  else []

set_option maxRecDepth 65536 in
theorem scmp_hdr (I : Inst) (p r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow (.hdr I p) r) t r pub Sched.B_SCMP true = [] := by
  rw [bus_scmp]; cdc_bus

set_option maxRecDepth 65536 in
theorem scmp_hash (I : Inst) (dig hpre : List Nat) (j r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow (.hash I dig hpre j) r) t r pub Sched.B_SCMP true = [] := by
  rw [bus_scmp]; cdc_bus

set_option maxRecDepth 65536 in
theorem scmp_ash (I : Inst) (ash : List Nat) (j r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow (.ash I ash j) r) t r pub Sched.B_SCMP true = [] := by
  rw [bus_scmp]; cdc_bus

set_option maxRecDepth 65536 in
theorem scmp_rec (I : Inst) (R : Rec) (f gg bpo bpr apv apostv bigv r t : Nat) (pub : List Fp) :
    rowTraffic Codec.table.interactions (dRow (.record I R f gg bpo bpr apv apostv bigv) r) t r pub
      Sched.B_SCMP true = scmpRec I R f gg := by
  rw [bus_scmp]
  unfold scmpRec
  by_cases h22 : f = 2 ∧ gg = 2
  · obtain ⟨rfl, rfl⟩ := h22
    cdc_bus
  · by_cases h27 : f = 2 ∧ gg = 7
    · obtain ⟨rfl, rfl⟩ := h27
      cdc_bus
      unfold zt0
      by_cases ht : I.tv = 0 <;> simp [ht, o1, z1]
    · simp only [h22, ite_false]
      have : ¬ (f = 2 ∧ gg = 7 ∧ I.tv = 0) := fun h => h27 ⟨h.1, h.2.1⟩
      simp only [this, ite_false]
      have hz : lookup (recA I R f gg bpo bpr apv apostv bigv) cg 0 = 0 := by
        cdc_cell
        simp only [h22, h27, ite_false]
      simp only [cv, Desc.asg, hz, z1, ite_false, List.replicate_zero]

end ZkFormal.NearV3.Render.Cdc

namespace ZkFormal.NearV3.Render.CdcScmp
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Candidates
open ZkFormal.NearV3.Assembly.CodecDigest

theorem loop_append {α σ ε : Type} (xs : List Nat) (step : Nat → σ → Except ε (ForInStep σ))
    (proj : σ → List α) (req : Nat → List α)
    (h : ∀ g s out, step g s = .ok out → ∃ s', out = .yield s' ∧ proj s' = proj s ++ req g) :
    ∀ s out, forIn xs s step = .ok out → proj out = proj s ++ xs.flatMap req := by
  induction xs with
  | nil => intro s out ho; simp only [List.forIn_nil] at ho; cases ho; simp
  | cons g xs ih =>
    intro s out ho
    rw [List.forIn_cons] at ho
    cases hs : step g s with
    | error e => simp only [hs, bind, Except.bind] at ho; cases ho
    | ok v =>
      obtain ⟨s', rfl, hp⟩ := h g s _ hs
      simp only [hs, bind, Except.bind] at ho
      rw [ih s' out ho, hp, List.flatMap_cons, List.append_assoc]

abbrev reqF (I : Input) (R : Run) (present : Bool) (gb : Array Nat) (fwd : List (Nat × Nat)) (k f : Nat) :=
  (List.range 8).flatMap (ProcCodecComparisonAppend.requests I R present gb fwd k f)

theorem field_reqs (I : Input) (R : Run) (present : Bool) (vid : Nat) (gb : Array Nat) (fwd : List (Nat × Nat))
    (k f : Nat) (s : RecordState) (out : ForInStep RecordState)
    (h : fieldStep I R present vid gb fwd k f s = .ok out) :
    ∃ s', out = .yield s' ∧ s'.2 = s.2 ++ reqF I R present gb fwd k f := by
  unfold fieldStep at h
  cases he : forIn (List.range 8) (s.1, s.2, 0, 0, 0, 0)
    (fun g st => ProcPriorCodecRecordStep.step I R present gb fwd
      (ProcPriorCodecNativeHash.instanceCells I R present vid) k f g st) with
  | error e => simp only [he, bind, Except.bind] at h; cases h
  | ok st =>
    simp only [he, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
    subst out
    refine ⟨_, rfl, ?_⟩
    exact loop_append (List.range 8) _ (fun st : ProcPriorCodecRecordStep.State => st.2.1)
      (ProcCodecComparisonAppend.requests I R present gb fwd k f)
      (fun g st o ho => ProcCodecComparisonAppend.step_requests I R present gb fwd _ k f g st o ho) _ st he

theorem block_reqs (I : Input) (R : Run) (present : Bool) (vid : Nat) (gb : Array Nat) (fwd : List (Nat × Nat))
    (k : Nat) (s : RecordState) (out : ForInStep RecordState)
    (h : blockStep I R present vid gb fwd k s = .ok out) :
    ∃ s', out = .yield s' ∧ s'.2 = s.2 ++ (List.range 3).flatMap (reqF I R present gb fwd k) := by
  unfold blockStep at h
  cases he : forIn (List.range 3) s (fieldStep I R present vid gb fwd k) with
  | error e => simp only [he, bind, Except.bind] at h; cases h
  | ok st =>
    simp only [he, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
    subst out
    exact ⟨_, rfl, loop_append (List.range 3) _ (fun st : RecordState => st.2) (reqF I R present gb fwd k)
      (fun f st o ho => field_reqs I R present vid gb fwd k f st o ho) _ st he⟩

private theorem bind_ok' {α β ε : Type} {x : Except ε α} {f : α → Except ε β} {out : β}
    (h : x >>= f = .ok out) : ∃ v, x = .ok v ∧ f v = .ok out := by
  cases x with
  | error e => cases h
  | ok v => exact ⟨v, rfl, h⟩

/-- **The repaired codec's comparison list**, in closed form. -/
theorem generated_reqs (I : Input) (R : Run) (present : Bool) (vid : Nat) (gb : Array Nat)
    (fwd : List (Nat × Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vid gb fwd = .ok out) :
    out.cmps = (List.range (R.n * R.n)).flatMap fun k => (List.range 3).flatMap (reqF I R present gb fwd k) := by
  rw [← coreLayout_eq] at h
  cases hc : coreLayout I R present vid gb fwd with
  | error e => simp [hc, Except.map] at h
  | ok o =>
    simp only [hc, Except.map, Except.ok.injEq] at h
    subst out
    show o.cmps = _
    unfold coreLayout at hc
    dsimp only at hc
    simp only [pure, Except.pure] at hc
    rw [push_loop] at hc
    simp only [bind, Except.bind] at hc
    obtain ⟨mid, hloop, hc⟩ := bind_ok' hc
    rw [push_loop] at hc
    simp only [bind, Except.bind] at hc
    rw [push_loop] at hc
    simp only [bind, Except.bind] at hc
    cases hc
    have := loop_append (List.range (R.n * R.n)) (blockStep I R present vid gb fwd) (fun st : RecordState => st.2)
      (fun k => (List.range 3).flatMap (reqF I R present gb fwd k))
      (fun k st o ho => block_reqs I R present vid gb fwd k st o ho) _ mid hloop
    simpa using this

end ZkFormal.NearV3.Render.CdcScmp

namespace ZkFormal.NearV3.Render.CdcScmp
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Render.Cdc
open ZkFormal.NearV3.Render.CdcGrant ZkFormal.NearV3.Assembly ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.NearV3.Candidates ZkFormal.NearV3.Assembly.CodecDigest

def scT : Desc → List (List Fp)
  | .record I R f gg _ _ _ _ _ => scmpRec I R f gg
  | _ => []

theorem rt_scmp (d : Desc) (r t : Nat) (pub : List Fp) :
    rowTraffic Sched.Codec.table.interactions (dRow d r) t r pub Sched.B_SCMP true = scT d := by
  cases d <;> simp only [scT, scmp_hdr, scmp_rec, scmp_hash, scmp_ash]

theorem blk_scmp (B : Cdc.Blk) : B.descs.flatMap scT =
    (List.range B.I.N).flatMap fun kk => scmpRec B.I (B.recs kk) 2 2 ++ scmpRec B.I (B.recs kk) 2 7 := by
  simp only [Cdc.Blk.descs, List.flatMap_append, Cdc.Blk.records, Cdc.flatten_flatMap, List.flatMap_map, scT, List.flatMap_nil]
  simp [Cdc.Blk.recordDescs, Cdc.Blk.fieldDescs, Cdc.Blk.recD, scT, scmpRec, List.range_succ, List.flatMap_append]

theorem reqs_block (I : Sched.Gen.Input) (R : Run) (present : Bool) (gb : Array Nat) (fwd : List (Nat × Nat)) (k : Nat) :
    (List.range 3).flatMap (reqF I R present gb fwd k) =
      ProcCodecComparisonAppend.requests I R present gb fwd k 2 2 ++
        ProcCodecComparisonAppend.requests I R present gb fwd k 2 7 := by
  simp [reqF, ProcCodecComparisonAppend.requests, List.range_succ]

/-- **The frozen codec's `B_SCMP` sends are the repaired codec's comparisons** (every block of `A`'s trace). -/
theorem codec_scmp_native {cb wb : Bytes} (A : AcceptedV3 cb wb) {bs : List NativeBlock} {B : Nat}
    (hc : PriorCore A.p B bs)
    (hctx : bs.map (fun b => (b.witness.ctx, b.witness.pre)) =
      (A.m.ctx A.k, A.m.pre) :: A.steps.map (fun e => (implicitCtx A.k e, e.pre)))
    (t : Nat) (pub : List Fp) :
    rowsTrafficFp Sched.Codec.table.interactions (codecCell (bs.map blkOf)) 22 t pub Sched.B_SCMP true =
      (bs.flatMap fun b => b.output.cmps).map Sched.Complete.cmpMsg := by
  rw [codec_bus _ (prior_cap hc) t pub _ _ scT (rt_scmp · · t pub), List.flatMap_map, List.map_flatMap]
  apply flatMap_congr_rt
  intro b hb
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hb
  obtain ⟨⟨-, hr⟩, -, -⟩ := hc.indexed i b hi
  have hn : b.run.n = b.pub.ids.length := (ProcActualRunProjection.run_fields _ i b.run hr).2.1
  rw [blk_scmp, generated_reqs _ _ _ _ _ _ _ (hc.valid b hb).1.2.2.2.2, List.map_flatMap]
  apply flatMap_congr_rt
  intro kk hkk
  have hk : kk < b.pub.ids.length * b.pub.ids.length := by
    have := List.mem_range.mp hkk; simpa [blkOf, hn] using this
  rw [reqs_block]
  have ha0 : ((blkOf b).recs kk).a0s =
      (if b.prior.isSome then (ProcActualInput.allowances b.pub.ids b.old)[kk]! else 0) := by
    by_cases hp : b.prior.isSome = true
    · rw [if_pos hp]; exact a0s_accepted A hc hctx b hb hp kk hk
    · rw [if_neg hp]
      simp only [blkOf]
      split <;> simp_all
  simp only [scmpRec, ProcCodecComparisonAppend.requests, apRv, cbv, ha0, List.map_append]
  simp [blkOf, Sched.Complete.cmpMsg, ProcPreparedSequence.input, hn, demand]
  by_cases ht : b.run.tau = 0
  · simp [ht, Sched.Complete.cmpMsg]; rfl
  · simp [ht]

end ZkFormal.NearV3.Render.CdcScmp
