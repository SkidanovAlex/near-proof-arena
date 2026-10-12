import ZkFormal.NearV3.Render.SchedBusRunDecomp

/-!
# The exact effect of one replay entry step (ops logs, pushes, used bits, entry)
-/
namespace ZkFormal.NearV3.Render.SchedRun
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Candidates

/-- Facts of one entry produced at position `x` with start time `T`. -/
structure EntryOk (cv : Array CReq) (rd : Round) (sh : List Nat) (x : Nat) (e : Entry) : Prop where
  hx : e.x = x
  hts : e.ts = (ProcPushConservation.stamp cv.size rd.bucket[x]!).1
  hein : e.ein = rd.bucket[x]!.v
  heout : e.eout = sh[x]!
  hcid : e.eout / 64 < cv.size
  hj : e.eout % 64 < cv[e.eout / 64]!.incs.length
  hinc : e.inc = cv[e.eout / 64]!.incs[e.eout % 64]!
  hrem : e.rem = cv[e.eout / 64]!.incs.length - e.eout % 64 - 1
  hs : e.s = cv[e.eout / 64]!.s
  hr : e.r = cv[e.eout / 64]!.r
  hlink : e.link = cv[e.eout / 64]!.link
  hpush : e.push = (e.ok && e.rem != 0)

theorem check_iff {b : Bool} {m : String} {u : Unit} : check b m = .ok u ↔ b = true := by
  unfold check; cases b <;> simp [pure, Except.pure, throw, throwThe, MonadExceptOf.throw, Except.error]

theorem entry_effect (I : Input) (cv : Array CReq) (rd : Round) (sh : List Nat) (T x : Nat)
    (sb rb aa gg : Array Nat) (ol os orr : Array (Array Gen.MOp)) (ps : Array (Nat×Nat×Nat×Nat))
    (used : Array (Array Bool)) (gi : Nat) (es : Array Entry) (out : ProcActualReplayEntry.Acc)
    (h : ProcActualReplayEntry.step I cv rd sh T x (sb,rb,aa,gg,ol,os,orr,ps,used,gi,es) = .ok (.yield out)) :
    ∃ e oL oS oR sb' rb' aa' gg' ps',
      out = (sb', rb', aa', gg', ol.modify e.link (·.push oL), os.modify e.s (·.push oS),
        orr.modify e.r (·.push oR), ps', used.modify (e.eout / 64) (·.set! (e.eout % 64) true), gi + 1,
        es.push e) ∧
      ps' = (if e.push then ps.push (T + x, e.alOut, e.zn, e.eout + 1) else ps) ∧
      EntryOk cv rd sh x e ∧
      oS = ⟨T + x, OP_GRANT, e.sbIn, e.sbOut, 0, 0, e.inc, e.ok, e.cS, e.cS⟩ ∧
      oR = ⟨T + x, OP_GRANT, e.rbIn, e.rbOut, 0, 0, e.inc, e.ok, e.cR, e.cR⟩ ∧
      oL.t = T + x ∧ oL.op = OP_GRANT ∧ oL.vin = e.alIn ∧ oL.v = e.alOut ∧ oL.inc = e.inc ∧
      oL.ok = e.ok ∧ oL.c = e.cL := by
  unfold ProcActualReplayEntry.step at h
  simp only [bind,Except.bind,pure,Except.pure] at h
  repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals refine ⟨⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_⟩, ⟨_,_,_,_,_,_,_,_,_,_⟩, _, _, _, _, _, _, _, rfl, ?_, ⟨rfl, rfl, rfl, rfl, ?_, ?_, rfl, rfl, rfl, rfl, rfl, ?_⟩,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  all_goals simp_all [check_iff]

theorem collect_ok (R K z : Nat) : ∀ (bs : List Push) (acc out : Array (Nat×Nat×Nat×Nat)),
    forIn bs acc (ProcActualBucketGuards.collectStep R K z) = .ok out →
      (∀ b ∈ bs, b.key = K ∧ b.z = z) ∧ out.toList = acc.toList ++ bs.map (ProcPushConservation.stamp R)
  | [], acc, out, h => by simp only [List.forIn_nil] at h; cases h; simp
  | b :: bs, acc, out, h => by
    rw [List.forIn_cons] at h
    simp only [ProcActualBucketGuards.collectStep, bind, Except.bind, pure, Except.pure] at h
    cases hc : check (b.key == K && b.z == z) "bucket push key/z" with
    | error e => simp [hc] at h
    | ok u =>
      have hb := (check_iff.mp hc)
      simp only [Bool.and_eq_true, beq_iff_eq] at hb
      simp only [hc] at h
      obtain ⟨h1, h2⟩ := collect_ok R K z bs _ out h
      refine ⟨?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hb
        · exact h1 x hx
      · rw [h2]; simp [ProcPushConservation.stamp]

set_option maxHeartbeats 1600000 in
theorem round_effect (I : Input) (cv : Array CReq) (key : List Nat) (rd : Round)
    (sb rb aa gg : Array Nat) (ol os orr : Array (Array Gen.MOp)) (ps bs : Array (Nat×Nat×Nat×Nat))
    (tm kp kq zq : Nat) (used : Array (Array Bool)) (rs : Array Gen.RoundD) (gi : Nat)
    (out : ProcActualReplayRound.Acc)
    (h : ProcActualReplayRound.step I cv key rd (sb,rb,aa,gg,ol,os,orr,ps,bs,tm,kp,kq,zq,used,rs,gi) =
      .ok (.yield out)) :
    ∃ (sh : List Nat) (kend : Nat) (col : Array (Nat×Nat×Nat×Nat)) (eo : ProcActualReplayEntry.Acc),
      forIn rd.bucket bs (ProcActualBucketGuards.collectStep cv.size rd.key rd.z) = .ok col ∧
      forIn (List.range rd.bucket.length) (sb,rb,aa,gg,ol,os,orr,ps,used,gi,(#[] : Array Entry))
        (ProcActualReplayEntry.step I cv rd sh tm) = .ok eo ∧
      out = (eo.1, eo.2.1, eo.2.2.1, eo.2.2.2.1, eo.2.2.2.2.1, eo.2.2.2.2.2.1, eo.2.2.2.2.2.2.1,
        eo.2.2.2.2.2.2.2.1, col, tm + rd.bucket.length, kend, rd.key, rd.z, eo.2.2.2.2.2.2.2.2.1,
        rs.push ⟨rd.key, rd.z, tm, rd.bucket.length, kp, kend, kq, zq, eo.2.2.2.2.2.2.2.2.2.2.toList⟩,
        eo.2.2.2.2.2.2.2.2.2.1) := by
  unfold ProcActualReplayRound.step at h
  simp only [bind,Except.bind,pure,Except.pure] at h
  repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals
    refine ⟨?sh, _, _, (_, _, _, _, _, _, _, _, _, _, _), ?_, ?_, rfl⟩
    rotate_left
    · assumption
    · assumption

end ZkFormal.NearV3.Render.SchedRun
