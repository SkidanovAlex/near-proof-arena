import ZkFormal.NearV3.Render.SchedBusSsdTable

/-!
# The converted requests of a run are the public raw requests with a set bit, in order
-/
set_option linter.unusedSimpArgs false
set_option autoImplicit false
namespace ZkFormal.NearV3.Render.SsdBus
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Candidates NearSpecV3.Scheduler

def cv3 (c : CReq) : List UInt8 × Nat × Nat := (c.bm, c.s, c.r)
def qv3 (q : RawReq) : List UInt8 × Nat × Nat := (q.bm, q.s, q.r)

theorem step3 (I : Input) (q : RawReq) (cv : Array CReq)
    (out : ForInStep (Array CReq)) (h : ProcActualConverted.step I q cv = .ok out) :
    ∃ next, out = .yield next ∧
      next.toList.map cv3 = cv.toList.map cv3 ++ ([q].filter fun q => !(setBits q.bm).isEmpty).map qv3 := by
  cases hb : setBits q.bm with
  | nil =>
    simp only [ProcActualConverted.step, hb, List.isEmpty_nil, ite_true, pure, Except.pure, Except.ok.injEq] at h
    subst out
    exact ⟨cv, rfl, by simp [hb]⟩
  | cons c cs =>
    simp only [ProcActualConverted.step, hb, List.isEmpty_cons, Bool.false_eq_true, ite_false] at h
    simp only [bind, Except.bind, pure, Except.pure] at h
    repeat first | cases h | split at h
    all_goals exact ⟨_, rfl, by simp [hb, cv3, qv3]⟩

theorem conv_loop3 (I : Input) (qs : List RawReq) (cv out : Array CReq)
    (h : forIn qs cv (ProcActualConverted.step I) = .ok out) :
    out.toList.map cv3 = cv.toList.map cv3 ++ (qs.filter fun q => !(setBits q.bm).isEmpty).map qv3 := by
  induction qs generalizing cv with
  | nil => simp only [List.forIn_nil] at h; cases h; simp
  | cons q qs ih =>
    rw [List.forIn_cons] at h
    cases he : ProcActualConverted.step I q cv with
    | error e => simp only [he, bind, Except.bind] at h; cases h
    | ok s =>
      rcases step3 I q cv s he with ⟨next, rfl, hn⟩
      simp only [he, bind, Except.bind] at h
      rw [ih next h, hn, List.filter_cons]
      by_cases hq : (setBits q.bm).isEmpty = true <;> simp [hq, List.append_assoc]

set_option maxHeartbeats 400000 in
theorem run_conv3 (I : Input) (tau : Nat) (R : Run) (h : ActualRun.run I tau = .ok R) :
    R.conv.map cv3 = (I.raw.filter fun q => !(setBits q.bm).isEmpty).map qv3 := by
  unfold ActualRun.run at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat first | cases h | split at h
  all_goals
    have := conv_loop3 I I.raw #[] _ (by assumption)
    simpa using this

end ZkFormal.NearV3.Render.SsdBus
