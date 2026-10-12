import ZkFormal.NearV3.Render.SchedBusMem
import ZkFormal.NearV3.Candidates.ProcActualMemoryTagSegments
import ZkFormal.NearV3.Candidates.ProcActualPoppedLog
import ZkFormal.NearV3.Candidates.ProcActualPushLogGuard

/-!
# Decomposition of one successful `ActualRun.run` (prefix, replay accumulator, segments, checks)
-/
namespace ZkFormal.NearV3.Render.SchedRun
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Candidates

theorem bind_ok {α β ε : Type} {x : Except ε α} {f : α→Except ε β} {out : β}
    (h:x >>= f=.ok out) : ∃v,x=.ok v ∧ f v=.ok out := by
  cases x with
  | error e=>cases h
  | ok v=>exact ⟨v,rfl,h⟩

theorem check_ok {b : Bool} {m : String} {u : Unit} (h : check b m = .ok u) : b = true := by
  unfold check at h; split at h <;> simp_all

abbrev Acc := ProcActualReplayRound.Acc
def accPushes (s : Acc) : Array (Nat×Nat×Nat×Nat) := s.2.2.2.2.2.2.2.1
def accUsed (s : Acc) : Array (Array Bool) := s.2.2.2.2.2.2.2.2.2.2.2.2.2.1
def accRounds (s : Acc) : Array Gen.RoundD := s.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem run_decomp (I : Input) (tau : Nat) (R : Run) (h : ActualRun.run I tau = .ok R) :
    ∃ cv st rs ev s gs, ProcActualPrefix.runPrefix I = .ok (cv, st, rs, ev) ∧
      ProcActualReplayFactor.replay I cv rs = .ok s ∧ ProcActualSegments.build I tau s = .ok gs ∧
      (sortPush (accPushes s).toList == sortPush (ProcActualPoppedLog.buckets s).toList) = true ∧
      R.segs = gs.toList ∧ R.rounds = (accRounds s).toList ∧ R.used = accUsed s ∧ R.conv = cv.toList ∧
      R.tau = tau ∧ R.fin = st ∧
      (s.1 == st.sb && s.2.1 == st.rb && s.2.2.1 == st.al && s.2.2.2.1 == st.g) = true := by
  rw [ProcActualRunFactor.run_eq_prefix] at h
  obtain ⟨⟨cv,st,rs,ev⟩,hpre,h⟩:=bind_ok h
  dsimp only at h
  rw [ProcActualEntryFactor.rest_eq,ProcActualRoundFactor.rest_eq,ProcActualReplayFactor.rest_eq] at h
  obtain ⟨s,hs,h⟩:=bind_ok h
  rw [ProcActualMemoryFactor.finish_eq,ProcActualSegmentFactor.finish_eq] at h
  unfold ProcActualSegmentFactor.finishSegments at h
  obtain ⟨u1,h1,h⟩:=bind_ok h
  obtain ⟨u2,h2,h⟩:=bind_ok h
  obtain ⟨_,_,h⟩:=bind_ok h
  obtain ⟨gs,hgs,h⟩:=bind_ok h
  obtain ⟨cs,_,h⟩:=bind_ok h
  rw [ProcActualComparisonFactor.afterMemory_eq] at h
  obtain ⟨ds,_,h⟩:=bind_ok h
  unfold ProcActualComparisonFactor.finish at h
  obtain ⟨_,_,h⟩:=bind_ok h
  obtain ⟨_,_,h⟩:=bind_ok h
  cases h
  exact ⟨cv, st, rs, ev, s, gs, hpre, hs, hgs, check_ok h1, rfl, rfl, rfl, rfl, rfl, rfl, check_ok h2⟩

end ZkFormal.NearV3.Render.SchedRun
