import NearCompression.SHA512Schedule
import NearCompression.SHA512RoundTrace

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra NearSpecV3.SHA512

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
theorem sha512_schedule_constraints_current :
    sha512ScheduleConstraints.all sha512CurrentExpr = true := by decide

theorem sha512_schedule_constraints_local (e : Expr) (he : e ∈ sha512ScheduleConstraints) :
    instructionLocalExpr e :=
  sha512_current_expr_local e (List.all_eq_true.mp sha512_schedule_constraints_current e he)

theorem sha512_schedule_trace_holds (air : Air) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t < air.tables.length)
    (table : air.tables[t] = sha512ScheduleTable)
    (holds : Holds air pub tr) (r : Nat) (hr : r < tr.height t) :
    sha512ScheduleHolds (tr.cell t r) := by
  intro e he
  have hc := holds.constr t ht r hr e
  rw [table] at hc
  have hv := hc he
  rw [instruction_local_eval e tr t r pub (sha512_schedule_constraints_local e he)] at hv
  exact hv

/-- Actual AIR satisfaction enforces the new-word arithmetic. Temporal window
links, and a connection to the round's w input, are separate obligations. -/
theorem sha512_schedule_trace_sound (air : Air) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t < air.tables.length)
    (table : air.tables[t] = sha512ScheduleTable)
    (holds : Holds air pub tr) (r : Nat) (hr : r < tr.height t) :
    sha512ScheduleOutput (tr.cell t r) =
      add64 (add64 (ssig1 (sha512ScheduleW14 (tr.cell t r))) (sha512ScheduleW9 (tr.cell t r)))
        (add64 (ssig0 (sha512ScheduleW1 (tr.cell t r))) (sha512ScheduleW0 (tr.cell t r))) :=
  sha512_schedule_sound _ (sha512_schedule_trace_holds air tr pub t ht table holds r hr)

def sha512ScheduleAir : Air := ⟨[sha512ScheduleTable],0,0⟩

/-- Completeness of the isolated schedule-core trace, without temporal links. -/
theorem sha512_schedule_trace_complete (tr : Trace Fp) (pub : List Fp)
    (height : 1 ≤ tr.log 0 ∧ tr.log 0 ≤ 22)
    (rows : ∀ r, r < tr.height 0 → sha512ScheduleHolds (tr.cell 0 r)) :
    Holds sha512ScheduleAir pub tr := by
  constructor
  · intro t ht
    have hzero : t = 0 := by simpa [sha512ScheduleAir] using ht
    subst t
    exact height
  · intro t ht r hr e he
    have hzero : t = 0 := by simpa [sha512ScheduleAir] using ht
    subst t
    rw [instruction_local_eval e tr 0 r pub (sha512_schedule_constraints_local e he)]
    exact rows r hr e he
  · intro t ht r hr i hi
    have hzero : t = 0 := by simpa [sha512ScheduleAir] using ht
    subst t
    simp [sha512ScheduleAir,sha512ScheduleTable] at hi
  · intro b m
    simp [busCount,busCount.go,sha512ScheduleAir,sha512ScheduleTable,tableBusCount]

def sha512ScheduleWitnessTrace (logSize : Nat) (w0 w1 w9 w14 : Nat → Nat) : Trace Fp :=
  ⟨fun _ => logSize, fun _ r col => sha512ScheduleWitness (w0 r) (w1 r) (w9 r) (w14 r) col⟩

theorem sha512_schedule_witness_trace_holds (logSize : Nat) (w0 w1 w9 w14 : Nat → Nat)
    (height : 1 ≤ logSize ∧ logSize ≤ 22)
    (bounds : ∀ r, r < 2^logSize → sha512ScheduleInputBounds (w0 r) (w1 r) (w9 r) (w14 r)) :
    Holds sha512ScheduleAir [] (sha512ScheduleWitnessTrace logSize w0 w1 w9 w14) := by
  apply sha512_schedule_trace_complete _ [] height
  intro r hr
  exact sha512_schedule_witness_holds (w0 r) (w1 r) (w9 r) (w14 r) (bounds r hr)

end NearCompression
