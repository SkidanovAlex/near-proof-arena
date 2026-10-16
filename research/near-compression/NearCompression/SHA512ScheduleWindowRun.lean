import NearCompression.SHA512ScheduleWindow

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra NearSpecV3.SHA512

/-- Iteration of the actual specification window update from the initial row. -/
def sha512ScheduleWindowRun (initial : List Nat) : Nat → List Nat
  | 0 => initial
  | n+1 => nextWindow (sha512ScheduleWindowRun initial n)

theorem sha512_window_prefix (air : Air) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t < air.tables.length)
    (table : air.tables[t] = sha512ScheduleWindowSequenceTable)
    (holds : Holds air pub tr) (n : Nat) (hn : n < tr.height t) :
    sha512ScheduleWindow (tr.cell t n) =
      sha512ScheduleWindowRun (sha512ScheduleWindow (tr.cell t 0)) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sha512_schedule_window_recurrence air tr pub t ht table holds n hn,ih (by omega)]
    rfl

/-- The final row expands once more, so a 64-row trace produces words W64..W79
from an initial 16-word window, without a wraparound link to the first row. -/
theorem sha512_window_terminal (air : Air) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t < air.tables.length)
    (table : air.tables[t] = sha512ScheduleWindowSequenceTable)
    (holds : Holds air pub tr) :
    sha512ScheduleWindowOutput (tr.cell t (tr.height t-1)) =
      sha512ScheduleWindowRun (sha512ScheduleWindow (tr.cell t 0)) (tr.height t) := by
  have positive : 0 < tr.height t := Nat.two_pow_pos _
  have last : tr.height t-1 < tr.height t := by omega
  have row := sha512_window_core_holds air tr pub t ht table holds (tr.height t-1) last
  rw [sha512_schedule_window_output _ row,
    sha512_window_prefix air tr pub t ht table holds (tr.height t-1) last]
  change sha512ScheduleWindowRun (sha512ScheduleWindow (tr.cell t 0)) ((tr.height t-1)+1) = _
  rw [Nat.sub_add_cancel (by omega)]

end NearCompression
