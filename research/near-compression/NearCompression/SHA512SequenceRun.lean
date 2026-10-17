import NearCompression.SHA512RoundSequence

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra

/-- Iterate actual rounds using the trace's decoded per-row k/w inputs. -/
def sha512SequenceRun (tr : Trace Fp) (t : Nat) : Nat → NearSpecV3.SHA512.Vars
  | 0 => sha512RoundVars (tr.cell t 0)
  | n+1 => NearSpecV3.SHA512.round (sha512SequenceRun tr t n)
      (sha512RoundK (tr.cell t n)) (sha512RoundW (tr.cell t n))

/-- Every input state is the result of all preceding constrained rounds. -/
theorem sha512_sequence_prefix (air : Air) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t < air.tables.length)
    (table : air.tables[t] = sha512RoundSequenceTable)
    (holds : Holds air pub tr) (n : Nat) (hn : n < tr.height t) :
    sha512RoundVars (tr.cell t n) = sha512SequenceRun tr t n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sha512_sequence_round_recurrence air tr pub t ht table holds n hn,
      ih (by omega)]
    rfl

/-- The last output represents the entire trace, including its final round.
The trace's k/w inputs are not asserted to be the SHA-512 constant schedule. -/
theorem sha512_sequence_terminal (air : Air) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t < air.tables.length)
    (table : air.tables[t] = sha512RoundSequenceTable)
    (holds : Holds air pub tr) :
    sha512RoundOutput (tr.cell t (tr.height t-1)) =
      sha512SequenceRun tr t (tr.height t) := by
  have positive : 0 < tr.height t := Nat.two_pow_pos _
  have last : tr.height t-1 < tr.height t := by omega
  have row := sha512_sequence_row_holds air tr pub t ht table holds (tr.height t-1) last
  rw [← sha512_round_full_output _ row,
    sha512_sequence_prefix air tr pub t ht table holds (tr.height t-1) last]
  change sha512SequenceRun tr t ((tr.height t-1)+1) = _
  rw [Nat.sub_add_cancel (by omega)]

end NearCompression
