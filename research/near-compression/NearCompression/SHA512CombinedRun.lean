import NearCompression.SHA512Combined

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra NearSpecV3.SHA512

def sha512CombinedKeys (tr : Trace Fp) (t start count : Nat) : List Nat :=
  (List.range' start count).map (fun r => sha512CombinedK (tr.cell t r))

/-- Any nonempty segment computes the actual specification's rounds function,
using its decoded constants and internally constrained message schedule. -/
theorem sha512_combined_segment (air : Air) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t < air.tables.length) (table : air.tables[t] = sha512CombinedTable)
    (holds : Holds air pub tr) (n start : Nat) (bound : start+n < tr.height t) :
    rounds (sha512CombinedVars (tr.cell t start)) (sha512CombinedKeys tr t start (n+1))
      (sha512CombinedWindow (tr.cell t start)) = sha512CombinedOutput (tr.cell t (start+n)) := by
  induction n generalizing start with
  | zero =>
    change round (sha512CombinedVars (tr.cell t start)) (sha512CombinedK (tr.cell t start))
      ((sha512CombinedWindow (tr.cell t start)).headD 0) = sha512CombinedOutput (tr.cell t start)
    exact
      (sha512_combined_output air tr pub t ht table holds start (by omega)).symm
  | succ n ih =>
    have link := sha512_combined_recurrence air tr pub t ht table holds start (by omega)
    rw [sha512CombinedKeys,List.range'_succ,List.map_cons,rounds]
    rw [←link.1,←link.2]
    have rest := ih (start+1) (by omega)
    simpa only [sha512CombinedKeys,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using rest

/-- The full trace computes rounds over its initial window and decoded k list.
This theorem does not identify that list with the fixed 80 SHA-512 constants. -/
theorem sha512_combined_terminal (air : Air) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t < air.tables.length) (table : air.tables[t] = sha512CombinedTable)
    (holds : Holds air pub tr) :
    rounds (sha512CombinedVars (tr.cell t 0)) (sha512CombinedKeys tr t 0 (tr.height t))
      (sha512CombinedWindow (tr.cell t 0)) = sha512CombinedOutput (tr.cell t (tr.height t-1)) := by
  have positive : 0 < tr.height t := Nat.two_pow_pos _
  have result := sha512_combined_segment air tr pub t ht table holds (tr.height t-1) 0 (by omega)
  simpa only [Nat.zero_add,Nat.sub_add_cancel (by omega : 1 ≤ tr.height t)] using result

end NearCompression
