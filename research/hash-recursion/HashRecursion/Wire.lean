import Std

/-! Exact wire accounting for concatenated byte sections. No protocol or
serializer adequacy claim: callers must show these sections contain everything
the verifier needs, including framing and public statement transport. -/
namespace HashRecursion

def wireBytes (sections : List (List UInt8)) : Nat :=
  (sections.map List.length).sum

theorem serialize_length (sections : List (List UInt8)) :
    sections.flatten.length = wireBytes sections := by
  induction sections with
  | nil => rfl
  | cons s ss ih => simp [wireBytes, List.flatten_cons, ih, wireBytes] at *

/-- One unshared binary Merkle path per query. Shared multiproofs and caps
use a different model and are not ruled out by these results. -/
def pathBytes (queries depth digestBytes : Nat) : Nat :=
  queries * depth * digestBytes

theorem paths_216_depth22_512 : pathBytes 216 22 64 = 304128 := by decide

/-- Even before openings, roots, metadata or other proof layers. -/
theorem unshared_paths_exceed_target (otherBytes : Nat) :
    300000 < pathBytes 216 22 64 + otherBytes := by
  have := paths_216_depth22_512
  omega

theorem paths_128_depth22_512 : pathBytes 128 22 64 = 180224 := by decide

/-- Strictly below 300,000, not ≤300,000. This grants no soundness to 128 queries. -/
theorem remaining_budget_128 (otherBytes : Nat) :
    pathBytes 128 22 64 + otherBytes < 300000 ↔ otherBytes < 119776 := by
  have := paths_128_depth22_512
  omega

end HashRecursion
