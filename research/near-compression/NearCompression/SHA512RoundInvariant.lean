import NearCompression.SHA512WindowInvariant
import NearCompression.SHA512RoundWitness

namespace NearCompression
open NearSpecV3.SHA512

def sha512VarsValid (v : Vars) : Prop :=
  v.a<2^64 ∧ v.b<2^64 ∧ v.c<2^64 ∧ v.d<2^64 ∧
    v.e<2^64 ∧ v.f<2^64 ∧ v.g<2^64 ∧ v.h<2^64

/-- State evolution paired with the actual schedule-window iteration. -/
def sha512CombinedStateRun (initial : Vars) (window : List Nat) (keys : Nat → Nat) : Nat → Vars
  | 0 => initial
  | n+1 => round (sha512CombinedStateRun initial window keys n) (keys n)
      ((sha512ScheduleWindowRun window n).getD 0 0)

theorem sha512_vars_round_valid (v : Vars) (valid : sha512VarsValid v) (k w : Nat) :
    sha512VarsValid (round v k w) := by
  rcases valid with ⟨ha,hb,hc,hd,he,hf,hg,hh⟩
  exact ⟨Nat.mod_lt _ (by decide),ha,hb,hc,Nat.mod_lt _ (by decide),he,hf,hg⟩

theorem sha512_vars_input_bounds (v : Vars) (valid : sha512VarsValid v) (k w : Nat)
    (hk : k<2^64) (hw : w<2^64) : sha512RoundInputBounds v k w := by
  rcases valid with ⟨ha,hb,hc,hd,he,hf,hg,hh⟩
  exact ⟨ha,hb,hc,hd,he,hf,hg,hh,hk,hw⟩

theorem sha512_combined_state_run_valid (initial : Vars) (valid : sha512VarsValid initial)
    (window : List Nat) (keys : Nat → Nat) (n : Nat) :
    sha512VarsValid (sha512CombinedStateRun initial window keys n) := by
  induction n with
  | zero => exact valid
  | succ n ih => exact sha512_vars_round_valid _ ih _ _

theorem sha512_combined_run_input_bounds (initial : Vars) (valid : sha512VarsValid initial)
    (window : List Nat) (windowValid : sha512WindowValid window) (keys : Nat → Nat)
    (keysBound : ∀ n, keys n<2^64) (n : Nat) :
    sha512RoundInputBounds (sha512CombinedStateRun initial window keys n) (keys n)
      ((sha512ScheduleWindowRun window n).getD 0 0) :=
  sha512_vars_input_bounds _ (sha512_combined_state_run_valid initial valid window keys n)
    _ _ (keysBound n) (sha512_window_getD_bound _ (sha512_window_run_valid window windowValid n) 0)


theorem sha512_standard_keys_bound (n : Nat) : K.getD n 0<2^64 := by
  have bounds : K.all (fun word => decide (word<2^64))=true := by decide
  by_cases hn : n<K.length
  · rw [←List.getElem_eq_getD (h := hn) 0]
    exact of_decide_eq_true (List.all_eq_true.mp bounds _ (List.getElem_mem hn))
  · simp [List.getD,hn]

theorem sha512_initial_state_valid : sha512VarsValid (ofList H0) := by
  unfold sha512VarsValid
  decide

end NearCompression
