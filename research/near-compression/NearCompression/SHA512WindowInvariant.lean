import NearCompression.SHA512ScheduleWindowRun

namespace NearCompression
open NearSpecV3.SHA512

/-- Domain of a SHA-512 rolling message window. -/
def sha512WindowValid (window : List Nat) : Prop :=
  window.length = 16 ∧ ∀ word ∈ window, word < 2^64

theorem sha512_window_next_valid (window : List Nat) (valid : sha512WindowValid window) :
    sha512WindowValid (nextWindow window) := by
  rcases valid with ⟨len,bounds⟩
  match window, len with
  | [w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15], _ =>
    constructor
    · rfl
    · intro word member
      simp only [nextWindow,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
        subst word <;> first
        | exact Nat.mod_lt _ (by decide)
        | apply bounds; simp

theorem sha512_window_run_valid (window : List Nat) (valid : sha512WindowValid window) (n : Nat) :
    sha512WindowValid (sha512ScheduleWindowRun window n) := by
  induction n with
  | zero => exact valid
  | succ n ih => exact sha512_window_next_valid _ ih

theorem sha512_window_getD_bound (window : List Nat) (valid : sha512WindowValid window)
    (i : Nat) : window.getD i 0 < 2^64 := by
  by_cases hi : i < window.length
  · rw [←List.getElem_eq_getD (h := hi) 0]
    exact valid.2 _ (List.getElem_mem hi)
  · simp [List.getD,hi]


theorem sha512_window_next_shift (window : List Nat) (len : window.length=16)
    (i : Nat) (hi : i<15) : (nextWindow window).getD i 0=window.getD (i+1) 0 := by
  match window, len with
  | [w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15], _ =>
    have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 := by omega
    rcases cases with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst i <;> rfl

theorem sha512_window_next_last (window : List Nat) (len : window.length=16) :
    (nextWindow window).getD 15 0 =
      add64 (add64 (ssig1 (window.getD 14 0)) (window.getD 9 0))
        (add64 (ssig0 (window.getD 1 0)) (window.getD 0 0)) := by
  match window, len with
  | [w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13,w14,w15], _ => rfl

end NearCompression
