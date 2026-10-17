import NearCompression.CallPersistence

/-! Numeric backend persistence without changing integer algorithms or traps. -/
namespace NearCompression
open NearSpecV3.Wasm

def NumericKeepsReal (s : St) : Except String St → Prop
  | .ok u => u.real = s.real
  | .error _ => True

theorem exec_num_keeps_real (s : St) (op : Nat) :
    NumericKeepsReal s (execNum s op) := by
  by_cases c0 : op = 0x45
  · simp only [execNum, c0, ite_true, ite_false, pop_n_stack_form]
    repeat' (split <;> (try simp_all only []))
    all_goals try simp only [pushI32, pushI64, pushV]
    all_goals first | rfl | trivial
  by_cases c1 : op = 0x50
  · simp only [execNum, c0, c1, ite_true, ite_false, pop_n_stack_form]
    repeat' (split <;> (try simp_all only []))
    all_goals try simp only [pushI32, pushI64, pushV]
    all_goals first | rfl | trivial
  by_cases c2 : (0x46 ≤ op ∧ op ≤ 0x4F) ∨ (0x51 ≤ op ∧ op ≤ 0x5A)
  · simp only [execNum, c0, c1, c2, ite_true, ite_false, pop_n_stack_form]
    repeat' (split <;> (try simp_all only []))
    all_goals try simp only [pushI32, pushI64, pushV]
    all_goals first | rfl | trivial
  by_cases c3 : 0x67 ≤ op ∧ op ≤ 0x69
  · simp only [execNum, c0, c1, c2, c3, ite_true, ite_false, pop_n_stack_form]
    repeat' (split <;> (try simp_all only []))
    all_goals try simp only [pushI32, pushI64, pushV]
    all_goals first | rfl | trivial
  by_cases c4 : 0x79 ≤ op ∧ op ≤ 0x7B
  · simp only [execNum, c0, c1, c2, c3, c4, ite_true, ite_false, pop_n_stack_form]
    repeat' (split <;> (try simp_all only []))
    all_goals try simp only [pushI32, pushI64, pushV]
    all_goals first | rfl | trivial
  by_cases c5 : (0x6A ≤ op ∧ op ≤ 0x78) ∨ (0x7C ≤ op ∧ op ≤ 0x8A)
  · simp only [execNum, c0, c1, c2, c3, c4, c5, ite_true, ite_false, pop_n_stack_form]
    repeat' (split <;> (try simp_all only []))
    all_goals try simp only [pushI32, pushI64, pushV]
    all_goals first | rfl | trivial
  simp only [execNum, c0, c1, c2, c3, c4, c5, ite_true, ite_false, pop_n_stack_form]
  repeat' (split <;> (try simp_all only []))
  all_goals try simp only [pushI32, pushI64, pushV]
  all_goals first | rfl | trivial


theorem numeric_instruction_keeps_backend (cfg : NearCfg) (p : Prepared)
    (s : St) (f : Frame) (pf : PFunc) (op : Nat) :
    ResultKeepsBackend s (exec cfg p s f pf (.num op)) := by
  have hn := exec_num_keeps_real s op
  simp only [exec]
  cases he : execNum s op with
  | error e =>
    simp only [he]
    split <;> first | rfl | trivial
  | ok u =>
    simp only [he, NumericKeepsReal] at hn
    change (setFrame u _).real.isSome = s.real.isSome
    rw [set_frame_real, hn]

end NearCompression
