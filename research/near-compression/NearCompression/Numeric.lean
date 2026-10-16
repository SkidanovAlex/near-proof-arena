import NearCompression.Calls

/-! Numeric execution simulation against the actual integer interpreter.
Numeric algorithms and their traps are retained, not replaced by field arithmetic. -/
namespace NearCompression
open NearSpecV3.Wasm

def numericValue : Val → Nat
  | .i32 v => v.toNat
  | .i64 v => v.toNat
  | .ref _ => 0

theorem pop_n_stack_form (s : St) : popN s =
    (numericValue (s.stack.back?.getD (.i32 0)), { s with stack := s.stack.pop }) := by
  unfold popN popV
  cases s.stack.back?.getD (.i32 0) <;> rfl

theorem exec_num_equiv (s t : St) (h : StateEquivalent s t) (op : Nat) :
    StateExceptEquivalent (execNum s op) (execNum t op) := by
  have hv : s.stack = t.stack := by have he := congrArg St.stack h.core; exact he
  by_cases c0 : op = 0x45
  · simp only [execNum, c0, ite_true, ite_false, pop_n_stack_form, hv]
    repeat' (split <;> (try simp_all only []))
    all_goals try simp only [pushI32, pushI64, pushV]
    all_goals first | exact state_equiv_set_stack s t h _ | rfl
  by_cases c1 : op = 0x50
  · simp only [execNum, c0, c1, ite_true, ite_false, pop_n_stack_form, hv]
    repeat' (split <;> (try simp_all only []))
    all_goals try simp only [pushI32, pushI64, pushV]
    all_goals first | exact state_equiv_set_stack s t h _ | rfl
  by_cases c2 : (0x46 ≤ op ∧ op ≤ 0x4F) ∨ (0x51 ≤ op ∧ op ≤ 0x5A)
  · simp only [execNum, c0, c1, c2, ite_true, ite_false, pop_n_stack_form, hv]
    repeat' (split <;> (try simp_all only []))
    all_goals try simp only [pushI32, pushI64, pushV]
    all_goals first | exact state_equiv_set_stack s t h _ | rfl
  by_cases c3 : 0x67 ≤ op ∧ op ≤ 0x69
  · simp only [execNum, c0, c1, c2, c3, ite_true, ite_false, pop_n_stack_form, hv]
    repeat' (split <;> (try simp_all only []))
    all_goals try simp only [pushI32, pushI64, pushV]
    all_goals first | exact state_equiv_set_stack s t h _ | rfl
  by_cases c4 : 0x79 ≤ op ∧ op ≤ 0x7B
  · simp only [execNum, c0, c1, c2, c3, c4, ite_true, ite_false, pop_n_stack_form, hv]
    repeat' (split <;> (try simp_all only []))
    all_goals try simp only [pushI32, pushI64, pushV]
    all_goals first | exact state_equiv_set_stack s t h _ | rfl
  by_cases c5 : (0x6A ≤ op ∧ op ≤ 0x78) ∨ (0x7C ≤ op ∧ op ≤ 0x8A)
  · simp only [execNum, c0, c1, c2, c3, c4, c5, ite_true, ite_false, pop_n_stack_form, hv]
    repeat' (split <;> (try simp_all only []))
    all_goals try simp only [pushI32, pushI64, pushV]
    all_goals first | exact state_equiv_set_stack s t h _ | rfl
  simp only [execNum, c0, c1, c2, c3, c4, c5, ite_true, ite_false, pop_n_stack_form, hv]
  repeat' (split <;> (try simp_all only []))
  all_goals try simp only [pushI32, pushI64, pushV]
  all_goals first | exact state_equiv_set_stack s t h _ | rfl

theorem exec_numeric_instruction_equiv (cfg : NearCfg) (p : Prepared)
    (s t : St) (h : StateEquivalent s t) (f : Frame) (pf : PFunc) (op : Nat) :
    ResultEquivalent (exec cfg p s f pf (.num op)) (exec cfg p t f pf (.num op)) := by
  have hn := exec_num_equiv s t h op
  simp only [exec]
  cases hs : execNum s op <;> cases ht : execNum t op <;>
    simp only [hs, ht, StateExceptEquivalent] at hn
  · simp only [hs, ht]
    rw [hn]
    split
    · exact ⟨h, rfl⟩
    · rfl
  · simp only [hs, ht]
    exact state_equiv_set_frame _ _ hn _

end NearCompression
