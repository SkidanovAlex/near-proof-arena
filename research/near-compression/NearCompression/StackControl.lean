import NearCompression.Numeric

/-! Stack and structured-control instruction families of the actual interpreter.
This coverage predicate groups proved cases; it does not restrict the challenge
or discharge the remaining instruction families. -/
namespace NearCompression
open NearSpecV3.Wasm

def referenceValue : Val → Option Nat
  | .ref r => r
  | _ => none

theorem pop_ref_stack_form (s : St) : popRef s =
    (referenceValue (s.stack.back?.getD (.i32 0)), { s with stack := s.stack.pop }) := by
  unfold popRef popV
  cases s.stack.back?.getD (.i32 0) <;> rfl

theorem state_equiv_stack_globals (s t : St) (h : StateEquivalent s t)
    (stack : Array Val) (globals : Array Val) :
    StateEquivalent { s with stack, globals } { t with stack, globals } :=
  ⟨congrArg (fun s : St => { s with stack, globals }) h.core, h.real⟩

def StackControlInstruction : Instr → Prop
  | .unreachable | .nop | .block _ | .loop _ | .if_ _ | .else_ | .end_
  | .br _ | .brIf _ | .brTable _ _ | .ret
  | .refNull _ | .refFunc _ | .refIsNull | .drop | .select _
  | .globalGet _ | .globalSet _ | .localGet _ | .localSet _ | .localTee _ | .i32Const _ | .i64Const _ => True
  | _ => False

theorem stack_control_instruction_equiv (cfg : NearCfg) (p : Prepared)
    (s t : St) (h : StateEquivalent s t) (f : Frame) (pf : PFunc)
    (i : Instr) (covered : StackControlInstruction i) :
    ResultEquivalent (exec cfg p s f pf i) (exec cfg p t f pf i) := by
  have hv : s.stack = t.stack := by have he := congrArg St.stack h.core; exact he
  have hg : s.globals = t.globals := by have he := congrArg St.globals h.core; exact he
  cases i <;> simp only [StackControlInstruction] at covered
  all_goals simp only [exec, pop_n_stack_form, pop_ref_stack_form, popV, pushI32, pushV, hv, hg]
  all_goals repeat' (split <;> (try simp_all only []))
  all_goals first
    | exact ⟨h, rfl⟩
    | rfl
    | exact do_return_equiv p s t h
    | exact do_br_equiv p s t h _ _
    | exact state_equiv_set_frame s t h _
    | exact state_equiv_set_frame _ _ (state_equiv_set_stack s t h _) _
    | exact do_br_equiv p _ _ (state_equiv_set_stack s t h _) _ _
    | exact state_equiv_set_frame _ _ (state_equiv_stack_globals s t h _ _) _
    | exact do_br_equiv p _ _ (state_equiv_stack_globals s t h _ _) _ _

end NearCompression
