import WasmBase.Event
import WasmBase.CheckFacts
/-!
# Spec-side lemmas: `execNum` on family opcodes, popping, pushing
-/
namespace WasmBase
open NearSpecV3.Wasm
set_option linter.unusedSimpArgs false

/-- Binary arithmetic family opcodes (no div/rem) and their width / binop index. -/
def binops : List Nat := [0x6A, 0x6B, 0x6C, 0x71, 0x72, 0x73, 0x74, 0x75, 0x76, 0x77, 0x78,
  0x7C, 0x7D, 0x7E, 0x83, 0x84, 0x85, 0x86, 0x87, 0x88, 0x89, 0x8A]
def isBinop (op : Nat) : Prop := op ∈ binops

def opW (op : Nat) : Nat := if op ≤ 0x78 then 32 else 64
def opK (op : Nat) : Nat := if op ≤ 0x78 then op - 0x6A else op - 0x7C

theorem execNum_binop (s : St) (op : Nat) (hop : isBinop op) :
    execNum s op =
      (match Num.binop (opW op) (opK op) (popN (popN s).2).1 (popN s).1 with
       | some r => .ok (if opW op = 32 then pushI32 (popN (popN s).2).2 r else pushI64 (popN (popN s).2).2 r)
       | none => .error (trapStr "IllegalArithmetic")) := by
  simp only [isBinop, binops, List.mem_cons, List.mem_nil_iff, or_false] at hop
  rcases hop with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
  subst h <;> simp [execNum, opW, opK] <;> rfl

end WasmBase

namespace WasmBase
theorem Ctx.facts (X : Ctx) : CheckFacts X.cfg X.p X.fn X.pf X.ck := by
  obtain ⟨pf', h⟩ := check_sound X.hck
  have : pf' = X.pf := by have := h.func; rw [X.hpf] at this; exact (Option.some.inj this).symm
  subst this; exact h
end WasmBase

namespace WasmBase
open NearSpecV3.Wasm

theorem popN_eq (s : St) :
    popN s = (vNum (s.stack.back?.getD (.i32 0)), { s with stack := s.stack.pop }) := by
  unfold popN popV
  cases s.stack.back?.getD (.i32 0) <;> rfl

theorem popV_eq (s : St) : popV s = (s.stack.back?.getD (.i32 0), { s with stack := s.stack.pop }) := rfl

theorem back_getD (a : Array Val) (h : 0 < a.size) :
    a.back?.getD (.i32 0) = a[a.size - 1]?.getD default := by
  rw [Array.back?_eq_getElem?, Array.getElem?_eq_getElem (by omega)]
  rfl

theorem getD_eq_of_getElem? {a : Array Val} {i : Nat} (h : i < a.size) :
    a[i]?.getD default = a[i] := by
  rw [Array.getElem?_eq_getElem h]; rfl

/-- `vNum` of a well-formed message's decoded value is its value. -/
theorem vNum_toVal {m : Msg} (hm : m.ok) : vNum m.toVal = m.val := by
  have := enc_val (v := m.toVal) (by unfold Msg.toVal; split <;> trivial) m.space m.slot m.tp
  rw [enc_of_ok hm] at this
  exact this.symm

theorem isNum_toVal (m : Msg) : isNum m.toVal := by unfold Msg.toVal; split <;> trivial

end WasmBase
