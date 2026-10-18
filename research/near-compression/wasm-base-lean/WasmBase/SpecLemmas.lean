import WasmBase.Event
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
