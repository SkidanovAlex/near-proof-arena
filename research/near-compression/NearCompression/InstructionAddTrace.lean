import NearCompression.InstructionAdd

namespace NearCompression
open NearSpecV3.Wasm ZkFormal.Air ZkFormal.Algebra

/-- Expressions whose value depends only on current-row columns and constants. -/
def instructionLocalExpr : Expr → Prop
  | .const _ => True
  | .col _ nx => nx = false
  | .add a b | .mul a b => instructionLocalExpr a ∧ instructionLocalExpr b
  | .neg a => instructionLocalExpr a
  | _ => False

/-- The gadget evaluator agrees with the actual AIR trace evaluator for local expressions. -/
theorem instruction_local_eval (e : Expr) (tr : Trace Fp) (t r : Nat)
    (pub : List Fp) (localExpr : instructionLocalExpr e) :
    e.eval tr t r pub = e.evalWith (instructionAddEnv (tr.cell t r)) := by
  induction e with
  | const n => rfl
  | col c nx =>
    have h : nx = false := localExpr
    subst nx
    rfl
  | add a b ia ib =>
    obtain ⟨ha, hb⟩ := localExpr
    change a.eval tr t r pub + b.eval tr t r pub = _
    rw [ia ha, ib hb]
    rfl
  | mul a b ia ib =>
    obtain ⟨ha, hb⟩ := localExpr
    change a.eval tr t r pub * b.eval tr t r pub = _
    rw [ia ha, ib hb]
    rfl
  | neg a ia => exact congrArg Neg.neg (ia localExpr)
  | pub i => exact False.elim localExpr
  | isFirst => exact False.elim localExpr
  | isLast => exact False.elim localExpr
  | isTransition => exact False.elim localExpr

/-- Extract the arithmetic row predicate from the actual AIR semantic relation. -/
theorem instruction_add32_trace_holds (air : Air) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t < air.tables.length)
    (table : air.tables[t] = instructionAdd32Table)
    (holds : Holds air pub tr) (r : Nat) (hr : r < tr.height t) :
    instructionAdd32Holds (tr.cell t r) := by
  intro e he
  have hc := holds.constr t ht r hr e
  rw [table] at hc
  have hv := hc he
  have hl : instructionLocalExpr e := by
    simp only [instructionAdd32Constraints, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with he | he | he | he <;> subst e <;> simp [instructionLocalExpr]
  rw [instruction_local_eval e tr t r pub hl] at hv
  exact hv

/-- Actual trace satisfaction implies the Wasm helper result, with explicit ranges. -/
theorem instruction_add32_trace_binop (air : Air) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t < air.tables.length)
    (table : air.tables[t] = instructionAdd32Table)
    (holds : Holds air pub tr) (r : Nat) (hr : r < tr.height t)
    (ranges : instructionAdd32Ranges (tr.cell t r)) :
    Num.binop 32 0 (instructionAddWord (tr.cell t r) 0 1)
      (instructionAddWord (tr.cell t r) 2 3) =
      some (instructionAddWord (tr.cell t r) 4 5) :=
  instruction_add32_binop _ ranges
    (instruction_add32_trace_holds air tr pub t ht table holds r hr)

/-- The arithmetic subtable meets the existing verifier's structural limits. -/
theorem instruction_add32_table_wf :
    instructionAdd32Table.wf ⟨[instructionAdd32Table], 0, 0⟩ 2 = true := by
  decide

end NearCompression
