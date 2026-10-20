import NearCompression.InstructionAddControl
import NearCompression.InstructionRangeTrace
import NearCompression.InstructionAddStep

namespace NearCompression
open NearSpecV3.Wasm ZkFormal.Air ZkFormal.Algebra

theorem instruction_control_constraints_local (e : Expr)
    (he : e ∈ instructionAdd32ControlConstraints) : instructionLocalExpr e := by
  rcases List.mem_append.mp he with he | he
  · rcases List.mem_append.mp he with he | he
    · exact instruction_range_constraints_local e he
    · simp only [instructionControlMetadataConstraints, List.mem_cons,
        List.not_mem_nil, or_false] at he
      rcases he with he | he | he | he | he | he <;> subst e <;>
        simp [instructionBitConstraint, instructionLocalExpr]
  · obtain ⟨slot, _, he⟩ := List.mem_flatMap.mp he
    rcases List.mem_cons.mp he with he | he
    · subst e
      exact ⟨rfl, instruction_bit_expr_local _ _⟩
    · obtain ⟨bit, _, he⟩ := List.mem_map.mp he
      subst e
      simp [instructionBitConstraint, instructionLocalExpr]

theorem instruction_control_trace_holds (air : Air) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t < air.tables.length)
    (table : air.tables[t] = instructionAdd32ControlTable)
    (holds : Holds air pub tr) (r : Nat) (hr : r < tr.height t) :
    instructionAdd32ControlHolds (tr.cell t r) := by
  intro e he
  have hc := holds.constr t ht r hr e
  rw [table] at hc
  have hv := hc he
  rw [instruction_local_eval e tr t r pub (instruction_control_constraints_local e he)] at hv
  exact hv

/-- The fetched row opcode and local next-PC value determine the exact step.
Fetch authentication and operand bindings remain explicit obligations. -/
theorem instruction_control_bound_step (row : Nat → Fp)
    (h : instructionAdd32ControlHolds row) (cfg : NearCfg) (p : Prepared)
    (s s₁ s₂ : St) (f : Frame) (fs : List Frame) (pf : PFunc)
    (frames : s.frames = f :: fs) (func : p.funcs[f.fn]? = some pf)
    (pc : f.pc = instructionAddWord row 105 106)
    (code : pf.code[f.pc]? = some (.num (row 104).toNat))
    (gas : pf.gas[f.pc]? = some none)
    (popRight : popN s = (instructionAddWord row 2 3, s₁))
    (popLeft : popN s₁ = (instructionAddWord row 0 1, s₂)) :
    step cfg p s = .cont (setFrame (pushI32 s₂ (instructionAddWord row 4 5))
      { f with pc := instructionAddWord row 107 108 }) := by
  have metadata :=  instruction_control_metadata_sound row h
  have fetched : pf.code[f.pc]? = some (.num 0x6A) := by
    simpa only [metadata.1] using code
  have hs := instruction_add32_step_no_charge row (instruction_control_addition_holds row h)
    cfg p s s₁ s₂ f fs pf frames func fetched gas popRight popLeft
  have nextPc : f.pc + 1 = instructionAddWord row 107 108 := by
    rw [pc]
    exact metadata.2.1
  simpa only [nextPc] using hs

end NearCompression
