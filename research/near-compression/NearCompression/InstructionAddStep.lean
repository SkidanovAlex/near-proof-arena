import NearCompression.InstructionAddRange

/-! Exact whole-state step semantics for the addition gadget. Prepared-code
fetch, stack bindings and gas metadata remain explicit premises; this file
does not claim those facts are enforced by polynomial constraints yet. -/
namespace NearCompression
open NearSpecV3.Wasm ZkFormal.Algebra

theorem instruction_add32_pop_push (s : St) (v : UInt32) :
    popN (pushV s (.i32 v)) = (v.toNat, s) := by
  simp [popN, popV, pushV]

/-- Polynomial arithmetic result is connected to exact instruction execution,
including the program-counter update and all untouched state fields. -/
theorem instruction_add32_exec (row : Nat → Fp)
    (h : instructionAdd32RangeHolds row) (cfg : NearCfg) (p : Prepared)
    (s s₁ s₂ : St) (f : Frame) (pf : PFunc)
    (popRight : popN s = (instructionAddWord row 2 3, s₁))
    (popLeft : popN s₁ = (instructionAddWord row 0 1, s₂)) :
    exec cfg p s f pf (.num 0x6A) =
      .cont (setFrame (pushI32 s₂ (instructionAddWord row 4 5))
        { f with pc := f.pc + 1 }) := by
  have hn := instruction_add32_range_exec_num row h s s₁ s₂ popRight popLeft
  simp only [exec, hn]

/-- The stack bindings can be discharged for a concrete pair of i32 operands. -/
theorem instruction_add32_exec_stack (row : Nat → Fp)
    (h : instructionAdd32RangeHolds row) (cfg : NearCfg) (p : Prepared)
    (s : St) (a b : UInt32) (f : Frame) (pf : PFunc)
    (left : instructionAddWord row 0 1 = a.toNat)
    (right : instructionAddWord row 2 3 = b.toNat) :
    exec cfg p (pushV (pushV s (.i32 a)) (.i32 b)) f pf (.num 0x6A) =
      .cont (setFrame (pushI32 s (instructionAddWord row 4 5))
        { f with pc := f.pc + 1 }) := by
  apply instruction_add32_exec row h cfg p _ (pushV s (.i32 a)) s f pf
  · rw [right]; exact instruction_add32_pop_push _ _
  · rw [left]; exact instruction_add32_pop_push _ _

/-- A fetched addition with no charge point executes exactly the proved step. -/
theorem instruction_add32_step_no_charge (row : Nat → Fp)
    (h : instructionAdd32RangeHolds row) (cfg : NearCfg) (p : Prepared)
    (s s₁ s₂ : St) (f : Frame) (fs : List Frame) (pf : PFunc)
    (frames : s.frames = f :: fs) (func : p.funcs[f.fn]? = some pf)
    (code : pf.code[f.pc]? = some (.num 0x6A))
    (gas : pf.gas[f.pc]? = some none)
    (popRight : popN s = (instructionAddWord row 2 3, s₁))
    (popLeft : popN s₁ = (instructionAddWord row 0 1, s₂)) :
    step cfg p s = .cont (setFrame (pushI32 s₂ (instructionAddWord row 4 5))
      { f with pc := f.pc + 1 }) := by
  simp only [step, frames, func, code, gas]
  exact instruction_add32_exec row h cfg p s s₁ s₂ f pf popRight popLeft

/-- Successful instrumentation changes only the fast gas counter. -/
theorem instruction_add32_charge_success (s : St) (fee : Fee) (count : Nat)
    (noOverflow : count * fee.l + fee.c < u64Bound)
    (enough : count * fee.l + fee.c ≤ s.gas.g) :
    charge s fee count =
      .cont { s with gas := { s.gas with g := s.gas.g - (count * fee.l + fee.c) } } := by
  simp only [charge, Nat.not_le.mpr noOverflow, if_false, Nat.not_lt.mpr enough]

/-- Failed charging returns its exact failure state before consuming operands. -/
theorem instruction_add32_step_charge_abort (cfg : NearCfg) (p : Prepared)
    (s failed : St) (f : Frame) (fs : List Frame) (pf : PFunc) (k : IK) (fee : Fee)
    (error : String) (frames : s.frames = f :: fs)
    (func : p.funcs[f.fn]? = some pf) (code : pf.code[f.pc]? = some (.num 0x6A))
    (gas : pf.gas[f.pc]? = some (some (k, fee)))
    (failure : charge s fee (if k = IK.linear then topCount s else 0) = .abort failed error) :
    step cfg p s = .abort failed error := by
  simp only [step, frames, func, code, gas, failure]

/-- Link-error/unmodeled charging also propagates before instruction execution. -/
theorem instruction_add32_step_charge_unmodeled (cfg : NearCfg) (p : Prepared)
    (s : St) (f : Frame) (fs : List Frame) (pf : PFunc) (k : IK) (fee : Fee)
    (error : String) (frames : s.frames = f :: fs)
    (func : p.funcs[f.fn]? = some pf) (code : pf.code[f.pc]? = some (.num 0x6A))
    (gas : pf.gas[f.pc]? = some (some (k, fee)))
    (failure : charge s fee (if k = IK.linear then topCount s else 0) = .unmodeled error) :
    step cfg p s = .unmodeled error := by
  simp only [step, frames, func, code, gas, failure]

/-- Stack pops commute with the gas-only instrumentation update. -/
theorem instruction_add32_pop_gas (s : St) (gas : Gas) :
    popN { s with gas := gas } = ((popN s).1, { (popN s).2 with gas := gas }) := by
  unfold popN popV
  cases s.stack.back?.getD (.i32 0) <;> rfl

/-- Successful charging followed by addition, with the exact fast-gas and PC
updates. Stack bindings are taken from the original pre-charge state. -/
theorem instruction_add32_step_charge_success (row : Nat → Fp)
    (h : instructionAdd32RangeHolds row) (cfg : NearCfg) (p : Prepared)
    (s s₁ s₂ : St) (f : Frame) (fs : List Frame) (pf : PFunc) (k : IK) (fee : Fee)
    (frames : s.frames = f :: fs) (func : p.funcs[f.fn]? = some pf)
    (code : pf.code[f.pc]? = some (.num 0x6A))
    (gas : pf.gas[f.pc]? = some (some (k, fee)))
    (popRight : popN s = (instructionAddWord row 2 3, s₁))
    (popLeft : popN s₁ = (instructionAddWord row 0 1, s₂))
    (noOverflow : (if k = IK.linear then topCount s else 0) * fee.l + fee.c < u64Bound)
    (enough : (if k = IK.linear then topCount s else 0) * fee.l + fee.c ≤ s.gas.g) :
    step cfg p s = .cont (setFrame
      (pushI32 { s₂ with gas := { s.gas with g := s.gas.g -
        ((if k = IK.linear then topCount s else 0) * fee.l + fee.c) } }
        (instructionAddWord row 4 5)) { f with pc := f.pc + 1 }) := by
  have charged := instruction_add32_charge_success s fee
    (if k = IK.linear then topCount s else 0) noOverflow enough
  let gs := { s.gas with g := s.gas.g -
    ((if k = IK.linear then topCount s else 0) * fee.l + fee.c) }
  have pr : popN { s with gas := gs } =
      (instructionAddWord row 2 3, { s₁ with gas := gs }) := by
    rw [instruction_add32_pop_gas, popRight]
  have pl : popN { s₁ with gas := gs } =
      (instructionAddWord row 0 1, { s₂ with gas := gs }) := by
    rw [instruction_add32_pop_gas, popLeft]
  have he := instruction_add32_exec row h cfg p _ _ _ f pf pr pl
  simp only [step, frames, func, code, gas, charged]
  simpa only [gs, frames] using he

/-- Overflow burns the synchronized remaining gas and returns the resulting
abort state; it cannot reach the arithmetic instruction. -/
theorem instruction_add32_charge_overflow (s synced : St) (fee : Fee) (count : Nat)
    (gs : Gas) (error : Option String)
    (overflow : u64Bound ≤ count * fee.l + fee.c)
    (syncedState : sync s = .ok synced)
    (burned : burn synced.gas synced.gas.remaining = (gs, error)) :
    charge s fee count = .abort { synced with gas := gs } (error.getD errIntOverflow) := by
  simp only [charge, overflow, if_true, syncedState, burned]
  cases error <;> rfl

/-- An insufficient fast-gas counter takes the synchronized burn/failure path,
with the exact failure gas state retained. -/
theorem instruction_add32_charge_insufficient (s synced : St) (fee : Fee) (count : Nat)
    (gs : Gas) (error : String)
    (noOverflow : count * fee.l + fee.c < u64Bound)
    (insufficient : s.gas.g < count * fee.l + fee.c)
    (syncedState : sync s = .ok synced)
    (burned : burn synced.gas (count * fee.l + fee.c) = (gs, some error)) :
    charge s fee count = .abort { synced with gas := gs } error := by
  simp only [charge, Nat.not_le.mpr noOverflow, if_false, insufficient, if_true,
    syncedState, burned]

end NearCompression
