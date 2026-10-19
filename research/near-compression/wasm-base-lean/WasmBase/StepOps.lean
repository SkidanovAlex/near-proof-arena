import WasmBase.Step
/-!
# WasmBase.StepOps — the spec step of each instruction class, from event messages

Each lemma takes the simulation relation at time `t`, the consumed messages (which the channel
argument shows are live) and the produced messages with the local semantic guarantee of the chip
(`*_sound` in `WasmBase.Local.*`), and returns the spec step and the relation at `t + 1`.
-/
namespace WasmBase
open NearSpecV3.Wasm
set_option linter.unusedSimpArgs false

theorem stepLive_congr {live : Msg → Prop} {c1 c2 p1 p2 : List Msg}
    (hc : ∀ x, x ∈ c1 ↔ x ∈ c2) (hp : ∀ x, x ∈ p1 ↔ x ∈ p2) :
    stepLive live c1 p1 = stepLive live c2 p2 := by
  funext x; simp only [stepLive, hc, hp]

theorem Rel_of_RelW_congr {X : Ctx} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live live' : Msg → Prop} (h : RelW X s f tps tpl t pc S live) (e : live = live') :
    Rel X s t pc S live' := ⟨f, tps, tpl, e ▸ h⟩

theorem isFamilyNum_of_binop {op : Nat} (h : isBinop op) : isFamilyNum op = true ∧ numPops op = 2 := by
  simp only [isBinop, binops, List.mem_cons, List.mem_nil_iff, or_false] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
  subst h <;> decide

theorem step_binop (X : Ctx) {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} (R : RelW X s f tps tpl t pc S live)
    {op fee : Nat} (hins : X.pf.code[pc]? = some (.num op)) (hop : isBinop op)
    (hfee : feeUnits X.cfg X.pf.gas[pc]? = some fee) (hg : X.R * (S + fee) ≤ X.g0)
    (hg64 : X.g0 < 2 ^ 64)
    (ma mb mr : Msg) (hma : live ma) (hmb : live mb)
    (sa : ma.space = 0 ∧ ma.slot = s.stack.size - 2)
    (sb : mb.space = 0 ∧ mb.slot = s.stack.size - 1)
    (sr : mr.space = 0 ∧ mr.slot = s.stack.size - 2 ∧ mr.tp = t ∧
      mr.tag = (if opW op = 64 then 1 else 0))
    (sem : ma.ok → mb.ok → mr.ok ∧ Num.binop (opW op) (opK op) ma.val mb.val = some mr.val) :
    ∃ s', step X.cfg X.p s = .cont s' ∧
      Rel X s' (t + 1) (pc + 1) (S + fee) (stepLive live [ma, mb] [mr]) := by
  have F := X.facts
  obtain ⟨hfam, hpops⟩ := isFamilyNum_of_binop hop
  have hv := F.verify pc R.pcLt
  have hL := R.labels
  have hH := R.height
  simp only [verifyAt, hins, hL, hH, kindOf, hfam, ite_true, hpops, Bool.and_eq_true,
    decide_eq_true_eq] at hv
  obtain ⟨h2, ⟨hnext, hL1⟩, hH1⟩ := hv
  -- the consumed messages are the top two stack entries
  have ea := R.stack_msg hma sa.1 (by omega)
  have eb := R.stack_msg hmb sb.1 (by omega)
  rw [sa.2] at ea; rw [sb.2] at eb
  have na := R.numS (s.stack.size - 2) (by omega)
  have nb := R.numS (s.stack.size - 1) (by omega)
  have oka : ma.ok := by rw [ea]; exact enc_ok na _ _ _
  have okb : mb.ok := by rw [eb]; exact enc_ok nb _ _ _
  obtain ⟨okr, hbin⟩ := sem oka okb
  have va : ma.val = vNum (s.stack[s.stack.size - 2]?.getD default) := by rw [ea]; exact enc_val na _ _ _
  have vb : mb.val = vNum (s.stack[s.stack.size - 1]?.getD default) := by rw [eb]; exact enc_val nb _ _ _
  -- the spec step
  rw [step_eq_exec X R hins hfee hg hg64]
  have hpopb : (popN { s with gas := { s.gas with g := s.gas.g - X.R * fee } }).1 = mb.val := by
    rw [popN_eq, vb]; simp only; rw [back_getD _ (by omega)]
  have hpopa : (popN (popN { s with gas := { s.gas with g := s.gas.g - X.R * fee } }).2).1 = ma.val := by
    rw [popN_eq, popN_eq, va]; simp only
    rw [back_getD _ (by simp; omega)]
    simp only [Array.size_pop, Array.getElem?_pop]
    rw [if_pos (by omega)]
    congr 2
  let v : Val := if opW op = 32 then .i32 (UInt32.ofNat mr.val) else .i64 (UInt64.ofNat mr.val)
  refine ⟨setFrame ({ s with gas := { s.gas with g := s.gas.g - X.R * fee }, stack := s.stack.pop.pop.push v })
    { f with pc := f.pc + 1 }, ?_, ?_⟩
  · simp only [exec, execNum_binop _ _ hop, hpopb, hpopa, hbin]
    split <;> simp [v, *, pushI32, pushI64, pushV, popN_eq]
  · have hw : opW op = 32 ∨ opW op = 64 := by unfold opW; split <;> simp
    have hvr : v = mr.toVal := by
      simp only [v, Msg.toVal, sr.2.2.2]
      rcases hw with hw | hw <;> simp [hw]
    have emr : mr = enc 0 (s.stack.size - 2) v t := by
      rw [hvr, ← sr.1, ← sr.2.1, ← sr.2.2.1]; exact (enc_of_ok okr).symm
    have hsz' : (s.stack.pop.pop.push v).size = s.stack.size - 1 := by simp; omega
    have SR := straight_rel X R (k := 2) (fee := fee) (by omega) (s.stack.pop.pop.push v) f.locals none
      (by intro i hi; simp only [Array.getElem?_push, Array.getElem?_pop, Array.size_pop]
          rw [if_neg (by omega), if_pos (by omega), if_pos (by omega)])
      (by omega)
      (by intro i hi
          simp only [Array.getElem?_push, Array.getElem?_pop, Array.size_pop] at hi ⊢
          by_cases hi' : i = s.stack.size - 1 - 1
          · rw [if_pos hi']; rw [hvr]; exact isNum_toVal mr
          · rw [if_neg hi', if_pos (by omega), if_pos (by omega)]; exact R.numS i (by omega))
      rfl (fun _ _ => rfl) (by simp) R.numL hnext hL1 (by rw [hsz', hH1]; congr 1; omega) hg
      (setFrame ({ s with gas := { s.gas with g := s.gas.g - X.R * fee }, stack := s.stack.pop.pop.push v })
        { f with pc := f.pc + 1 })
      (by simp [setFrame, R.frames]) (by simp [setFrame, R.frames, R.pcEq]) (by simp [setFrame, R.frames])
    refine Rel_of_RelW_congr SR (stepLive_congr ?_ ?_)
    · intro x
      simp only [List.mem_append, List.mem_map, List.mem_range, Option.toList_none, List.not_mem_nil,
        or_false, List.mem_cons, List.mem_nil_iff, false_and, exists_false]
      constructor
      · rintro ⟨d, hd, rfl⟩
        rcases (show d = 0 ∨ d = 1 by omega) with rfl | rfl
        · left; rw [ea, Nat.add_zero]
        · right; rw [eb, show s.stack.size - 2 + 1 = s.stack.size - 1 by omega]
      · rintro (rfl | rfl)
        · exact ⟨0, by omega, by rw [ea, Nat.add_zero]⟩
        · exact ⟨1, by omega, by rw [eb, show s.stack.size - 2 + 1 = s.stack.size - 1 by omega]⟩
    · intro x
      simp only [List.mem_append, List.mem_map, List.mem_range, Option.toList_none, List.not_mem_nil,
        or_false, List.mem_cons, List.mem_nil_iff, hsz', false_and, exists_false]
      constructor
      · rintro ⟨d, hd, rfl⟩
        have : d = 0 := by omega
        subst this
        rw [emr]; simp only [Nat.add_zero, Array.getElem?_push, Array.size_pop]
        rw [if_pos (by omega)]; rfl
      · rintro rfl
        refine ⟨0, by omega, ?_⟩
        rw [emr]; simp only [Nat.add_zero, Array.getElem?_push, Array.size_pop]
        rw [if_pos (by omega)]; rfl

end WasmBase

namespace WasmBase
open NearSpecV3.Wasm

/-- A trapping binary op (div/rem by zero, signed overflow): the spec step aborts, having charged
the fee. -/
theorem step_binop_trap (X : Ctx) {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} (R : RelW X s f tps tpl t pc S live)
    {op fee : Nat} (hins : X.pf.code[pc]? = some (.num op)) (hop : isBinop op)
    (hfee : feeUnits X.cfg X.pf.gas[pc]? = some fee) (hg : X.R * (S + fee) ≤ X.g0)
    (hg64 : X.g0 < 2 ^ 64)
    (ma mb : Msg) (hma : live ma) (hmb : live mb)
    (sa : ma.space = 0 ∧ ma.slot = s.stack.size - 2)
    (sb : mb.space = 0 ∧ mb.slot = s.stack.size - 1)
    (sem : ma.ok → mb.ok → Num.binop (opW op) (opK op) ma.val mb.val = none) :
    ∃ sN e, step X.cfg X.p s = .abort sN e ∧ X.R * (S + fee) + sN.gas.g = X.g0 := by
  have F := X.facts
  obtain ⟨hfam, hpops⟩ := isFamilyNum_of_binop hop
  have hv := F.verify pc R.pcLt
  have hL := R.labels
  have hH := R.height
  simp only [verifyAt, hins, hL, hH, kindOf, hfam, ite_true, hpops, Bool.and_eq_true,
    decide_eq_true_eq] at hv
  obtain ⟨h2, -, -⟩ := hv
  have ea := R.stack_msg hma sa.1 (by omega)
  have eb := R.stack_msg hmb sb.1 (by omega)
  rw [sa.2] at ea; rw [sb.2] at eb
  have na := R.numS (s.stack.size - 2) (by omega)
  have nb := R.numS (s.stack.size - 1) (by omega)
  have oka : ma.ok := by rw [ea]; exact enc_ok na _ _ _
  have okb : mb.ok := by rw [eb]; exact enc_ok nb _ _ _
  have hbin := sem oka okb
  have va : ma.val = vNum (s.stack[s.stack.size - 2]?.getD default) := by rw [ea]; exact enc_val na _ _ _
  have vb : mb.val = vNum (s.stack[s.stack.size - 1]?.getD default) := by rw [eb]; exact enc_val nb _ _ _
  rw [step_eq_exec X R hins hfee hg hg64]
  have hpopb : (popN { s with gas := { s.gas with g := s.gas.g - X.R * fee } }).1 = mb.val := by
    rw [popN_eq, vb]; simp only; rw [back_getD _ (by omega)]
  have hpopa : (popN (popN { s with gas := { s.gas with g := s.gas.g - X.R * fee } }).2).1 = ma.val := by
    rw [popN_eq, popN_eq, va]; simp only
    rw [back_getD _ (by simp; omega)]
    simp only [Array.size_pop, Array.getElem?_pop]
    rw [if_pos (by omega)]
    congr 2
  refine ⟨{ s with gas := { s.gas with g := s.gas.g - X.R * fee } }, trapStr "IllegalArithmetic", ?_, ?_⟩
  · have htr : (trapStr "IllegalArithmetic").startsWith "WasmTrap" = true := by decide +kernel
    simp only [exec, execNum_binop _ _ hop, hpopb, hpopa, hbin, htr, ite_true]
  · have hgas := R.gas
    simp only
    rw [Nat.mul_add] at hg ⊢
    omega

end WasmBase
