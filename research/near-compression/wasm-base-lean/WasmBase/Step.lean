import WasmBase.SpecLemmas
/-!
# WasmBase.Step — one spec `step` from the simulation relation

`step_eq_exec`: the gas charge at the pc (constant fee `R · fee`, D2) succeeds because the final
gas check `R · S_final ≤ g0` bounds every intermediate sum.  `straight_rel`: the generic successor
relation for instructions that keep the label stack and move to `pc + 1`.
-/
namespace WasmBase
open NearSpecV3.Wasm
set_option linter.unusedSimpArgs false

theorem step_eq_exec (X : Ctx) {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} (R : RelW X s f tps tpl t pc S live) {ins : Instr} {fee : Nat}
    (hins : X.pf.code[pc]? = some ins) (hfee : feeUnits X.cfg X.pf.gas[pc]? = some fee)
    (hg : X.R * (S + fee) ≤ X.g0) (hg64 : X.g0 < 2 ^ 64) :
    step X.cfg X.p s = exec X.cfg X.p { s with gas := { s.gas with g := s.gas.g - X.R * fee } } f X.pf ins := by
  have hgas := R.gas
  have hpf : X.p.funcs[f.fn]? = some X.pf := by rw [R.fn]; exact X.hpf
  have hcode : X.pf.code[f.pc]? = some ins := by rw [R.pcEq]; exact hins
  cases hg' : X.pf.gas[pc]? with
  | none => simp [feeUnits, hg'] at hfee
  | some e =>
    cases e with
    | none =>
      simp only [feeUnits, hg', Option.some.injEq] at hfee
      subst hfee
      have hge : X.pf.gas[f.pc]? = some none := by rw [R.pcEq]; exact hg'
      rw [Nat.mul_zero, Nat.sub_zero, show ({ s with gas := { s.gas with g := s.gas.g } } : St) = s from rfl]
      simp only [step, R.frames, hpf, hcode, hge]
    | some kf =>
      obtain ⟨k, fe⟩ := kf
      simp only [feeUnits, hg'] at hfee
      split at hfee
      · rename_i hc
        obtain ⟨hl, hR, hmod, _⟩ := hc
        simp only [Option.some.injEq] at hfee
        have hc : fe.c = X.R * fee := by
          rw [← hfee]; unfold Ctx.R; exact (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hmod)).symm
        have hge : X.pf.gas[f.pc]? = some (some (k, fe)) := by rw [R.pcEq]; exact hg'
        have hamt : ∀ n, n * fe.l + fe.c = X.R * fee := by intro n; rw [hl, hc]; simp
        have hlt : ¬ (X.R * fee ≥ u64Bound) := by
          unfold u64Bound; have := Nat.mul_le_mul_left X.R (Nat.le_add_left fee S); omega
        have hle : ¬ (X.R * fee > s.gas.g) := by
          have : X.R * (S + fee) = X.R * S + X.R * fee := Nat.mul_add _ _ _
          omega
        simp only [step, R.frames, hpf, hcode, hge, charge, hamt, hlt, hle, ite_false]
      · simp at hfee

/-- The view relation after an instruction that keeps the labels, moves to `pc + 1`, pops `k` stack
entries and pushes the entries of `stk'` beyond `n - k`, and changes locals at most at `J`. -/
theorem straight_rel (X : Ctx) {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S fee k : Nat}
    {live : Msg → Prop} (R : RelW X s f tps tpl t pc S live)
    (hk : k ≤ s.stack.size) (stk' locs' : Array Val) (J : Option Nat)
    (keep : ∀ i, i < s.stack.size - k → stk'[i]? = s.stack[i]?) (hsz : s.stack.size - k ≤ stk'.size)
    (hnum : ∀ i, i < stk'.size → isNum (stk'[i]?.getD default))
    (lsz : locs'.size = f.locals.size) (lkeep : ∀ j, some j ≠ J → locs'[j]? = f.locals[j]?)
    (hJ : ∀ j, J = some j → j < f.locals.size)
    (lnum : ∀ j, j < locs'.size → isNum (locs'[j]?.getD default))
    (hnext : pc + 1 < X.pf.code.size) (hL : X.ck.labels[pc + 1]? = some f.labels)
    (hH : X.ck.heights[pc + 1]? = some stk'.size)
    (hgs : X.R * (S + fee) ≤ X.g0)
    (s' : St) (hs'stk : s'.stack = stk') (hs'fr : s'.frames = [{ f with pc := pc + 1, locals := locs' }])
    (hs'g : s'.gas.g = s.gas.g - X.R * fee) :
    RelW X s' { f with pc := pc + 1, locals := locs' }
      (fun i => if i < s.stack.size - k then tps i else t) (fun j => if some j = J then t else tpl j)
      (t + 1) (pc + 1) (S + fee)
      (stepLive live
        (((List.range k).map fun d => enc 0 (s.stack.size - k + d)
            (s.stack[s.stack.size - k + d]?.getD default) (tps (s.stack.size - k + d))) ++
          J.toList.map (fun j => enc 1 j (f.locals[j]?.getD default) (tpl j)))
        (((List.range (stk'.size - (s.stack.size - k))).map fun d =>
            enc 0 (s.stack.size - k + d) (stk'[s.stack.size - k + d]?.getD default) t) ++
          J.toList.map (fun j => enc 1 j (locs'[j]?.getD default) t))) where
  frames := hs'fr
  fn := R.fn
  pcEq := rfl
  pcLt := hnext
  labels := hL
  base := R.base
  height := by rw [hs'stk]; exact hH
  nloc := by simp [lsz, R.nloc]
  gas := by
    have hg := R.gas
    have : X.R * (S + fee) = X.R * S + X.R * fee := Nat.mul_add _ _ _
    rw [hs'g]; omega
  numS := by rw [hs'stk]; exact hnum
  numL := lnum
  tpsLt := by
    intro i hi
    show (if i < s.stack.size - k then tps i else t) < t + 1
    split
    · have := R.tpsLt i (by omega); omega
    · omega
  tplLt := by
    intro j hj
    show (if some j = J then t else tpl j) < t + 1
    split
    · omega
    · have := R.tplLt j (by simpa [lsz] using hj); omega
  live := by
    intro x
    rw [hs'stk]
    simp only [stepLive]
    rw [view_update J hk keep hsz lsz lkeep hJ R.tpsLt R.tplLt x]
    constructor
    · rintro (⟨h1, h2⟩ | h3)
      · exact Or.inl ⟨(R.live x).mp h1, h2⟩
      · exact Or.inr h3
    · rintro (⟨h1, h2⟩ | h3)
      · exact Or.inl ⟨(R.live x).mpr h1, h2⟩
      · exact Or.inr h3

end WasmBase
