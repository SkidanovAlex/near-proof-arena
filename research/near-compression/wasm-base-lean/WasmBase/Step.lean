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

theorem step_eq_exec (X : Ctx) {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} (R : RelW X E s f tps tpl t pc S live) {ins : Instr} {fee : Nat}
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

/-- The live-set part of `straight_rel` (no heap facts needed). -/
theorem straight_live (X : Ctx) {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S k : Nat}
    {live : Msg → Prop} (R : RelW X E s f tps tpl t pc S live)
    (hk : k ≤ s.stack.size) (stk' locs' : Array Val) (J : Option Nat)
    (keep : ∀ i, i < s.stack.size - k → stk'[i]? = s.stack[i]?) (hsz : s.stack.size - k ≤ stk'.size)
    (lsz : locs'.size = f.locals.size) (lkeep : ∀ j, some j ≠ J → locs'[j]? = f.locals[j]?)
    (hJ : ∀ j, J = some j → j < f.locals.size) (x : Msg) :
    stepLive live
        (((List.range k).map fun d => enc 0 (s.stack.size - k + d)
            (s.stack[s.stack.size - k + d]?.getD default) (tps (s.stack.size - k + d))) ++
          J.toList.map (fun j => enc E.lsp j (f.locals[j]?.getD default) (tpl j)))
        (((List.range (stk'.size - (s.stack.size - k))).map fun d =>
            enc 0 (s.stack.size - k + d) (stk'[s.stack.size - k + d]?.getD default) t) ++
          J.toList.map (fun j => enc E.lsp j (locs'[j]?.getD default) t)) x ↔
      x ∈ stackView stk' (fun i => if i < s.stack.size - k then tps i else t) ∨
      x ∈ localView E.lsp locs' (fun j => if some j = J then t else tpl j) ∨ E.live x := by
  simp only [stepLive]
  have vu := view_update (sp := E.lsp) (by simp [Env.lsp]) J hk keep hsz lsz lkeep hJ R.tpsLt R.tplLt x
  -- environment messages are never consumed or produced here (other spaces)
  have hcons : E.live x → x ∉ (((List.range k).map fun d => enc 0 (s.stack.size - k + d)
      (s.stack[s.stack.size - k + d]?.getD default) (tps (s.stack.size - k + d))) ++
      J.toList.map (fun j => enc E.lsp j (f.locals[j]?.getD default) (tpl j))) := by
    intro he hx
    obtain ⟨h0, h1⟩ := R.envSep x he
    simp only [List.mem_append, List.mem_map, List.mem_range, Option.mem_toList] at hx
    rcases hx with ⟨d, _, rfl⟩ | ⟨j, _, rfl⟩
    · exact h0 rfl
    · exact h1 rfl
  have hprod : E.live x → x ∉ (((List.range (stk'.size - (s.stack.size - k))).map fun d =>
      enc 0 (s.stack.size - k + d) (stk'[s.stack.size - k + d]?.getD default) t) ++
      J.toList.map (fun j => enc E.lsp j (locs'[j]?.getD default) t)) := by
    intro he hx
    obtain ⟨h0, h1⟩ := R.envSep x he
    simp only [List.mem_append, List.mem_map, List.mem_range, Option.mem_toList] at hx
    rcases hx with ⟨d, _, rfl⟩ | ⟨j, _, rfl⟩
    · exact h0 rfl
    · exact h1 rfl
  have toLive : x ∈ stackView s.stack tps ∨ x ∈ localView E.lsp f.locals tpl → live x := fun h =>
    (R.live x).mpr (h.elim Or.inl (fun h => Or.inr (Or.inl h)))
  constructor
  · rintro (⟨h1, h2⟩ | h3)
    · rcases (R.live x).mp h1 with h | h | h
      · rcases vu.mpr (Or.inl ⟨Or.inl h, h2⟩) with h' | h'
        · exact Or.inl h'
        · exact Or.inr (Or.inl h')
      · rcases vu.mpr (Or.inl ⟨Or.inr h, h2⟩) with h' | h'
        · exact Or.inl h'
        · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr h)
    · rcases vu.mpr (Or.inr h3) with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
  · rintro (h1 | h1 | h3)
    · rcases vu.mp (Or.inl h1) with ⟨h, h2⟩ | h
      · exact Or.inl ⟨toLive h, h2⟩
      · exact Or.inr h
    · rcases vu.mp (Or.inr h1) with ⟨h, h2⟩ | h
      · exact Or.inl ⟨toLive h, h2⟩
      · exact Or.inr h
    · exact Or.inl ⟨(R.live x).mpr (Or.inr (Or.inr h3)), hcons h3⟩


/-- The view relation after an instruction that keeps the labels, moves to `pc + 1`, pops `k` stack
entries and pushes the entries of `stk'` beyond `n - k`, and changes locals at most at `J`. -/
theorem straight_rel (X : Ctx) {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S fee k : Nat}
    {live : Msg → Prop} (R : RelW X E s f tps tpl t pc S live)
    (hk : k ≤ s.stack.size) (stk' locs' : Array Val) (J : Option Nat)
    (keep : ∀ i, i < s.stack.size - k → stk'[i]? = s.stack[i]?) (hsz : s.stack.size - k ≤ stk'.size)
    (hnum : ∀ i, i < stk'.size → isNum (stk'[i]?.getD default))
    (lsz : locs'.size = f.locals.size) (lkeep : ∀ j, some j ≠ J → locs'[j]? = f.locals[j]?)
    (hJ : ∀ j, J = some j → j < f.locals.size)
    (lnum : ∀ j, j < locs'.size → isNum (locs'[j]?.getD default))
    (hnext : pc + 1 < X.pf.code.size)
    (hL : ∃ ls, X.ck.labels[pc + 1]? = some ls ∧ f.labels = shiftLabels E.sb ls)
    (hsb : E.sb ≤ stk'.size) (hH : X.ck.heights[pc + 1]? = some (stk'.size - E.sb))
    (hgs : X.R * (S + fee) ≤ X.g0)
    (s' : St) (hs'stk : s'.stack = stk') (hs'fr : s'.frames = { f with pc := pc + 1, locals := locs' } :: E.rest)
    (hs'g : s'.gas.g = s.gas.g - X.R * fee) (hs'pg : s'.pages = s.pages) :
    RelW X E s' { f with pc := pc + 1, locals := locs' }
      (fun i => if i < s.stack.size - k then tps i else t) (fun j => if some j = J then t else tpl j)
      (t + 1) (pc + 1) (S + fee)
      (stepLive live
        (((List.range k).map fun d => enc 0 (s.stack.size - k + d)
            (s.stack[s.stack.size - k + d]?.getD default) (tps (s.stack.size - k + d))) ++
          J.toList.map (fun j => enc E.lsp j (f.locals[j]?.getD default) (tpl j)))
        (((List.range (stk'.size - (s.stack.size - k))).map fun d =>
            enc 0 (s.stack.size - k + d) (stk'[s.stack.size - k + d]?.getD default) t) ++
          J.toList.map (fun j => enc E.lsp j (locs'[j]?.getD default) t))) where
  frames := hs'fr
  fn := R.fn
  pcEq := rfl
  pcLt := hnext
  labels := hL
  base := R.base
  sbLe := by rw [hs'stk]; exact hsb
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
  envSep := R.envSep
  entry := R.entry
  sbLt := R.sbLt
  cidLt := R.cidLt
  heap := R.heap.mono hs'pg (by omega)
  live := by
    intro x
    rw [hs'stk]
    exact straight_live X R hk stk' locs' J keep hsz lsz lkeep hJ x

end WasmBase
