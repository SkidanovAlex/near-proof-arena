import WasmBase.StepOps
/-!
# WasmBase.StepOps2 — generic straight-line step, and the remaining instruction classes
-/
namespace WasmBase
open NearSpecV3.Wasm
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

/-- A live stack message at slot `n - d` decodes to that stack entry. -/
theorem RelW.stack_dec {X : Ctx} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} (R : RelW X s f tps tpl t pc S live) {m : Msg} (hm : live m)
    {i : Nat} (hs : m.space = 0) (hi : m.slot = i) (hlt : i < s.stack.size) :
    m = enc 0 i (s.stack[i]?.getD default) (tps i) ∧ m.ok ∧
      m.val = vNum (s.stack[i]?.getD default) ∧ m.toVal = s.stack[i]?.getD default := by
  have e := R.stack_msg hm hs (by omega)
  rw [hi] at e
  have n := R.numS i hlt
  refine ⟨e, by rw [e]; exact enc_ok n _ _ _, by rw [e]; exact enc_val n _ _ _, by rw [e]; exact enc_toVal n _ _ _⟩

theorem RelW.local_dec {X : Ctx} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} (R : RelW X s f tps tpl t pc S live) {m : Msg} (hm : live m)
    {j : Nat} (hs : m.space = 1) (hj : m.slot = j) (hlt : j < f.locals.size) :
    m = enc 1 j (f.locals[j]?.getD default) (tpl j) ∧ m.ok ∧
      m.val = vNum (f.locals[j]?.getD default) ∧ m.toVal = f.locals[j]?.getD default := by
  have e := R.local_msg hm hs (by omega)
  rw [hj] at e
  have n := R.numL j hlt
  refine ⟨e, by rw [e]; exact enc_ok n _ _ _, by rw [e]; exact enc_val n _ _ _, by rw [e]; exact enc_toVal n _ _ _⟩

/-- **Generic straight-line step**: charge, an `exec` that leaves the labels and moves to `pc + 1`,
and the channel view update with the event's consumed/produced messages. -/
theorem step_straight (X : Ctx) {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} (R : RelW X s f tps tpl t pc S live) {ins : Instr} {fee : Nat}
    (hins : X.pf.code[pc]? = some ins) (hfee : feeUnits X.cfg X.pf.gas[pc]? = some fee)
    (hg : X.R * (S + fee) ≤ X.g0) (hg64 : X.g0 < 2 ^ 64)
    (k : Nat) (hk : k ≤ s.stack.size) (stk' locs' : Array Val) (J : Option Nat)
    (keep : ∀ i, i < s.stack.size - k → stk'[i]? = s.stack[i]?) (hsz : s.stack.size - k ≤ stk'.size)
    (hnum : ∀ i, i < stk'.size → isNum (stk'[i]?.getD default))
    (lsz : locs'.size = f.locals.size) (lkeep : ∀ j, some j ≠ J → locs'[j]? = f.locals[j]?)
    (hJ : ∀ j, J = some j → j < f.locals.size)
    (lnum : ∀ j, j < locs'.size → isNum (locs'[j]?.getD default))
    (hnext : pc + 1 < X.pf.code.size) (hL1 : X.ck.labels[pc + 1]? = some f.labels)
    (hH1 : X.ck.heights[pc + 1]? = some stk'.size)
    (hexec : exec X.cfg X.p { s with gas := { s.gas with g := s.gas.g - X.R * fee } } f X.pf ins =
      .cont { s with gas := { s.gas with g := s.gas.g - X.R * fee }, stack := stk',
                     frames := [{ f with pc := pc + 1, locals := locs' }] })
    (cons prod : List Msg)
    (hc : ∀ x, x ∈ ((List.range k).map fun d => enc 0 (s.stack.size - k + d)
            (s.stack[s.stack.size - k + d]?.getD default) (tps (s.stack.size - k + d))) ++
          J.toList.map (fun j => enc 1 j (f.locals[j]?.getD default) (tpl j)) ↔ x ∈ cons)
    (hp : ∀ x, x ∈ ((List.range (stk'.size - (s.stack.size - k))).map fun d =>
            enc 0 (s.stack.size - k + d) (stk'[s.stack.size - k + d]?.getD default) t) ++
          J.toList.map (fun j => enc 1 j (locs'[j]?.getD default) t) ↔ x ∈ prod) :
    ∃ s', step X.cfg X.p s = .cont s' ∧ Rel X s' (t + 1) (pc + 1) (S + fee) (stepLive live cons prod) := by
  refine ⟨_, by rw [step_eq_exec X R hins hfee hg hg64, hexec], ?_⟩
  have SR := straight_rel X R hk stk' locs' J keep hsz hnum lsz lkeep hJ lnum hnext hL1 hH1 hg
    { s with gas := { s.gas with g := s.gas.g - X.R * fee }, stack := stk',
             frames := [{ f with pc := pc + 1, locals := locs' }] } rfl rfl rfl
  exact Rel_of_RelW_congr SR (stepLive_congr hc hp)

/-- `setFrame` on a one-frame state. -/
theorem setFrame_one {s : St} {f : Frame} (h : s.frames = [f]) (f' : Frame) :
    setFrame s f' = { s with frames := [f'] } := by
  simp [setFrame, h]

/-! ## Verification facts for straight instructions -/

theorem verify_straight (X : Ctx) {pc : Nat} {ins : Instr} {ls : List Label} {h pops pushes : Nat}
    (hpc : pc < X.pf.code.size) (hins : X.pf.code[pc]? = some ins) (hL : X.ck.labels[pc]? = some ls)
    (hH : X.ck.heights[pc]? = some h) (hk : kindOf ls ins = some (.straight pops pushes))
    (hnc : ∀ bt, ins ≠ .block bt) (hnl : ins ≠ .loop none) (hne : ins ≠ .end_) (hnr : ins ≠ .ret)
    (hnb : ∀ l, ins ≠ .br l) (hnbi : ∀ l, ins ≠ .brIf l) :
    pops ≤ h ∧ pc + 1 < X.pf.code.size ∧ X.ck.labels[pc + 1]? = some ls ∧
      X.ck.heights[pc + 1]? = some (h - pops + pushes) := by
  have hv := X.facts.verify pc hpc
  have e : verifyAt X.pf X.ck.labels X.ck.heights pc =
      (decide (pops ≤ h) && (decide (pc + 1 < X.pf.code.size) && decide (X.ck.labels[pc + 1]? = some ls) &&
        decide (X.ck.heights[pc + 1]? = some (h - pops + pushes)))) := by
    unfold verifyAt
    rw [hins, hL, hH]
    cases ins with
    | block bt => exact absurd rfl (hnc bt)
    | loop bt => cases bt with
      | none => exact absurd rfl hnl
      | some _ => simp [kindOf] at hk
    | end_ => exact absurd rfl hne
    | ret => exact absurd rfl hnr
    | br l => exact absurd rfl (hnb l)
    | brIf l => exact absurd rfl (hnbi l)
    | _ => simp only [hk]
  rw [e] at hv
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
  exact ⟨hv.1, hv.2.1.1, hv.2.1.2, hv.2.2⟩

/-! ## const, drop -/

theorem enc_eq_of_fields {m : Msg} {sp sl : Nat} {v : Val} {tp : Nat}
    (h1 : m.space = sp) (h2 : m.slot = sl) (h3 : m.tag = vTag v) (h4 : m.l0 = vNum v % 65536)
    (h5 : m.l1 = vNum v / 65536 % 65536) (h6 : m.l2 = vNum v / 2 ^ 32 % 65536)
    (h7 : m.l3 = vNum v / 2 ^ 48 % 65536) (h8 : m.tp = tp) : m = enc sp sl v tp := by
  cases m; simp_all [enc]

theorem step_const (X : Ctx) {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} (R : RelW X s f tps tpl t pc S live) {ins : Instr} {v : Val} {fee : Nat}
    (hiv : (∃ x, ins = .i32Const x ∧ v = .i32 x) ∨ (∃ x, ins = .i64Const x ∧ v = .i64 x))
    (hins : X.pf.code[pc]? = some ins)
    (hfee : feeUnits X.cfg X.pf.gas[pc]? = some fee) (hg : X.R * (S + fee) ≤ X.g0) (hg64 : X.g0 < 2 ^ 64)
    (mr : Msg) (hmr : mr = enc 0 s.stack.size v t) :
    ∃ s', step X.cfg X.p s = .cont s' ∧ Rel X s' (t + 1) (pc + 1) (S + fee) (stepLive live [] [mr]) := by
  have hL := R.labels; have hH := R.height
  have hnum : isNum v := by rcases hiv with ⟨x, -, rfl⟩ | ⟨x, -, rfl⟩ <;> trivial
  have hk : kindOf f.labels ins = some (.straight 0 1) := by
    rcases hiv with ⟨x, rfl, -⟩ | ⟨x, rfl, -⟩ <;> rfl
  obtain ⟨-, hnext, hL1, hH1⟩ := verify_straight X R.pcLt hins hL hH hk
    (by intro bt; rcases hiv with ⟨x, rfl, -⟩ | ⟨x, rfl, -⟩ <;> simp)
    (by rcases hiv with ⟨x, rfl, -⟩ | ⟨x, rfl, -⟩ <;> simp) (by rcases hiv with ⟨x, rfl, -⟩ | ⟨x, rfl, -⟩ <;> simp)
    (by rcases hiv with ⟨x, rfl, -⟩ | ⟨x, rfl, -⟩ <;> simp)
    (by intro l; rcases hiv with ⟨x, rfl, -⟩ | ⟨x, rfl, -⟩ <;> simp)
    (by intro l; rcases hiv with ⟨x, rfl, -⟩ | ⟨x, rfl, -⟩ <;> simp)
  have hsz : (s.stack.push v).size = s.stack.size - 0 + 1 := by simp
  apply step_straight X R hins hfee hg hg64 0 (Nat.zero_le _) (s.stack.push v) f.locals none
    (by intro i hi; simp only [Array.getElem?_push]; rw [if_neg (by omega)]) (by simp)
    (by intro i hi; simp only [Array.size_push] at hi; simp only [Array.getElem?_push]
        by_cases h : i = s.stack.size
        · rw [if_pos h]; exact hnum
        · rw [if_neg h]; exact R.numS i (by omega))
    rfl (fun _ _ => rfl) (by simp) R.numL hnext hL1 (by rw [hsz]; exact hH1)
  · rcases hiv with ⟨x, rfl, rfl⟩ | ⟨x, rfl, rfl⟩ <;> simp [exec, pushV, setFrame, R.frames, R.pcEq]
  · intro x; simp
  · intro x
    simp only [List.mem_append, List.mem_map, List.mem_range, Option.toList_none, List.not_mem_nil,
      or_false, List.mem_cons, List.mem_nil_iff, false_and, exists_false, Array.size_push, Nat.sub_zero,
      Nat.add_sub_cancel_left]
    constructor
    · rintro ⟨d, hd, rfl⟩
      have : d = 0 := by omega
      subst this; rw [hmr]; simp [Array.getElem?_push]
    · rintro rfl; exact ⟨0, by omega, by rw [hmr]; simp [Array.getElem?_push]⟩

theorem step_drop (X : Ctx) {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} (R : RelW X s f tps tpl t pc S live) {fee : Nat}
    (hins : X.pf.code[pc]? = some .drop)
    (hfee : feeUnits X.cfg X.pf.gas[pc]? = some fee) (hg : X.R * (S + fee) ≤ X.g0) (hg64 : X.g0 < 2 ^ 64)
    (ma : Msg) (hma : live ma) (sa : ma.space = 0 ∧ ma.slot = s.stack.size - 1) :
    ∃ s', step X.cfg X.p s = .cont s' ∧ Rel X s' (t + 1) (pc + 1) (S + fee) (stepLive live [ma] []) := by
  have hL := R.labels; have hH := R.height
  obtain ⟨h1, hnext, hL1, hH1⟩ := verify_straight X R.pcLt hins hL hH (pops := 1) (pushes := 0) rfl
    (by intro bt; simp) (by simp) (by simp) (by simp) (by intro l; simp) (by intro l; simp)
  obtain ⟨ea, -, -, -⟩ := R.stack_dec hma sa.1 sa.2 (by omega)
  have hsz : s.stack.pop.size = s.stack.size - 1 + 0 := by simp
  apply step_straight X R hins hfee hg hg64 1 h1 s.stack.pop f.locals none
    (by intro i hi; simp only [Array.getElem?_pop]; rw [if_pos (by omega)]) (by simp)
    (by intro i hi; simp only [Array.size_pop] at hi; simp only [Array.getElem?_pop]
        rw [if_pos (by omega)]; exact R.numS i (by omega))
    rfl (fun _ _ => rfl) (by simp) R.numL hnext hL1 (by rw [hsz]; exact hH1)
  · simp [exec, popV, setFrame, R.frames, R.pcEq]
  · intro x
    simp only [List.mem_append, List.mem_map, List.mem_range, Option.toList_none, List.not_mem_nil,
      or_false, List.mem_cons, List.mem_nil_iff, false_and, exists_false]
    constructor
    · rintro ⟨d, hd, rfl⟩
      have : d = 0 := by omega
      subst this; rw [ea, Nat.add_zero]
    · rintro rfl; exact ⟨0, by omega, by rw [ea, Nat.add_zero]⟩
  · intro x
    simp only [List.mem_append, List.mem_map, List.mem_range, Option.toList_none, List.not_mem_nil,
      or_false, false_and, exists_false, Array.size_pop, List.mem_nil_iff, iff_false]
    rintro ⟨d, hd, _⟩; omega

end WasmBase
