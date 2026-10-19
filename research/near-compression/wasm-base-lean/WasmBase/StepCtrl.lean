import WasmBase.StepOps2
/-!
# WasmBase.StepCtrl — structured control: block, loop, end, br, br_if, return

Labels are static (`CheckOut.labels`); under the no-discard condition (D3) branches leave the operand
stack unchanged, so the AIR's CTRL row only moves the pc (and pops the `br_if` condition).
-/
namespace WasmBase
open NearSpecV3.Wasm
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

/-- Relation after a control instruction: stack `popK k`, new pc and labels, locals unchanged. -/
theorem ctrl_rel (X : Ctx) {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S fee k : Nat}
    {live : Msg → Prop} (R : RelW X s f tps tpl t pc S live) (hk : k ≤ s.stack.size)
    (pc' : Nat) (ls' : List Label)
    (hnext : pc' < X.pf.code.size) (hL : X.ck.labels[pc']? = some ls')
    (hH : X.ck.heights[pc']? = some (s.stack.size - k))
    (hgs : X.R * (S + fee) ≤ X.g0)
    (s' : St) (hs'stk : s'.stack = popK s.stack k) (hs'fr : s'.frames = [{ f with pc := pc', labels := ls' }])
    (hs'g : s'.gas.g = s.gas.g - X.R * fee) :
    RelW X s' { f with pc := pc', labels := ls' }
      (fun i => if i < s.stack.size - k then tps i else t) (fun j => if some j = none then t else tpl j)
      (t + 1) pc' (S + fee)
      (stepLive live
        (((List.range k).map fun d => enc 0 (s.stack.size - k + d)
            (s.stack[s.stack.size - k + d]?.getD default) (tps (s.stack.size - k + d))) ++
          (none : Option Nat).toList.map (fun j => enc 1 j (f.locals[j]?.getD default) (tpl j)))
        (((List.range ((popK s.stack k).size - (s.stack.size - k))).map fun d =>
            enc 0 (s.stack.size - k + d) ((popK s.stack k)[s.stack.size - k + d]?.getD default) t) ++
          (none : Option Nat).toList.map (fun j => enc 1 j (f.locals[j]?.getD default) t))) where
  frames := hs'fr
  fn := R.fn
  pcEq := rfl
  pcLt := hnext
  labels := hL
  base := R.base
  height := by rw [hs'stk, popK_size]; exact hH
  nloc := R.nloc
  gas := by
    have hg := R.gas
    have : X.R * (S + fee) = X.R * S + X.R * fee := Nat.mul_add _ _ _
    rw [hs'g]; omega
  numS := by
    rw [hs'stk]; intro i hi; rw [popK_size] at hi; rw [popK_get _ _ _ hi]; exact R.numS i (by omega)
  numL := R.numL
  tpsLt := by
    intro i hi
    show (if i < s.stack.size - k then tps i else t) < t + 1
    split
    · have := R.tpsLt i (by omega); omega
    · omega
  tplLt := by
    intro j hj
    show (if some j = none then t else tpl j) < t + 1
    simp only [reduceCtorEq, ite_false]
    have := R.tplLt j hj; omega
  live := by
    intro x
    rw [hs'stk]
    simp only [stepLive]
    rw [view_update none hk (popK_get s.stack k) (by rw [popK_size]; exact Nat.le_refl _) rfl (fun _ _ => rfl)
      (fun j hj => by cases hj) R.tpsLt R.tplLt x]
    constructor
    · rintro (⟨h1, h2⟩ | h3)
      · exact Or.inl ⟨(R.live x).mp h1, h2⟩
      · exact Or.inr h3
    · rintro (⟨h1, h2⟩ | h3)
      · exact Or.inl ⟨(R.live x).mpr h1, h2⟩
      · exact Or.inr h3

/-- Control step with nothing popped (block, loop, nested end, br). -/
theorem step_ctrl0 (X : Ctx) {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} (R : RelW X s f tps tpl t pc S live) {ins : Instr} {fee : Nat}
    (hins : X.pf.code[pc]? = some ins) (hfee : feeUnits X.cfg X.pf.gas[pc]? = some fee)
    (hg : X.R * (S + fee) ≤ X.g0) (hg64 : X.g0 < 2 ^ 64) (pc' : Nat) (ls' : List Label)
    (hnext : pc' < X.pf.code.size) (hL : X.ck.labels[pc']? = some ls')
    (hH : X.ck.heights[pc']? = some s.stack.size)
    (hexec : exec X.cfg X.p { s with gas := { s.gas with g := s.gas.g - X.R * fee } } f X.pf ins =
      .cont { s with gas := { s.gas with g := s.gas.g - X.R * fee },
                     frames := [{ f with pc := pc', labels := ls' }] }) :
    ∃ s', step X.cfg X.p s = .cont s' ∧ Rel X s' (t + 1) pc' (S + fee) (stepLive live [] []) := by
  refine ⟨_, by rw [step_eq_exec X R hins hfee hg hg64, hexec], ?_⟩
  have CR := ctrl_rel X R (k := 0) (fee := fee) (Nat.zero_le _) pc' ls' hnext hL (by simpa using hH) hg
    { s with gas := { s.gas with g := s.gas.g - X.R * fee }, frames := [{ f with pc := pc', labels := ls' }] }
    rfl rfl rfl
  refine Rel_of_RelW_congr CR (stepLive_congr ?_ ?_)
  · intro x; simp
  · intro x; simp [popK_size]

/-- `doBr` to a non-function label under no-discard leaves the stack unchanged. -/
theorem stack_nodiscard (a : Array Val) (h ar : Nat) (hn : h + ar = a.size) :
    a.extract 0 h ++ a.extract (a.size - ar) a.size = a := by
  have : a.size - ar = h := by omega
  rw [this, Array.extract_append_extract]
  simp [Nat.max_def]
  grind

theorem doBr_label (p : Prepared) (s : St) (f : Frame) (l : Nat) (lab : Label)
    (hl : l + 1 < f.labels.length) (hlab : f.labels[l]? = some lab)
    (hn : lab.height + lab.arity = s.stack.size) :
    doBr p s f l = .cont (setFrame s { f with pc := lab.target, labels := (if lab.isLoop then f.labels.drop l else f.labels.drop (l + 1)) }) := by
  unfold doBr
  rw [if_neg (by omega), hlab]
  simp only
  rw [stack_nodiscard s.stack lab.height lab.arity hn]

/-- `doReturn` from the only frame under no-discard leaves the stack unchanged. -/
theorem doReturn_one (X : Ctx) (s : St) (f : Frame) (hfr : s.frames = [f]) (hfn : f.fn = X.fn)
    (hb : f.base = 0) (har : s.stack.size = X.pf.type.results.size) :
    doReturn X.p s = .fin { s with stack := s.stack, frames := [], stackRem := s.stackRem + X.pf.stackCharge } := by
  unfold doReturn
  rw [hfr]
  simp only
  rw [hfn, X.hpf]
  simp only [hb, List.isEmpty_nil, ite_true]
  rw [← har, stack_nodiscard s.stack 0 s.stack.size (by omega)]

/-! ## block, loop, nested end, br -/

theorem step_block (X : Ctx) {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} (R : RelW X s f tps tpl t pc S live) {bt : BT} {fee : Nat}
    (hins : X.pf.code[pc]? = some (.block bt)) (hfee : feeUnits X.cfg X.pf.gas[pc]? = some fee)
    (hg : X.R * (S + fee) ≤ X.g0) (hg64 : X.g0 < 2 ^ 64) :
    ∃ s', step X.cfg X.p s = .cont s' ∧ Rel X s' (t + 1) (pc + 1) (S + fee) (stepLive live [] []) := by
  have hv := X.facts.verify pc R.pcLt
  unfold verifyAt at hv
  rw [hins, R.labels, R.height] at hv
  simp only at hv
  cases he : X.pf.endOf[pc]? with
  | none => simp [he] at hv
  | some e =>
    simp only [he, Bool.and_eq_true, decide_eq_true_eq] at hv
    obtain ⟨⟨hnext, hL1⟩, hH1⟩ := hv
    apply step_ctrl0 X R hins hfee hg hg64 (pc + 1) _ hnext hL1 hH1
    simp only [exec, R.pcEq, he, setFrame, R.frames]

theorem step_loop (X : Ctx) {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} (R : RelW X s f tps tpl t pc S live) {fee : Nat}
    (hins : X.pf.code[pc]? = some (.loop none)) (hfee : feeUnits X.cfg X.pf.gas[pc]? = some fee)
    (hg : X.R * (S + fee) ≤ X.g0) (hg64 : X.g0 < 2 ^ 64) :
    ∃ s', step X.cfg X.p s = .cont s' ∧ Rel X s' (t + 1) (pc + 1) (S + fee) (stepLive live [] []) := by
  have hv := X.facts.verify pc R.pcLt
  unfold verifyAt at hv
  rw [hins, R.labels, R.height] at hv
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
  obtain ⟨⟨hnext, hL1⟩, hH1⟩ := hv
  apply step_ctrl0 X R hins hfee hg hg64 (pc + 1) _ hnext hL1 hH1
  simp only [exec, R.pcEq, setFrame, R.frames]

theorem step_end_nested (X : Ctx) {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} (R : RelW X s f tps tpl t pc S live) {fee : Nat} {lab lab' : Label}
    {rest : List Label} (hls : f.labels = lab :: lab' :: rest)
    (hins : X.pf.code[pc]? = some .end_) (hfee : feeUnits X.cfg X.pf.gas[pc]? = some fee)
    (hg : X.R * (S + fee) ≤ X.g0) (hg64 : X.g0 < 2 ^ 64) :
    ∃ s', step X.cfg X.p s = .cont s' ∧ Rel X s' (t + 1) (pc + 1) (S + fee) (stepLive live [] []) := by
  have hv := X.facts.verify pc R.pcLt
  unfold verifyAt at hv
  rw [hins, R.labels, R.height, hls] at hv
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
  obtain ⟨⟨hnext, hL1⟩, hH1⟩ := hv
  apply step_ctrl0 X R hins hfee hg hg64 (pc + 1) _ hnext hL1 hH1
  simp only [exec, hls, setFrame, R.frames, R.pcEq]

theorem step_br (X : Ctx) {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} (R : RelW X s f tps tpl t pc S live) {l fee : Nat} {lab : Label}
    (hl : l + 1 < f.labels.length) (hlab : f.labels[l]? = some lab)
    (hins : X.pf.code[pc]? = some (.br l)) (hfee : feeUnits X.cfg X.pf.gas[pc]? = some fee)
    (hg : X.R * (S + fee) ≤ X.g0) (hg64 : X.g0 < 2 ^ 64) :
    ∃ s', step X.cfg X.p s = .cont s' ∧ Rel X s' (t + 1) lab.target (S + fee) (stepLive live [] []) := by
  have hv := X.facts.verify pc R.pcLt
  unfold verifyAt at hv
  rw [hins, R.labels, R.height] at hv
  simp only [show ¬ (l + 1 ≥ f.labels.length) by omega, ite_false, hlab, Bool.and_eq_true,
    decide_eq_true_eq] at hv
  obtain ⟨hn, ⟨hnext, hL1⟩, hH1⟩ := hv
  apply step_ctrl0 X R hins hfee hg hg64 lab.target _ hnext hL1 hH1
  simp only [exec]
  rw [doBr_label X.p { s with gas := { s.gas with g := s.gas.g - X.R * fee } } f l lab hl hlab hn.symm]
  simp only [setFrame, R.frames]

/-! ## br_if -/

theorem step_brIf (X : Ctx) {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} (R : RelW X s f tps tpl t pc S live) {l fee : Nat} {lab : Label}
    (hl : l + 1 < f.labels.length) (hlab : f.labels[l]? = some lab)
    (hins : X.pf.code[pc]? = some (.brIf l)) (hfee : feeUnits X.cfg X.pf.gas[pc]? = some fee)
    (hg : X.R * (S + fee) ≤ X.g0) (hg64 : X.g0 < 2 ^ 64)
    (mc : Msg) (hmc : live mc) (sc : mc.space = 0 ∧ mc.slot = s.stack.size - 1) :
    ∃ s', step X.cfg X.p s = .cont s' ∧
      Rel X s' (t + 1) (if mc.val = 0 then pc + 1 else lab.target) (S + fee) (stepLive live [mc] []) := by
  have hv := X.facts.verify pc R.pcLt
  unfold verifyAt at hv
  rw [hins, R.labels, R.height] at hv
  simp only [show ¬ (l + 1 ≥ f.labels.length) by omega, ite_false, hlab, Bool.and_eq_true,
    decide_eq_true_eq] at hv
  obtain ⟨⟨h1, ⟨hnext, hL1⟩, hH1⟩, hn, ⟨hnextT, hLT⟩, hHT⟩ := hv
  obtain ⟨ec, okc, vc, -⟩ := R.stack_dec hmc sc.1 sc.2 (by omega)
  have hpop : (popN { s with gas := { s.gas with g := s.gas.g - X.R * fee } }).1 = mc.val := by
    rw [popN_eq, vc]; simp only; rw [back_getD _ (by omega)]
  have hb' : vNum (s.stack.back?.getD (.i32 0)) = mc.val := by rw [back_getD _ (by omega), vc]
  -- both outcomes pop the condition (k = 1) and change only pc / labels
  have key : ∀ (pc' : Nat) (ls' : List Label), pc' < X.pf.code.size → X.ck.labels[pc']? = some ls' →
      X.ck.heights[pc']? = some (s.stack.size - 1) →
      exec X.cfg X.p { s with gas := { s.gas with g := s.gas.g - X.R * fee } } f X.pf (.brIf l) =
        .cont { s with gas := { s.gas with g := s.gas.g - X.R * fee }, stack := popK s.stack 1,
                       frames := [{ f with pc := pc', labels := ls' }] } →
      ∃ s', step X.cfg X.p s = .cont s' ∧ Rel X s' (t + 1) pc' (S + fee) (stepLive live [mc] []) := by
    intro pc' ls' hn' hL' hH' hexec
    refine ⟨_, by rw [step_eq_exec X R hins hfee hg hg64, hexec], ?_⟩
    have CR := ctrl_rel X R (k := 1) (fee := fee) (by omega) pc' ls' hn' hL' hH' hg
      { s with gas := { s.gas with g := s.gas.g - X.R * fee }, stack := popK s.stack 1,
               frames := [{ f with pc := pc', labels := ls' }] } rfl rfl rfl
    refine Rel_of_RelW_congr CR (stepLive_congr ?_ ?_)
    · intro x
      simp only [List.mem_append, List.mem_map, List.mem_range, Option.toList_none, List.not_mem_nil,
        or_false, List.mem_cons, List.mem_nil_iff, false_and, exists_false]
      constructor
      · rintro ⟨d, hd, rfl⟩
        have : d = 0 := by omega
        subst this; rw [ec, Nat.add_zero]
      · rintro rfl; exact ⟨0, by omega, by rw [ec, Nat.add_zero]⟩
    · intro x
      simp only [List.mem_append, List.mem_map, List.mem_range, Option.toList_none, List.not_mem_nil,
        or_false, false_and, exists_false, popK_size, List.mem_nil_iff, iff_false]
      rintro ⟨d, hd, _⟩; omega
  by_cases h0 : mc.val = 0
  · rw [if_pos h0]
    apply key (pc + 1) f.labels hnext hL1 (by rw [hH1])
    simp only [exec, popN_eq, hb', h0, ne_eq, not_true_eq_false, ite_false, setFrame, R.frames, R.pcEq,
      popK, Array.size_pop]
  · rw [if_neg h0]
    apply key lab.target _ hnextT hLT (by rw [hHT])
    simp only [exec, popN_eq, hb', ne_eq, h0, not_false_eq_true, ite_true]
    rw [doBr_label X.p _ f l lab hl hlab (by simp only [Array.size_pop]; omega)]
    simp only [setFrame, R.frames, popK]

/-! ## return from the function (end of body, return, br / br_if to the function label) -/

/-- The halting outcome: the spec finishes with the same operand stack. -/
def Halted (X : Ctx) (s sN : St) (fee : Nat) (stk : Array Val) : Prop :=
  sN.frames = [] ∧ sN.stack = stk ∧ sN.gas.g = s.gas.g - X.R * fee

theorem step_halt (X : Ctx) {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} (R : RelW X s f tps tpl t pc S live) {ins : Instr} {fee : Nat}
    (hins : X.pf.code[pc]? = some ins)
    (hkind : (ins = .end_ ∧ f.labels.length = 1) ∨ ins = .ret ∨ (∃ l, ins = .br l ∧ l + 1 ≥ f.labels.length))
    (hfee : feeUnits X.cfg X.pf.gas[pc]? = some fee)
    (hg : X.R * (S + fee) ≤ X.g0) (hg64 : X.g0 < 2 ^ 64) :
    ∃ sN, step X.cfg X.p s = .fin sN ∧ Halted X s sN fee s.stack := by
  have hv := X.facts.verify pc R.pcLt
  have hone : ins = .end_ → f.labels.length = 1 → ∃ lab0, f.labels = [lab0] := by
    intro _ h1; exact List.length_eq_one_iff.mp h1
  have har : s.stack.size = X.pf.type.results.size := by
    unfold verifyAt at hv
    rw [hins, R.labels, R.height] at hv
    rcases hkind with ⟨rfl, h1⟩ | rfl | ⟨l, rfl, hl⟩
    · obtain ⟨lab0, hls⟩ := hone rfl h1
      simp only [hls, decide_eq_true_eq] at hv; exact hv
    · simpa using hv
    · simp only [hl, ite_true, decide_eq_true_eq] at hv; exact hv
  rw [step_eq_exec X R hins hfee hg hg64]
  let s1 : St := { s with gas := { s.gas with g := s.gas.g - X.R * fee } }
  have hd := doReturn_one X s1 f R.frames R.fn R.base har
  refine ⟨{ s1 with stack := s1.stack, frames := [], stackRem := s1.stackRem + X.pf.stackCharge }, ?_,
    ⟨rfl, rfl, rfl⟩⟩
  rcases hkind with ⟨rfl, h1⟩ | rfl | ⟨l, rfl, hl⟩
  · obtain ⟨lab0, hls⟩ := hone rfl h1
    simp only [exec, hls]; exact hd
  · simp only [exec]; exact hd
  · simp only [exec]; unfold doBr; rw [if_pos hl]; exact hd

theorem step_haltIf (X : Ctx) {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} (R : RelW X s f tps tpl t pc S live) {l fee : Nat}
    (hl : l + 1 ≥ f.labels.length)
    (hins : X.pf.code[pc]? = some (.brIf l)) (hfee : feeUnits X.cfg X.pf.gas[pc]? = some fee)
    (hg : X.R * (S + fee) ≤ X.g0) (hg64 : X.g0 < 2 ^ 64)
    (mc : Msg) (hmc : live mc) (sc : mc.space = 0 ∧ mc.slot = s.stack.size - 1) :
    (mc.val ≠ 0 → ∃ sN, step X.cfg X.p s = .fin sN ∧ Halted X s sN fee s.stack.pop) ∧
    (mc.val = 0 → ∃ s', step X.cfg X.p s = .cont s' ∧
      Rel X s' (t + 1) (pc + 1) (S + fee) (stepLive live [mc] [])) := by
  have hv := X.facts.verify pc R.pcLt
  unfold verifyAt at hv
  rw [hins, R.labels, R.height] at hv
  simp only [hl, ite_true, Bool.and_eq_true, decide_eq_true_eq] at hv
  obtain ⟨⟨h1, ⟨hnext, hL1⟩, hH1⟩, har⟩ := hv
  obtain ⟨ec, okc, vc, -⟩ := R.stack_dec hmc sc.1 sc.2 (by omega)
  have hpop : (popN { s with gas := { s.gas with g := s.gas.g - X.R * fee } }).1 = mc.val := by
    rw [popN_eq, vc]; simp only; rw [back_getD _ (by omega)]
  have hb' : vNum (s.stack.back?.getD (.i32 0)) = mc.val := by rw [back_getD _ (by omega), vc]
  let s1 : St := { s with gas := { s.gas with g := s.gas.g - X.R * fee } }
  let s2 : St := { s1 with stack := s1.stack.pop }
  constructor
  · intro h0
    rw [step_eq_exec X R hins hfee hg hg64]
    have hd := doReturn_one X s2 f (by simp [s2, s1, R.frames]) R.fn R.base (by simp [s2, s1]; omega)
    refine ⟨{ s2 with stack := s2.stack, frames := [], stackRem := s2.stackRem + X.pf.stackCharge }, ?_,
      ⟨rfl, rfl, rfl⟩⟩
    simp only [exec, popN_eq, hb', ne_eq, h0, not_false_eq_true, ite_true]
    unfold doBr; rw [if_pos hl]; exact hd
  · intro h0
    refine ⟨{ s1 with stack := popK s.stack 1, frames := [{ f with pc := pc + 1, labels := f.labels }] }, ?_, ?_⟩
    · rw [step_eq_exec X R hins hfee hg hg64]
      simp only [exec, popN_eq, hb', h0, ne_eq, not_true_eq_false, ite_false, setFrame, R.frames, R.pcEq,
        popK, s1]
    · have CR := ctrl_rel X R (k := 1) (fee := fee) (by omega) (pc + 1) f.labels hnext hL1 (by rw [hH1]) hg
        { s1 with stack := popK s.stack 1, frames := [{ f with pc := pc + 1, labels := f.labels }] } rfl rfl rfl
      refine Rel_of_RelW_congr CR (stepLive_congr ?_ ?_)
      · intro x
        simp only [List.mem_append, List.mem_map, List.mem_range, Option.toList_none, List.not_mem_nil,
          or_false, List.mem_cons, List.mem_nil_iff, false_and, exists_false]
        constructor
        · rintro ⟨d, hd, rfl⟩
          have : d = 0 := by omega
          subst this; rw [ec, Nat.add_zero]
        · rintro rfl; exact ⟨0, by omega, by rw [ec, Nat.add_zero]⟩
      · intro x
        simp only [List.mem_append, List.mem_map, List.mem_range, Option.toList_none, List.not_mem_nil,
          or_false, false_and, exists_false, popK_size, List.mem_nil_iff, iff_false]
        rintro ⟨d, hd, _⟩; omega

end WasmBase
