import WasmBase.StepOps2
/-!
# WasmBase.StepMem — loads and stores under the simulation relation

The memory is channel space 3, one message per touched byte (`memView`, `HeapOK`).  A load consumes
the address and the `w` byte messages and produces them again (fresh time) plus the result; a store
consumes the value, the address and the `w` old byte messages and produces the new bytes.

`straight_rel_env`: `straight_rel` when the event also consumes / produces outer messages `ce` /
`pe` (other spaces), with the outer live set updated accordingly.
-/
namespace WasmBase
open NearSpecV3.Wasm
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

/-- A live message outside space 0 and the current locals space is an outer message. -/
theorem RelW.env_msg {X : Ctx} {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} (R : RelW X E s f tps tpl t pc S live) {x : Msg} (hx : live x)
    (h0 : x.space ≠ 0) (h1 : x.space ≠ E.lsp) : E.live x := by
  rcases (R.live x).mp hx with h | h | h
  · obtain ⟨i, _, rfl⟩ := mem_stackView.mp h; exact absurd rfl h0
  · obtain ⟨j, _, rfl⟩ := mem_localView.mp h; exact absurd rfl h1
  · exact h

/-- The successor relation of a straight-line instruction that also consumes the outer messages
`ce` and produces `pe` (in spaces other than 0 and the locals space). -/
theorem straight_rel_env (X : Ctx) {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S fee k : Nat}
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
    (hs'g : s'.gas.g = s.gas.g - X.R * fee)
    (ce pe : List Msg) (hce : ∀ x ∈ ce, E.live x) (hpe : ∀ x ∈ pe, x.space ≠ 0 ∧ x.space ≠ E.lsp)
    (hheap : HeapOK { E with live := stepLive E.live ce pe } s' (t + 1)) :
    RelW X { E with live := stepLive E.live ce pe } s' { f with pc := pc + 1, locals := locs' }
      (fun i => if i < s.stack.size - k then tps i else t) (fun j => if some j = J then t else tpl j)
      (t + 1) (pc + 1) (S + fee)
      (stepLive live
        ((((List.range k).map fun d => enc 0 (s.stack.size - k + d)
            (s.stack[s.stack.size - k + d]?.getD default) (tps (s.stack.size - k + d))) ++
          J.toList.map (fun j => enc E.lsp j (f.locals[j]?.getD default) (tpl j))) ++ ce)
        ((((List.range (stk'.size - (s.stack.size - k))).map fun d =>
            enc 0 (s.stack.size - k + d) (stk'[s.stack.size - k + d]?.getD default) t) ++
          J.toList.map (fun j => enc E.lsp j (locs'[j]?.getD default) t)) ++ pe)) where
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
  envSep := by
    intro x hx
    rcases hx with ⟨h, _⟩ | h
    · exact R.envSep x h
    · exact hpe x h
  entry := R.entry
  sbLt := R.sbLt
  cidLt := R.cidLt
  heap := hheap
  live := by
    intro x
    have SL := straight_live X R hk stk' locs' J keep hsz lsz lkeep hJ x
    rw [hs'stk]
    -- stack / local messages are never outer messages
    have hsep : ∀ y, (y ∈ stackView stk' (fun i => if i < s.stack.size - k then tps i else t) ∨
        y ∈ localView E.lsp locs' (fun j => if some j = J then t else tpl j)) → y.space = 0 ∨ y.space = E.lsp := by
      rintro y (h | h)
      · obtain ⟨i, _, rfl⟩ := mem_stackView.mp h; exact Or.inl rfl
      · obtain ⟨j, _, rfl⟩ := mem_localView.mp h; exact Or.inr rfl
    have hscSp : ∀ y, y ∈ (((List.range k).map fun d => enc 0 (s.stack.size - k + d)
          (s.stack[s.stack.size - k + d]?.getD default) (tps (s.stack.size - k + d))) ++
          J.toList.map (fun j => enc E.lsp j (f.locals[j]?.getD default) (tpl j))) ∨
        y ∈ (((List.range (stk'.size - (s.stack.size - k))).map fun d =>
          enc 0 (s.stack.size - k + d) (stk'[s.stack.size - k + d]?.getD default) t) ++
          J.toList.map (fun j => enc E.lsp j (locs'[j]?.getD default) t)) → y.space = 0 ∨ y.space = E.lsp := by
      intro y hy
      simp only [List.mem_append, List.mem_map, List.mem_range, Option.mem_toList] at hy
      rcases hy with (⟨d, _, rfl⟩ | ⟨j, _, rfl⟩) | (⟨d, _, rfl⟩ | ⟨j, _, rfl⟩)
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    have ceSp : ∀ y ∈ ce, y.space ≠ 0 ∧ y.space ≠ E.lsp := fun y hy => R.envSep y (hce y hy)
    simp only [stepLive, List.mem_append] at SL ⊢
    constructor
    · rintro (⟨hl, hn⟩ | hp)
      · have hn1 : ¬ (x ∈ _ ∨ x ∈ _) := fun h => hn (Or.inl h)
        have hn2 : x ∉ ce := fun h => hn (Or.inr h)
        rcases SL.mp (Or.inl ⟨hl, hn1⟩) with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl ⟨h, hn2⟩))
      · rcases hp with hp | hp
        · rcases SL.mp (Or.inr hp) with h | h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exfalso
            have := R.envSep x h
            rcases hscSp x (Or.inr (List.mem_append.mpr hp)) with e | e
            · exact this.1 e
            · exact this.2 e
        · exact Or.inr (Or.inr (Or.inr hp))
    · rintro (h | h | (⟨he, hn⟩ | hp))
      · rcases SL.mpr (Or.inl h) with ⟨hl, hn⟩ | hp
        · refine Or.inl ⟨hl, ?_⟩
          rintro (h' | h')
          · exact hn h'
          · rcases hsep x (Or.inl h) with e | e
            · exact (ceSp x h').1 e
            · exact (ceSp x h').2 e
        · exact Or.inr (Or.inl hp)
      · rcases SL.mpr (Or.inr (Or.inl h)) with ⟨hl, hn⟩ | hp
        · refine Or.inl ⟨hl, ?_⟩
          rintro (h' | h')
          · exact hn h'
          · rcases hsep x (Or.inr h) with e | e
            · exact (ceSp x h').1 e
            · exact (ceSp x h').2 e
        · exact Or.inr (Or.inl hp)
      · rcases SL.mpr (Or.inr (Or.inr he)) with ⟨hl, hn'⟩ | hp
        · refine Or.inl ⟨hl, ?_⟩
          rintro (h' | h')
          · exact hn' h'
          · exact hn h'
        · exfalso
          have := R.envSep x he
          rcases hscSp x (Or.inr (List.mem_append.mpr hp)) with e | e
          · exact this.1 e
          · exact this.2 e
      · exact Or.inr (Or.inr hp)

/-! ## The heap under a memory access -/

theorem encB_inj {a v tp a' v' tp' : Nat} (h : encB a v tp = encB a' v' tp') : a = a' ∧ v = v' ∧ tp = tp' := by
  simp only [encB, Msg.mk.injEq] at h; exact ⟨h.2.1, h.2.2.2.1, h.2.2.2.2.2.2.2⟩

@[simp] theorem encB_space (a v tp : Nat) : (encB a v tp).space = 3 := rfl
@[simp] theorem encB_slot (a v tp : Nat) : (encB a v tp).slot = a := rfl

/-- A live byte message carries the current byte of an in-bounds address. -/
theorem heap_read {E : Env} {s : St} {t a v tp : Nat} (H : HeapOK E s t) (hl : E.live (encB a v tp)) :
    (readByte s a).toNat = v ∧ a < memBytes s := by
  obtain ⟨T, tpm, -, hlt, -, hv⟩ := H.mem
  obtain ⟨a', ha', he⟩ := mem_memView.mp ((hv _ rfl).mp hl)
  obtain ⟨e1, e2, -⟩ := encB_inj he
  subst e1
  exact ⟨e2.symm, hlt a ha'⟩

/-- The heap after an access to the bytes `[ea, ea + w)`: the old byte messages are consumed, the
new ones (current bytes of `s'`, time `t`) produced; all other bytes are unchanged. -/
theorem heap_update {E : Env} {s s' : St} {t ea w : Nat} (H : HeapOK E s t) (hP' : PagesOK s')
    (hmb : memBytes s' = memBytes s)
    (hrd : ∀ a, ¬ (ea ≤ a ∧ a < ea + w) → readByte s' a = readByte s a)
    (bv tb nb : Nat → Nat) (hlive : ∀ i, i < w → E.live (encB (ea + i) (bv i) (tb i)))
    (hnew : ∀ i, i < w → (readByte s' (ea + i)).toNat = nb i) :
    HeapOK { E with live := (stepLive E.live ((List.range w).map fun i => encB (ea + i) (bv i) (tb i))
        ((List.range w).map fun i => encB (ea + i) (nb i) t)) } s' (t + 1) := by
  obtain ⟨T, tpm, hnd, hlt, htp, hv⟩ := H.mem
  -- the consumed messages are the memView entries of their addresses
  have hold : ∀ i, i < w → ea + i ∈ T ∧ bv i = (readByte s (ea + i)).toNat ∧ tb i = tpm (ea + i) := by
    intro i hi
    obtain ⟨a', ha', he⟩ := mem_memView.mp ((hv _ rfl).mp (hlive i hi))
    obtain ⟨e1, e2, e3⟩ := encB_inj he
    subst e1
    exact ⟨ha', e2, e3⟩
  refine ⟨hP', T, fun a => if ea ≤ a ∧ a < ea + w then t else tpm a, hnd,
    fun a ha => by rw [hmb]; exact hlt a ha,
    fun a ha => by
      show (if ea ≤ a ∧ a < ea + w then t else tpm a) < t + 1
      split
      · omega
      · have := htp a ha; omega, fun x hx => ?_⟩
  simp only [stepLive, List.mem_map, List.mem_range]
  constructor
  · rintro (⟨hl, hn⟩ | ⟨i, hi, rfl⟩)
    · obtain ⟨a, ha, rfl⟩ := mem_memView.mp ((hv x hx).mp hl)
      by_cases hr : ea ≤ a ∧ a < ea + w
      · exfalso; apply hn
        obtain ⟨-, e2, e3⟩ := hold (a - ea) (by omega)
        refine ⟨a - ea, by omega, ?_⟩
        rw [show ea + (a - ea) = a by omega] at e2 e3
        rw [e2, e3, show ea + (a - ea) = a by omega]
      · refine mem_memView.mpr ⟨a, ha, ?_⟩
        rw [hrd a hr, if_neg hr]
    · refine mem_memView.mpr ⟨ea + i, (hold i hi).1, ?_⟩
      rw [hnew i hi, if_pos (by omega)]
  · intro hm
    obtain ⟨a, ha, rfl⟩ := mem_memView.mp hm
    by_cases hr : ea ≤ a ∧ a < ea + w
    · right
      refine ⟨a - ea, by omega, ?_⟩
      have := hnew (a - ea) (by omega)
      rw [show ea + (a - ea) = a by omega] at this
      rw [show ea + (a - ea) = a by omega, this, if_pos hr]
    · left
      rw [hrd a hr, if_neg hr]
      refine ⟨(hv _ rfl).mpr (mem_memView.mpr ⟨a, ha, rfl⟩), ?_⟩
      rintro ⟨i, hi, he⟩
      have := congrArg Msg.slot he
      simp only [encB_slot] at this
      omega

/-! ## Loads -/

/-- The value a load pushes, from the little-endian value `v` of its bytes. -/
def loadVal (op v : Nat) : Val :=
  let v' := if (loadSpec op).2.1 then Num.extendS (if (loadSpec op).2.2 then 64 else 32) (8 * (loadSpec op).1) v else v
  if (loadSpec op).2.2 then .i64 (UInt64.ofNat v') else .i32 (UInt32.ofNat v')

theorem loadVal_num (op v : Nat) : isNum (loadVal op v) := by
  simp only [loadVal]; split <;> trivial

theorem loadSpec_w_pos (op : Nat) : 1 ≤ (loadSpec op).1 ∧ (loadSpec op).1 ≤ 8 := by
  unfold loadSpec; split <;> simp

theorem leVal_shift (f : Nat → Nat) (a w : Nat) : leVal f a w = leVal (fun i => f (a + i)) 0 w := by
  induction w with
  | zero => rfl
  | succ w ih => simp only [leVal, ih, Nat.zero_add]

theorem leVal_congr {f g : Nat → Nat} {a w : Nat} (h : ∀ i, i < w → f (a + i) = g (a + i)) :
    leVal f a w = leVal g a w := by
  induction w with
  | zero => rfl
  | succ w ih => simp only [leVal, ih (fun i hi => h i (by omega)), h w (by omega)]

theorem exec_load (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (pf : PFunc) (op al off : Nat) :
    exec cfg p s f pf (.load op al off) =
      if (popN s).1 + off + (loadSpec op).1 > memBytes (popN s).2 then .abort (popN s).2 trapMem
      else .cont (setFrame (pushV (popN s).2 (loadVal op (readLE (popN s).2 ((popN s).1 + off) (loadSpec op).1)))
        { f with pc := f.pc + 1 }) := by
  simp only [exec]
  rcases hl : loadSpec op with ⟨w, sgn, is64⟩
  simp only [loadVal, hl]
  split <;> (try rfl)
  cases is64 <;> rfl

/-- **Load.** The address is the top of the stack; the `w` byte messages at `ea + i` are live
memory messages, so they carry the current bytes and are in bounds (no trap); the result replaces
the address; the byte messages are produced again with time `t`. -/
theorem step_load (X : Ctx) {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} (R : RelW X E s f tps tpl t pc S live)
    {op al off fee : Nat} (hins : X.pf.code[pc]? = some (.load op al off)) (hop : isLoadOp op = true)
    (hoff : off < 2 ^ 32)
    (hfee : feeUnits X.cfg X.pf.gas[pc]? = some fee) (hg : X.R * (S + fee) ≤ X.g0) (hg64 : X.g0 < 2 ^ 64)
    (ma : Msg) (hma : live ma) (sa : ma.space = 0 ∧ ma.slot = s.stack.size - 1)
    (ea : Nat) (hea : ma.ok → ma.val + off = ea)
    (bv tb : Nat → Nat) (hmb : ∀ i, i < (loadSpec op).1 → live (encB (ea + i) (bv i) (tb i)))
    (mr : Msg)
    (hmr : (∀ i, i < (loadSpec op).1 → bv i < 256) →
      mr = enc 0 (s.stack.size - 1) (loadVal op (leVal bv 0 (loadSpec op).1)) t) :
    ∃ s', step X.cfg X.p s = .cont s' ∧ Rel X s' (t + 1) (pc + 1) (S + fee) E.sb E.cid
      (stepLive live (ma :: (List.range (loadSpec op).1).map fun i => encB (ea + i) (bv i) (tb i))
        (mr :: (List.range (loadSpec op).1).map fun i => encB (ea + i) (bv i) t)) := by
  have F := X.facts
  obtain ⟨ls0, hL, hfl⟩ := R.labels
  have hH := R.height
  have hsbR := R.sbLe
  obtain ⟨h1, hnext, hL1, hH1⟩ := verify_straight X R.pcLt hins hL hH (pops := 1) (pushes := 1)
    (by simp [kindOf, hop, hoff]) (by intro bt; simp) (by simp) (by simp) (by simp) (by intro l; simp)
    (by intro l; simp)
  obtain ⟨ea0, oka, va, -⟩ := R.stack_dec hma sa.1 sa.2 (by omega)
  have hea' := hea oka
  obtain ⟨w1, w8⟩ := loadSpec_w_pos op
  generalize hw : (loadSpec op).1 = w at hmb hmr w1 w8 ⊢
  -- the bytes: live outer messages, hence current bytes in bounds
  have hbyte : ∀ i, i < w → (readByte s (ea + i)).toNat = bv i ∧ ea + i < memBytes s := fun i hi =>
    heap_read R.heap (R.env_msg (hmb i hi) (by simp) (by simp [Env.lsp]; omega))
  have hbv : ∀ i, i < w → bv i < 256 := fun i hi => by
    rw [← (hbyte i hi).1]; exact (readByte s (ea + i)).toNat_lt
  have hmr' := hmr hbv
  have hinb : ea + w ≤ memBytes s := by have := (hbyte (w - 1) (by omega)).2; omega
  -- the spec step
  let s1 : St := { s with gas := { s.gas with g := s.gas.g - X.R * fee }, stack := s.stack.pop }
  let val : Val := loadVal op (leVal bv 0 w)
  have hpop : popN { s with gas := { s.gas with g := s.gas.g - X.R * fee } } = (ma.val, s1) := by
    rw [popN_eq, va, back_getD _ (by show 0 < s.stack.size; omega)]
  have hrd : readLE s1 ea w = leVal bv 0 w := by
    rw [readLE_eq, leVal_shift]
    exact leVal_congr (fun i hi => by simp only [Nat.zero_add]; exact (hbyte i hi).1)
  have hfr1 : s1.frames = f :: E.rest := R.frames
  refine ⟨setFrame (pushV s1 val) { f with pc := f.pc + 1 }, ?_, ?_⟩
  · rw [step_eq_exec X R hins hfee hg hg64, exec_load, hpop]
    simp only [hw, hea']
    have hm1 : memBytes s1 = memBytes s := rfl
    rw [if_neg (show ¬ (ea + w > memBytes s1) by omega), hrd]
  · let s2 : St := { s1 with stack := s.stack.pop.push val, frames := { f with pc := pc + 1, locals := f.locals } :: E.rest }
    have hs2 : setFrame (pushV s1 val) { f with pc := f.pc + 1 } = s2 := by
      simp only [setFrame, pushV, hfr1, R.pcEq, s2]; rfl
    rw [hs2]
    have hsz' : (s.stack.pop.push val).size = s.stack.size := by simp; omega
    have SR := straight_rel_env X R (k := 1) (fee := fee) (by omega) (s.stack.pop.push val) f.locals none
      (by intro i hi; simp only [Array.getElem?_push, Array.getElem?_pop, Array.size_pop]
          rw [if_neg (by omega), if_pos (by omega)])
      (by simp)
      (by intro i hi
          simp only [Array.getElem?_push, Array.getElem?_pop, Array.size_pop] at hi ⊢
          by_cases hi' : i = s.stack.size - 1
          · rw [if_pos hi']; exact loadVal_num _ _
          · rw [if_neg hi', if_pos (by omega)]; exact R.numS i (by omega))
      rfl (fun _ _ => rfl) (by simp) R.numL hnext ⟨ls0, hL1, hfl⟩ (by rw [hsz']; omega)
      (by rw [hsz', hH1]; congr 1; omega) hg
      s2 rfl rfl rfl
      ((List.range w).map fun i => encB (ea + i) (bv i) (tb i))
      ((List.range w).map fun i => encB (ea + i) (bv i) t)
      (fun x hx => by
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
        exact R.env_msg (hmb i (List.mem_range.mp hi)) (by simp) (by simp [Env.lsp]; omega))
      (fun x hx => by
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
        exact ⟨by simp, by simp [Env.lsp]; omega⟩)
      (heap_update (s' := s2) R.heap R.heap.pages rfl (fun a _ => rfl) bv tb bv
        (fun i hi => R.env_msg (hmb i hi) (by simp) (by simp [Env.lsp]; omega))
        (fun i hi => (hbyte i hi).1))
    have RR := Rel_of_RelW_congr SR (stepLive_congr
      (c2 := ma :: (List.range w).map fun i => encB (ea + i) (bv i) (tb i))
      (p2 := mr :: (List.range w).map fun i => encB (ea + i) (bv i) t) ?_ ?_)
    · exact RR
    · intro x
      rw [show List.range 1 = [0] from rfl]
      simp only [List.map_cons, List.map_nil, Option.toList_none, List.append_nil, List.cons_append,
        List.nil_append, Nat.add_zero, ← ea0]
    · intro x
      have e1 : (s.stack.pop.push val).size - (s.stack.size - 1) = 1 := by rw [hsz']; omega
      have hv : (s.stack.pop.push val)[s.stack.size - 1]?.getD default = val := by
        rw [show s.stack.size - 1 = s.stack.pop.size by simp, Array.getElem?_push_size]; rfl
      rw [e1, show List.range 1 = [0] from rfl]
      simp only [List.map_cons, List.map_nil, Option.toList_none, List.append_nil, List.cons_append,
        List.nil_append, Nat.add_zero, hv, hmr']
      exact Iff.rfl

/-! ## Stores -/

theorem storeWidth_pos (op : Nat) : 1 ≤ storeWidth op ∧ storeWidth op ≤ 8 := by
  unfold storeWidth; split <;> simp

theorem exec_store (cfg : NearCfg) (p : Prepared) (s : St) (f : Frame) (pf : PFunc) (op al off : Nat) :
    exec cfg p s f pf (.store op al off) =
      if (popN (popN s).2).1 + off + storeWidth op > memBytes (popN (popN s).2).2 then .abort (popN (popN s).2).2 trapMem
      else .cont (setFrame (writeLE (popN (popN s).2).2 ((popN (popN s).2).1 + off) (storeWidth op)
        ((popN s).1 % 256 ^ storeWidth op)) { f with pc := f.pc + 1 }) := by
  simp only [exec]

theorem byte_of_mod (v w i : Nat) (hi : i < w) : v % 256 ^ w / 256 ^ i % 256 = v / 256 ^ i % 256 := by
  have h1 : 256 ^ w = 256 ^ i * 256 ^ (w - i) := by rw [← Nat.pow_add]; congr 1; omega
  rw [h1, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd]
  have := Nat.pow_dvd_pow 256 (show 1 ≤ w - i by omega)
  simpa using this

/-- **Store.** The value is the top of the stack, the address below it; the `w` old byte messages
are live memory messages (current bytes, in bounds: no trap); the new byte messages carry the bytes
of the value. -/
theorem step_store (X : Ctx) {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} (R : RelW X E s f tps tpl t pc S live)
    {op al off fee : Nat} (hins : X.pf.code[pc]? = some (.store op al off)) (hop : isStoreOp op = true)
    (hoff : off < 2 ^ 32)
    (hfee : feeUnits X.cfg X.pf.gas[pc]? = some fee) (hg : X.R * (S + fee) ≤ X.g0) (hg64 : X.g0 < 2 ^ 64)
    (mv ma : Msg) (hmv : live mv) (hma : live ma)
    (sv : mv.space = 0 ∧ mv.slot = s.stack.size - 1) (sa : ma.space = 0 ∧ ma.slot = s.stack.size - 2)
    (ea : Nat) (hea : ma.ok → ma.val + off = ea)
    (bv tb nb : Nat → Nat) (hmb : ∀ i, i < storeWidth op → live (encB (ea + i) (bv i) (tb i)))
    (hnb : mv.ok → ∀ i, i < storeWidth op → nb i = mv.val / 256 ^ i % 256) :
    ∃ s', step X.cfg X.p s = .cont s' ∧ Rel X s' (t + 1) (pc + 1) (S + fee) E.sb E.cid
      (stepLive live (mv :: ma :: (List.range (storeWidth op)).map fun i => encB (ea + i) (bv i) (tb i))
        ((List.range (storeWidth op)).map fun i => encB (ea + i) (nb i) t)) := by
  have F := X.facts
  obtain ⟨ls0, hL, hfl⟩ := R.labels
  have hH := R.height
  have hsbR := R.sbLe
  obtain ⟨h2, hnext, hL1, hH1⟩ := verify_straight X R.pcLt hins hL hH (pops := 2) (pushes := 0)
    (by simp [kindOf, hop, hoff]) (by intro bt; simp) (by simp) (by simp) (by simp) (by intro l; simp)
    (by intro l; simp)
  obtain ⟨ev, okv, vv, -⟩ := R.stack_dec hmv sv.1 sv.2 (by omega)
  obtain ⟨ea0, oka, va, -⟩ := R.stack_dec hma sa.1 sa.2 (by omega)
  have hea' := hea oka
  have hnb' := hnb okv
  obtain ⟨w1, w8⟩ := storeWidth_pos op
  generalize hw : storeWidth op = w at hmb hnb' w1 w8 ⊢
  have hbyte : ∀ i, i < w → (readByte s (ea + i)).toNat = bv i ∧ ea + i < memBytes s := fun i hi =>
    heap_read R.heap (R.env_msg (hmb i hi) (by simp) (by simp [Env.lsp]; omega))
  have hinb : ea + w ≤ memBytes s := by have := (hbyte (w - 1) (by omega)).2; omega
  -- the spec step
  let s1 : St := { s with gas := { s.gas with g := s.gas.g - X.R * fee }, stack := s.stack.pop.pop }
  have hpop1 : popN { s with gas := { s.gas with g := s.gas.g - X.R * fee } } =
      (mv.val, { s with gas := { s.gas with g := s.gas.g - X.R * fee }, stack := s.stack.pop }) := by
    rw [popN_eq, vv, back_getD _ (by show 0 < s.stack.size; omega)]
  have hpop2 : popN { s with gas := { s.gas with g := s.gas.g - X.R * fee }, stack := s.stack.pop } = (ma.val, s1) := by
    rw [popN_eq, va, back_getD _ (by show 0 < s.stack.pop.size; simp; omega)]
    simp only [Array.size_pop, Array.getElem?_pop]
    rw [if_pos (by omega), show s.stack.size - 1 - 1 = s.stack.size - 2 by omega]
  have hP1 : PagesOK s1 := R.heap.pages
  have hm1 : memBytes s1 = memBytes s := rfl
  obtain ⟨⟨pg, hpg⟩, hsz, hok, hrdW⟩ := writeLE_facts hP1 (a := ea) (w := w) (by omega) (mv.val % 256 ^ w)
  let s2 : St := { s1 with pages := pg, frames := { f with pc := pc + 1, locals := f.locals } :: E.rest }
  have hfr1 : s1.frames = f :: E.rest := R.frames
  have hs2 : setFrame (writeLE s1 ea w (mv.val % 256 ^ w)) { f with pc := f.pc + 1 } = s2 := by
    rw [hpg]; simp only [setFrame, hfr1, R.pcEq, s2]
  refine ⟨s2, ?_, ?_⟩
  · rw [step_eq_exec X R hins hfee hg hg64, exec_store, hpop1, hpop2]
    simp only [hw, hea']
    rw [if_neg (show ¬ (ea + w > memBytes s1) by omega), hs2]
  · have hsz' : s.stack.pop.pop.size = s.stack.size - 2 := by simp; omega
    have hpg2 : s2.pages = (writeLE s1 ea w (mv.val % 256 ^ w)).pages := by rw [hpg]
    have SR := straight_rel_env X R (k := 2) (fee := fee) (by omega) s.stack.pop.pop f.locals none
      (by intro i hi; simp only [Array.getElem?_pop, Array.size_pop]
          rw [if_pos (by omega), if_pos (by omega)])
      (by simp; omega)
      (by intro i hi
          simp only [Array.getElem?_pop, Array.size_pop] at hi ⊢
          rw [if_pos (by omega), if_pos (by omega)]; exact R.numS i (by omega))
      rfl (fun _ _ => rfl) (by simp) R.numL hnext ⟨ls0, hL1, hfl⟩ (by rw [hsz']; omega)
      (by rw [hsz', hH1]; congr 1; omega) hg
      s2 rfl rfl rfl
      ((List.range w).map fun i => encB (ea + i) (bv i) (tb i))
      ((List.range w).map fun i => encB (ea + i) (nb i) t)
      (fun x hx => by
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
        exact R.env_msg (hmb i (List.mem_range.mp hi)) (by simp) (by simp [Env.lsp]; omega))
      (fun x hx => by
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
        exact ⟨by simp, by simp [Env.lsp]; omega⟩)
      (heap_update (s' := s2) R.heap
        (fun i h => by have := hok i (by rw [← hpg2]; exact h); simpa only [hpg2] using this)
        (by rw [memBytes_congr hpg2, ← hm1]; unfold memBytes; rw [hsz])
        (fun a ha => by rw [readByte_congr hpg2, hrdW a, if_neg ha]; rfl)
        bv tb nb
        (fun i hi => R.env_msg (hmb i hi) (by simp) (by simp [Env.lsp]; omega))
        (fun i hi => by
          rw [readByte_congr hpg2, hrdW (ea + i), if_pos (by omega), Nat.add_sub_cancel_left,
            byte_of_mod _ _ _ hi, hnb' i hi]
          simp))
    have RR := Rel_of_RelW_congr SR (stepLive_congr
      (c2 := mv :: ma :: (List.range w).map fun i => encB (ea + i) (bv i) (tb i))
      (p2 := (List.range w).map fun i => encB (ea + i) (nb i) t) ?_ ?_)
    · exact RR
    · intro x
      rw [show List.range 2 = [0, 1] from rfl]
      simp only [List.map_cons, List.map_nil, Option.toList_none, List.append_nil, List.cons_append,
        List.nil_append, Nat.add_zero, show s.stack.size - 2 + 1 = s.stack.size - 1 by omega, ← ea0, ← ev,
        List.mem_cons]
      constructor
      · rintro (h | h | h)
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · rintro (h | h | h)
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
    · intro x
      rw [show s.stack.pop.pop.size - (s.stack.size - 2) = 0 by rw [hsz']; omega]
      simp only [List.range_zero, List.map_nil, Option.toList_none, List.append_nil, List.nil_append]

end WasmBase
