import NearCompression.StorageMutations

/-! Observational composition for map-independent boundaries. The interpreter
step-preservation premise is explicit and is NOT discharged by this module.
Unlike exact-state composition, codecs may reconstruct different map buckets. -/
namespace NearCompression
open NearSpecV3.Wasm

theorem real_equiv_refl (a : TTN.RealStore) : RealEquivalent a a :=
  ⟨rfl, rfl, .refl _, ⟨.refl _, rfl, rfl⟩, rfl, ⟨.refl _, rfl⟩, rfl, rfl⟩

theorem real_equiv_symm (a b : TTN.RealStore) (h : RealEquivalent a b) : RealEquivalent b a :=
  ⟨h.store.symm, h.root.symm, h.overlay.symm,
    ⟨h.acct.1.symm, h.acct.2.1.symm, h.acct.2.2.symm⟩, h.pfx.symm,
    ⟨h.recd.1.symm, h.recd.2.symm⟩, h.recBefore.symm, h.writes.symm⟩

theorem real_equiv_trans (a b c : TTN.RealStore) (h : RealEquivalent a b) (g : RealEquivalent b c) :
    RealEquivalent a c :=
  ⟨h.store.trans g.store, h.root.trans g.root, h.overlay.trans g.overlay,
    ⟨h.acct.1.trans g.acct.1, h.acct.2.1.trans g.acct.2.1, h.acct.2.2.trans g.acct.2.2⟩,
    h.pfx.trans g.pfx, ⟨h.recd.1.trans g.recd.1, h.recd.2.trans g.recd.2⟩,
    h.recBefore.trans g.recBefore, h.writes.trans g.writes⟩

theorem optional_real_equiv_refl (a : Option TTN.RealStore) : OptionalRealEquivalent a a := by
  cases a with
  | none => trivial
  | some a => exact real_equiv_refl a

theorem optional_real_equiv_symm (a b : Option TTN.RealStore) (h : OptionalRealEquivalent a b) :
    OptionalRealEquivalent b a := by
  cases a <;> cases b <;> simp only [OptionalRealEquivalent] at h ⊢
  exact real_equiv_symm _ _ h

theorem optional_real_equiv_trans (a b c : Option TTN.RealStore)
    (h : OptionalRealEquivalent a b) (g : OptionalRealEquivalent b c) : OptionalRealEquivalent a c := by
  cases a <;> cases b <;> cases c <;> simp only [OptionalRealEquivalent] at h g ⊢
  exact real_equiv_trans _ _ _ h g

theorem state_equiv_refl (s : St) : StateEquivalent s s := ⟨rfl, optional_real_equiv_refl _⟩
theorem state_equiv_symm (s t : St) (h : StateEquivalent s t) : StateEquivalent t s :=
  ⟨h.core.symm, optional_real_equiv_symm _ _ h.real⟩
theorem state_equiv_trans (s t u : St) (h : StateEquivalent s t) (g : StateEquivalent t u) :
    StateEquivalent s u := ⟨h.core.trans g.core, optional_real_equiv_trans _ _ _ h.real g.real⟩

/-- Terminal tag and error text are observable, even when all memory agrees. -/
def ResultEquivalent : Res → Res → Prop
  | .cont s, .cont t => StateEquivalent s t
  | .fin s, .fin t => StateEquivalent s t
  | .abort s e, .abort t f => StateEquivalent s t ∧ e = f
  | .unmodeled e, .unmodeled f => e = f
  | _, _ => False

theorem result_equiv_refl (r : Res) : ResultEquivalent r r := by
  cases r <;> first | exact state_equiv_refl _ | exact ⟨state_equiv_refl _, rfl⟩ | rfl

theorem result_equiv_symm (r t : Res) (h : ResultEquivalent r t) : ResultEquivalent t r := by
  cases r <;> cases t <;> simp only [ResultEquivalent] at h ⊢
  · exact state_equiv_symm _ _ h
  · exact state_equiv_symm _ _ h
  · exact ⟨state_equiv_symm _ _ h.1, h.2.symm⟩
  · exact h.symm

theorem result_equiv_trans (r t u : Res) (h : ResultEquivalent r t) (g : ResultEquivalent t u) :
    ResultEquivalent r u := by
  cases r <;> cases t <;> cases u <;> simp only [ResultEquivalent] at h g ⊢
  · exact state_equiv_trans _ _ _ h g
  · exact state_equiv_trans _ _ _ h g
  · exact ⟨state_equiv_trans _ _ _ h.1 g.1, h.2.trans g.2⟩
  · exact h.trans g

theorem result_equiv_bind (r t : Res) (h : ResultEquivalent r t) (f g : St → Res)
    (next : ∀ s u, StateEquivalent s u → ResultEquivalent (f s) (g u)) :
    ResultEquivalent (r.bind f) (t.bind g) := by
  cases r <;> cases t <;> simp only [ResultEquivalent] at h <;>
    first | exact next _ _ h | exact h

/-- Remaining whole-interpreter obligation; storage-host lemmas alone are not
this theorem. It includes every instruction and every allowed host family. -/
def StepPreservesMaps (cfg : NearCfg) (program : Prepared) : Prop :=
  ∀ s t, StateEquivalent s t → ResultEquivalent (step cfg program s) (step cfg program t)

theorem segment_equiv_of_step (cfg : NearCfg) (program : Prepared)
    (stepSim : StepPreservesMaps cfg program) (n : Nat) (s t : St) (h : StateEquivalent s t) :
    ResultEquivalent (seg cfg program n s) (seg cfg program n t) := by
  induction n generalizing s t with
  | zero => exact h
  | succ n ih =>
    exact result_equiv_bind _ _ (stepSim s t h) _ _ (fun s t h => ih s t h)

theorem fold_equiv_of_step (cfg : NearCfg) (program : Prepared)
    (stepSim : StepPreservesMaps cfg program) (ks : List Nat) (s t : St) (h : StateEquivalent s t) :
    ResultEquivalent (foldSegments cfg program ks s) (foldSegments cfg program ks t) := by
  rw [foldSegments_eq_seg, foldSegments_eq_seg]
  exact segment_equiv_of_step cfg program stepSim _ s t h

theorem run_equiv_of_step (cfg : NearCfg) (program : Prepared)
    (stepSim : StepPreservesMaps cfg program) (n : Nat) (s t : St) (h : StateEquivalent s t) :
    ResultEquivalent (run cfg program n s) (run cfg program n t) := by
  induction n generalizing s t with
  | zero => rfl
  | succ n ih =>
    have he := stepSim s t h
    cases hs : step cfg program s <;> cases ht : step cfg program t <;>
      simp only [hs, ht, ResultEquivalent] at he
    all_goals simp only [run, hs, ht]
    · exact ih _ _ he
    · exact he
    · exact he
    · exact he

theorem normalized_run_of_step (cfg : NearCfg) (program : Prepared)
    (stepSim : StepPreservesMaps cfg program) (n : Nat) (s : St) :
    ResultEquivalent (run cfg program n (normalizeStateMaps s)) (run cfg program n s) :=
  run_equiv_of_step cfg program stepSim n _ s (normalized_state_equiv s)

/-- An observational codec cannot identify termination with continuation. -/
theorem result_equiv_terminal_tag (s t : St) : ¬ ResultEquivalent (.fin s) (.cont t) := by
  intro h
  exact h

end NearCompression
