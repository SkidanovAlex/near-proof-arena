import WasmBase.Prelude
/-!
# WasmBase.Chain — the execution chain from the STATE bus

Abstractly: edges `(in, out)` (one per active instruction row), an initial and a final message,
and a level function (the timestamp field) with `level out = level in + 1` in `F_p`.  If
`init :: outs` is a permutation of `final :: ins` and there are fewer than `p - 1` edges, the
edges form a single path from `init` to `final` (no cycles, no branching, nothing left over).
A cycle would need `p` edges: the levels increase by one per edge in `F_p`.
-/
namespace WasmBase
open ZkFormal.Algebra
set_option linter.unusedSimpArgs false

variable {α : Type}

/-- `es` is a path of edges from `a` to `b`. -/
def IsPath : α → List (α × α) → α → Prop
  | a, [], b => a = b
  | a, e :: es, b => e.1 = a ∧ IsPath e.2 es b

def fsum (l : List F) : F := l.foldr (· + ·) 0

theorem fsum_perm {l₁ l₂ : List F} (h : l₁.Perm l₂) : fsum l₁ = fsum l₂ := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp only [fsum, List.foldr_cons] at *; rw [ih]
  | swap x y l => simp only [fsum, List.foldr_cons]; grind
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem fsum_levels (R : List (α × α)) (lv : α → F) (hstep : ∀ e ∈ R, lv e.2 = lv e.1 + 1) :
    fsum (R.map fun e => lv e.2) = fsum (R.map fun e => lv e.1) + (R.length : F) := by
  induction R with
  | nil => simp [fsum]; rfl
  | cons e R ih =>
    simp only [List.map_cons, fsum, List.foldr_cons, List.length_cons] at *
    rw [ih (fun e' he' => hstep e' (List.mem_cons_of_mem _ he')), hstep e List.mem_cons_self,
      Lean.Grind.Semiring.natCast_add]
    grind

/-- No nonempty cycle of fewer than `p` edges. -/
theorem no_cycle (R : List (α × α)) (lv : α → F) (hstep : ∀ e ∈ R, lv e.2 = lv e.1 + 1)
    (hlen : R.length < P) (hperm : (R.map Prod.snd).Perm (R.map Prod.fst)) : R = [] := by
  have h1 := fsum_perm (hperm.map lv)
  simp only [List.map_map] at h1
  have h2 := fsum_levels R lv hstep
  have h3 : ((R.length : Nat) : F) = ((0 : Nat) : F) := by
    have e1 : fsum (R.map fun e => lv e.2) = fsum (R.map (lv ∘ Prod.snd)) := rfl
    have e2 : fsum (R.map fun e => lv e.1) = fsum (R.map (lv ∘ Prod.fst)) := rfl
    rw [e1, e2, h1] at h2
    rw [show ((0 : Nat) : F) = 0 from rfl]
    grind
  have := natEq h3 hlen (by decide)
  exact List.length_eq_zero_iff.mp this

theorem chain_aux [DecidableEq α] (final : α) (lv : α → F) :
    ∀ (n : Nat) (R : List (α × α)) (cur : α), R.length ≤ n →
      (cur :: R.map Prod.snd).Perm (final :: R.map Prod.fst) →
      (∀ e ∈ R, lv e.2 = lv e.1 + 1) → R.length < P →
      ∃ es : List (α × α), es.Perm R ∧ IsPath cur es final := by
  intro n
  induction n with
  | zero =>
    intro R cur hn hp _ _
    have hR : R = [] := List.length_eq_zero_iff.mp (by omega)
    subst hR
    exact ⟨[], List.Perm.refl _, by simpa [IsPath] using hp⟩
  | succ n ih =>
    intro R cur hn hp hstep hlen
    by_cases hcf : cur = final
    · subst hcf
      have hp' := (List.perm_cons cur).mp hp
      have := no_cycle R lv hstep hlen hp'
      subst this
      exact ⟨[], List.Perm.refl _, rfl⟩
    · have hmem : cur ∈ final :: R.map Prod.fst := hp.subset List.mem_cons_self
      rcases List.mem_cons.mp hmem with h | h
      · exact absurd h hcf
      obtain ⟨e, he, hecur⟩ := List.mem_map.mp h
      let R' := R.erase e
      have hRe : R.Perm (e :: R') := List.perm_cons_erase he
      have hlen' : R'.length = R.length - 1 := List.length_erase_of_mem he
      have hR'pos : 0 < R.length := List.length_pos_of_mem he
      have hp2 : (e.2 :: R'.map Prod.snd).Perm (final :: R'.map Prod.fst) := by
        have a1 : (cur :: R.map Prod.snd).Perm (cur :: e.2 :: R'.map Prod.snd) :=
          List.Perm.cons _ (by simpa using hRe.map Prod.snd)
        have a2 : (final :: R.map Prod.fst).Perm (final :: e.1 :: R'.map Prod.fst) :=
          List.Perm.cons _ (by simpa using hRe.map Prod.fst)
        have a3 : (cur :: e.2 :: R'.map Prod.snd).Perm (cur :: final :: R'.map Prod.fst) := by
          have := (a1.symm.trans hp).trans a2
          rw [hecur] at this
          exact this.trans (List.Perm.swap _ _ _)
        exact (List.perm_cons cur).mp a3
      obtain ⟨es, hes, hpath⟩ := ih R' e.2 (by omega) hp2
        (fun e' he' => hstep e' (List.mem_of_mem_erase he')) (by omega)
      exact ⟨e :: es, (List.Perm.cons e hes).trans hRe.symm, ⟨hecur, hpath⟩⟩

/-- **Chain lemma.** -/
theorem chain [DecidableEq α] (E : List (α × α)) (init final : α) (lv : α → F)
    (hperm : (init :: E.map Prod.snd).Perm (final :: E.map Prod.fst))
    (hstep : ∀ e ∈ E, lv e.2 = lv e.1 + 1) (hlen : E.length < P) :
    ∃ es : List (α × α), es.Perm E ∧ IsPath init es final :=
  chain_aux final lv E.length E init (Nat.le_refl _) hperm hstep hlen

/-- Levels along a path. -/
theorem path_levels (lv : α → F) : ∀ (es : List (α × α)) (a b : α),
    IsPath a es b → (∀ e ∈ es, lv e.2 = lv e.1 + 1) →
    (∀ k (hk : k < es.length), lv (es[k]'hk).1 = lv a + (k : F)) ∧ lv b = lv a + (es.length : F) := by
  intro es
  induction es with
  | nil => intro a b h _; simp only [IsPath] at h; subst h; simp; rw [show ((0 : Nat) : F) = 0 from rfl]; grind
  | cons e es ih =>
    intro a b h hs
    obtain ⟨he, hp⟩ := h
    obtain ⟨ih1, ih2⟩ := ih e.2 b hp (fun e' he' => hs e' (List.mem_cons_of_mem _ he'))
    have hs0 := hs e List.mem_cons_self
    refine ⟨?_, ?_⟩
    · intro k hk
      cases k with
      | zero => simp [he]; rw [show ((0 : Nat) : F) = 0 from rfl]; grind
      | succ k =>
        simp only [List.getElem_cons_succ]
        rw [ih1 k (by simpa using hk), hs0, he, Lean.Grind.Semiring.natCast_add]
        grind
    · rw [ih2, hs0, he]; simp only [List.length_cons, Lean.Grind.Semiring.natCast_add]; grind

end WasmBase
