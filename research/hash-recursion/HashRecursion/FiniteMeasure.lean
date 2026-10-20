import HashRecursion.Composition
import HashRecursion.Oracle

/-!
Finite event measures over any ordered additive commutative monoid. In
particular, this does not require rational quantum probabilities. Nonnegative
weights and their normalization must come from the eventual Born-rule model.
There is no assumption that an arbitrary extraction coupling exists.
-/
namespace HashRecursion.Quantum
open Lean.Grind Lean.Grind.AddCommMonoid Std

variable {Ω R : Type} [AddCommMonoid R] [LE R] [IsPreorder R] [OrderedAdd R]

noncomputable def eventMass (outcomes : List Ω) (weight : Ω → R)
    (event : Ω → Prop) : R := by
  classical
  exact (outcomes.map (fun ω => if event ω then weight ω else 0)).sum

private theorem map_sum_mono (xs : List Ω) (f g : Ω → R)
    (h : ∀ x, f x ≤ g x) : (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => exact le_refl _
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    exact OrderedAdd.add_le_add (h x) ih

omit [LE R] [IsPreorder R] [OrderedAdd R] in
private theorem map_sum_add (xs : List Ω) (f g : Ω → R) :
    (xs.map (fun x => f x + g x)).sum = (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => simp [add_zero]
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    simp only [add_assoc, add_left_comm]

theorem eventMass_mono (outcomes : List Ω) (weight : Ω → R)
    (nonneg : ∀ ω, 0 ≤ weight ω) (E F : Ω → Prop)
    (h : ∀ ω, E ω → F ω) : eventMass outcomes weight E ≤ eventMass outcomes weight F := by
  classical
  apply map_sum_mono
  intro ω
  by_cases he : E ω
  · simp only [he, h ω he, ite_true]
    exact le_refl _
  · simp only [he, ite_false]
    by_cases hf : F ω
    · simpa only [hf, ite_true] using nonneg ω
    · simp only [hf, ite_false]
      exact le_refl _

theorem eventMass_union_le (outcomes : List Ω) (weight : Ω → R)
    (nonneg : ∀ ω, 0 ≤ weight ω) (E F : Ω → Prop) :
    eventMass outcomes weight (fun ω => E ω ∨ F ω) ≤
      eventMass outcomes weight E + eventMass outcomes weight F := by
  classical
  unfold eventMass
  rw [← map_sum_add]
  apply map_sum_mono
  intro ω
  by_cases he : E ω <;> by_cases hf : F ω
  · simp only [he, hf, true_or, ite_true]
    have hh := OrderedAdd.add_le_right (weight ω) (nonneg ω)
    simpa only [add_zero] using hh
  · simp only [he, hf, true_or, ite_true, ite_false, add_zero]
    exact le_refl _
  · simp only [he, hf, or_true, ite_true, ite_false, zero_add]
    exact le_refl _
  · simp only [he, hf, false_or, ite_false, add_zero]
    exact le_refl _

theorem eventMass_le_total (outcomes : List Ω) (weight : Ω → R)
    (nonneg : ∀ ω, 0 ≤ weight ω) (E : Ω → Prop) :
    eventMass outcomes weight E ≤ (outcomes.map weight).sum := by
  classical
  have hh := eventMass_mono outcomes weight nonneg E (fun _ => True) (fun _ _ => trivial)
  simpa only [eventMass, ite_true] using hh

/-- Union-bound consequence of a supplied extraction coupling, with no
independence or rationality assumption. Establishing the coupling and the
distribution of its extracted adversary remains a cryptographic obligation. -/
theorem extraction_mass_bound {C I : Type}
    (outcomes : List Ω) (weight : Ω → R) (nonneg : ∀ ω, 0 ≤ weight ω)
    (claim : Ω → C) (extracted : Ω → I) (language : C → Prop)
    (inner : C → I → Prop) (accepted failure : Ω → Prop)
    (extracts : ∀ ω, accepted ω → ¬ failure ω → inner (claim ω) (extracted ω)) :
    eventMass outcomes weight (fun ω => accepted ω ∧ ¬ language (claim ω)) ≤
      eventMass outcomes weight failure +
      eventMass outcomes weight
        (fun ω => inner (claim ω) (extracted ω) ∧ ¬ language (claim ω)) := by
  apply le_trans (eventMass_mono outcomes weight nonneg _ _
    (extraction_event_inclusion claim extracted language inner accepted failure extracts))
  exact eventMass_union_le outcomes weight nonneg _ _

omit [LE R] [IsPreorder R] [OrderedAdd R] in
/-- Oracle queries preserve the mass of any event about the unchanged input
and workspace registers, even with entanglement. The weight function is any
pointwise amplitude weight (e.g. squared complex modulus). -/
theorem query_preserves_input_event {n m : Nat} {W A : Type}
    (basis : FiniteBasis (Register n m W)) (h : BitVec n → BitVec m)
    (weight : A → R) (ψ : Register n m W → A) (E : BitVec n → W → Prop) :
    eventMass basis.elements (fun b => weight (query h ψ b)) (fun b => E b.1 b.2.2) =
      eventMass basis.elements (fun b => weight (ψ b)) (fun b => E b.1 b.2.2) := by
  classical
  let f := fun b : Register n m W => if E b.1 b.2.2 then weight (ψ b) else 0
  have hp := (basis.involution_perm (oracleStep h) (oracleStep_involution h)).map f
  have hs : ((basis.elements.map (oracleStep h)).map f).sum =
      (basis.elements.map f).sum := by
    apply hp.foldr_eq'
    intro x _ y _ z
    simp only [add_left_comm]
  unfold eventMass
  calc
    _ = ((basis.elements.map (oracleStep h)).map f).sum := by
      rw [List.map_map]
      congr 1
    _ = _ := hs

end HashRecursion.Quantum
