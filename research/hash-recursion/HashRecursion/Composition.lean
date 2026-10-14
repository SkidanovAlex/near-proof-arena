import Std

/-!
Model-independent logical obligations for recursive compression.
There is no quantum adversary semantics or extractor construction in this file.
An outcome can encode an entire coupled reduction experiment. Establishing that
such a coupling exists, with suitable distributions and resources, is a separate
cryptographic obligation; the pointwise hypothesis below does not establish it.
-/
namespace HashRecursion

def WrappedLanguage {C P : Type} (verify : C → P → Prop) (c : C) : Prop :=
  ∃ p, verify c p

/-- Perfect soundness for the existential wrapper language does not imply
soundness for the intended language. This is a logical counterexample, not a
claim that the toy inner verifier is computationally sound. -/
theorem existential_wrapper_counterexample :
    ∃ (language : Bool → Prop) (inner outer : Bool → Unit → Prop),
      (∀ c p, outer c p → WrappedLanguage inner c) ∧
      (∃ c p, outer c p ∧ ¬ language c) := by
  refine ⟨(fun c => c = true), (fun _ _ => True), (fun _ _ => True), ?_, ?_⟩
  · intro c _ _
    exact ⟨(), trivial⟩
  · exact ⟨false, (), trivial, Bool.false_ne_true⟩

/-- With perfect inner soundness the existential wrapper does
compose. Computational soundness alone is not this hypothesis. -/
theorem perfect_composition {C I O : Type} (language : C → Prop)
    (inner : C → I → Prop) (outer : C → O → Prop)
    (hi : ∀ c p, inner c p → language c)
    (ho : ∀ c p, outer c p → WrappedLanguage inner c) :
    ∀ c p, outer c p → language c := by
  intro c p h
  obtain ⟨ip, hp⟩ := ho c p h
  exact hi c ip hp

/-- Outside an explicitly identified extraction failure, an accepted false
outer claim yields an accepted false inner claim with the SAME statement. -/
theorem extraction_event_inclusion {Ω C I : Type}
    (claim : Ω → C) (extracted : Ω → I) (language : C → Prop)
    (inner : C → I → Prop) (accepted extractionFailure : Ω → Prop)
    (extracts : ∀ ω, accepted ω → ¬ extractionFailure ω →
      inner (claim ω) (extracted ω)) :
    ∀ ω, (accepted ω ∧ ¬ language (claim ω)) →
      extractionFailure ω ∨
        (inner (claim ω) (extracted ω) ∧ ¬ language (claim ω)) := by
  intro ω h
  classical
  by_cases he : extractionFailure ω
  · exact Or.inl he
  · exact Or.inr ⟨extracts ω h.1 he, h.2⟩

/-- Resources charged to the EXTRACTED adversary, not just the original one.
Time is an abstract cost unit; instantiation must specify its quantum meaning. -/
structure Resources where
  hashQueries : Nat
  proofQueries : Nat
  time : Nat
  deriving DecidableEq, Repr

def Resources.Within (used limit : Resources) : Prop :=
  used.hashQueries ≤ limit.hashQueries ∧
  used.proofQueries ≤ limit.proofQueries ∧ used.time ≤ limit.time

theorem Resources.within_trans {a b c : Resources}
    (h : a.Within b) (k : b.Within c) : a.Within c :=
  ⟨Nat.le_trans h.1 k.1, Nat.le_trans h.2.1 k.2.1, Nat.le_trans h.2.2 k.2.2⟩

end HashRecursion
