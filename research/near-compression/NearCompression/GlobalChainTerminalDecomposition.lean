import NearCompression.GlobalChainMass
import NearCompression.ScalarRSTerminal

/-! Concrete indexed candidate states and the disclosed-terminal/query join.
No transition soundness is assumed: a large accepting query set explicitly
exhibits an index where a false candidate state becomes true. Bounding those
adaptive events requires the separate nonlinear extraction reduction. -/
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

noncomputable def indexedChainCandidate (N0 : Nat) (sizes degrees : Nat → Nat)
    (roots challenges : Nat → K) (oracles : Nat → Nat → K)
    (weights : Nat → List K) (claims : Nat → K) (threshold stage : Nat) : Prop :=
  ∃ p : Poly K,p.DegLt (degrees stage) ∧ scalarRSResidual (weights stage) p=claims stage ∧
    threshold≤consistencyMass (List.range (sizes stage))
      (globalChainWeight (List.range N0) sizes (globalRSChainCheck sizes roots challenges oracles) stage)
      (fun y => oracles stage y=p.eval (roots stage^y))

private theorem consistency_mass_all {A : Type} (domain : List A) (weight : A → Nat)
    (event : A → Prop) (all : ∀ x∈domain,event x) :
    consistencyMass domain weight event=(domain.map weight).sum := by
  classical
  induction domain with
  | nil => simp [consistencyMass]
  | cons x xs ih =>
    have h := all x (by simp)
    have rest := ih (fun y hy => all y (by simp [hy]))
    simp only [consistencyMass,List.map_cons,List.sum_cons] at rest ⊢
    rw [rest]
    simp [h]

/-- The terminal candidate is the ACTUAL disclosed coefficient list.
No existential polynomial-oracle premise is used. `terminalValues` is the
complete checked terminal oracle equality; cryptographic binding is separate. -/
theorem indexed_terminal_candidate_of_queries (N0 : Nat) (sizes degrees : Nat → Nat)
    (roots challenges : Nat → K) (oracles : Nat → Nat → K)
    (weights : Nat → List K) (claims : Nat → K) (threshold rounds : Nat)
    (positive : ∀ j≤rounds,0<sizes j)
    (halves : ∀ j<rounds,sizes j=2*sizes (j+1))
    (coefficients : List K) (shape : coefficients.length≤degrees rounds)
    (terminalValues : ∀ y<sizes rounds,
      oracles rounds y=(Poly.mk coefficients).eval (roots rounds^y))
    (terminalResidual : scalarRSResidual (weights rounds) (Poly.mk coefficients)=claims rounds)
    (many : threshold≤count (List.range N0)
      (globalChainPass sizes (globalRSChainCheck sizes roots challenges oracles) rounds)) :
    indexedChainCandidate N0 sizes degrees roots challenges oracles weights claims threshold rounds := by
  refine ⟨Poly.mk coefficients,(Poly.degLt_length _).mono shape,terminalResidual,?_⟩
  rw [consistency_mass_all _ _ _ (fun y hy => terminalValues y (List.mem_range.mp hy))]
  rw [global_rs_chain_query_count N0 sizes roots challenges oracles rounds positive halves]
  exact many

private theorem false_to_true_step (state : Nat → Prop) (rounds : Nat)
    (initial : ¬state 0) (terminal : state rounds) :
    ∃ i,i<rounds ∧ ¬state i ∧ state (i+1) := by
  classical
  induction rounds with
  | zero => exact False.elim (initial terminal)
  | succ n ih =>
    by_cases prev : state n
    · obtain ⟨i,hi,hn,hy⟩ := ih prev
      exact ⟨i,by omega,hn,hy⟩
    · exact ⟨n,by omega,prev,terminal⟩

/-- Exact fixed-transcript decomposition: absent an initial candidate, either
fewer than threshold query seeds pass, or a concrete candidate transition
occurs. This is not a hidden verifier-soundness assumption. -/
theorem global_chain_terminal_decomposition (N0 : Nat) (sizes degrees : Nat → Nat)
    (roots challenges : Nat → K) (oracles : Nat → Nat → K)
    (weights : Nat → List K) (claims : Nat → K) (threshold rounds : Nat)
    (positive : ∀ j≤rounds,0<sizes j)
    (halves : ∀ j<rounds,sizes j=2*sizes (j+1))
    (coefficients : List K) (shape : coefficients.length≤degrees rounds)
    (terminalValues : ∀ y<sizes rounds,
      oracles rounds y=(Poly.mk coefficients).eval (roots rounds^y))
    (terminalResidual : scalarRSResidual (weights rounds) (Poly.mk coefficients)=claims rounds)
    (initial : ¬indexedChainCandidate N0 sizes degrees roots challenges oracles weights claims threshold 0) :
    count (List.range N0)
      (globalChainPass sizes (globalRSChainCheck sizes roots challenges oracles) rounds)<threshold ∨
    ∃ i,i<rounds ∧
      ¬indexedChainCandidate N0 sizes degrees roots challenges oracles weights claims threshold i ∧
      indexedChainCandidate N0 sizes degrees roots challenges oracles weights claims threshold (i+1) := by
  classical
  by_cases few : count (List.range N0)
      (globalChainPass sizes (globalRSChainCheck sizes roots challenges oracles) rounds)<threshold
  · exact Or.inl few
  · apply Or.inr
    exact false_to_true_step _ rounds initial
      (indexed_terminal_candidate_of_queries N0 sizes degrees roots challenges oracles weights claims
        threshold rounds positive halves coefficients shape terminalValues terminalResidual (by omega))

end NearCompression
