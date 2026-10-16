import NearCompression.IndexedWeightedPullback
import NearCompression.GlobalChainTerminalDecomposition

namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

def indexedPairFold (N : Nat) (source : Nat → K) (root r : K) (y : Nat) : K :=
  let eo := rsPairDecode (root^y) (source y,source (y+N))
  (1-r)*eo.1+r*eo.2

noncomputable def indexedFoldSuccess (N D T : Nat) (weight : Nat → Nat)
    (source : Nat → K) (root childRoot : K) (weights : List K) (w0 w1 : K)
    (sent : Poly K) (r : K) : Prop :=
  ∃ p : Poly K,p.DegLt D ∧
    T≤consistencyMass (List.range N) (fun y => weight y+weight (y+N))
      (fun y => indexedPairFold N source root r y=p.eval (childRoot^y)) ∧
    ((1-r)*w0+r*w1)*scalarRSResidual weights p=sent.eval r

noncomputable def indexedFoldOutcome (N D T : Nat) (weight : Nat → Nat)
    (source : Nat → K) (root childRoot : K) (weights : List K) (w0 w1 : K)
    (sent : Poly K) : Prop :=
  ∃ even odd : Poly K,even.DegLt D ∧ odd.DegLt D ∧
    T≤consistencyMass (List.range N) (fun y => weight y+weight (y+N))
      (fun y => rsPairDecode (root^y) (source y,source (y+N))=
        (even.eval (childRoot^y),odd.eval (childRoot^y))) ∧
    (sent-weightedFoldResidualPolynomial w0 w1
      (scalarRSResidual weights even) (scalarRSResidual weights odd)).IsZero

/-- Same nonlinear concentration obligation in the implementation's natural
integer index coordinates. Root-domain validity is required to prove it from
the primary theorem; this definition does not assert it holds. -/
noncomputable def IndexedFoldExtraction (sample : List K) (error N D T : Nat)
    (weight : Nat → Nat) (source : Nat → K) (root childRoot : K)
    (weights : List K) (w0 w1 : K) (sent : Poly K) : Prop :=
  error<count sample (indexedFoldSuccess N D T weight source root childRoot weights w0 w1 sent) →
    indexedFoldOutcome N D T weight source root childRoot weights w0 w1 sent

noncomputable def indexedFoldBad (N D T : Nat) (weight : Nat → Nat)
    (source : Nat → K) (root childRoot : K) (weights : List K) (w0 w1 : K)
    (sent : Poly K) (r : K) : Prop :=
  indexedFoldSuccess N D T weight source root childRoot weights w0 w1 sent r ∧
    ¬indexedFoldOutcome N D T weight source root childRoot weights w0 w1 sent

theorem indexed_fold_bad_count (sample : List K) (error N D T : Nat)
    (weight : Nat → Nat) (source : Nat → K) (root childRoot : K)
    (weights : List K) (w0 w1 : K) (sent : Poly K)
    (extraction : IndexedFoldExtraction sample error N D T weight source root childRoot weights w0 w1 sent) :
    count sample (indexedFoldBad N D T weight source root childRoot weights w0 w1 sent)≤error := by
  classical
  by_cases outcome : indexedFoldOutcome N D T weight source root childRoot weights w0 w1 sent
  · simp [indexedFoldBad,outcome,count]
  · have bound : count sample (indexedFoldSuccess N D T weight source root childRoot weights w0 w1 sent)≤error := by
      have h : ¬error<count sample (indexedFoldSuccess N D T weight source root childRoot weights w0 w1 sent) :=
        fun many => outcome (extraction many)
      omega
    apply Nat.le_trans _ bound
    apply count_mono
    intro r h
    exact h.1

theorem scalar_residual_weight_scale (weights : List K) (p : Poly K) (s : K) :
    scalarRSResidual (weights.map (fun w => s*w)) p=s*scalarRSResidual weights p := by
  unfold scalarRSResidual
  generalize 0=offset
  induction weights generalizing offset with
  | nil => simp only [List.map_nil,scalarRSResidualFrom]; grind
  | cons w ws ih => simp only [List.map_cons,scalarRSResidualFrom,ih]; grind

/-- Exact transition: a post-round candidate yields the fixed projected-measure
success predicate. This uses the literal transcript weight recurrence. -/
theorem indexed_child_implies_fold_success (N0 : Nat) (sizes degrees : Nat → Nat)
    (roots challenges : Nat → K) (oracles : Nat → Nat → K)
    (allWeights : Nat → List K) (claims : Nat → K) (T i : Nat)
    (tailWeights : List K) (w0 w1 : K) (sent : Poly K)
    (nextWeights : allWeights (i+1)=tailWeights.map
      (fun w => ((1-challenges i)*w0+challenges i*w1)*w))
    (nextClaim : claims (i+1)=sent.eval (challenges i))
    (child : indexedChainCandidate N0 sizes degrees roots challenges oracles allWeights claims T (i+1)) :
    indexedFoldSuccess (sizes (i+1)) (degrees (i+1)) T
      (globalChainWeight (List.range N0) sizes (globalRSChainCheck sizes roots challenges oracles) i)
      (oracles i) (roots i) (roots (i+1)) tailWeights w0 w1 sent (challenges i) := by
  classical
  obtain ⟨p,degree,residual,agree⟩ := child
  refine ⟨p,degree,?_,?_⟩
  · have transfer := consistency_gated_agreement (List.range (sizes (i+1)))
      (fun y => globalChainWeight (List.range N0) sizes
        (globalRSChainCheck sizes roots challenges oracles) i y+
        globalChainWeight (List.range N0) sizes
        (globalRSChainCheck sizes roots challenges oracles) i (y+sizes (i+1)))
      (indexedPairFold (sizes (i+1)) (oracles i) (roots i) (challenges i))
      (oracles (i+1)) (fun y => p.eval (roots (i+1)^y))
    have eqPred : ∀ y,globalRSChainCheck sizes roots challenges oracles i y ↔
        oracles (i+1) y=indexedPairFold (sizes (i+1)) (oracles i) (roots i) (challenges i) y := by
      intro y; exact eq_comm
    simp only [globalChainWeight,eqPred] at agree
    exact Nat.le_trans agree transfer
  · rw [nextWeights,scalar_residual_weight_scale,nextClaim] at residual
    exact residual

theorem indexed_outcome_implies_parent (N0 : Nat) (sizes degrees : Nat → Nat)
    (roots challenges : Nat → K) (oracles : Nat → Nat → K)
    (allWeights : Nat → List K) (claims : Nat → K) (T i : Nat)
    (tailWeights : List K) (w0 w1 : K) (sent : Poly K)
    (sizeStep : sizes i=2*sizes (i+1)) (degreeStep : degrees i=2*degrees (i+1))
    (parentWeights : allWeights i=rsInterleave (tailWeights.map (fun w => w0*w))
      (tailWeights.map (fun w => w1*w)))
    (parentClaim : claims i=sent.eval 0+sent.eval 1)
    (h2 : (2:K)≠0) (nonzero : ∀ y<sizes (i+1),roots i^y≠0)
    (squared : ∀ y<sizes (i+1),roots (i+1)^y=roots i^y*roots i^y)
    (negative : ∀ y<sizes (i+1),roots i^(y+sizes (i+1))= -(roots i^y))
    (outcome : indexedFoldOutcome (sizes (i+1)) (degrees (i+1)) T
      (globalChainWeight (List.range N0) sizes (globalRSChainCheck sizes roots challenges oracles) i)
      (oracles i) (roots i) (roots (i+1)) tailWeights w0 w1 sent) :
    indexedChainCandidate N0 sizes degrees roots challenges oracles allWeights claims T i := by
  obtain ⟨even,odd,de,do_,agree,identity⟩ := outcome
  obtain ⟨p,degree,mass,residual⟩ := indexed_weighted_parent (sizes (i+1)) (degrees (i+1)) T
    (globalChainWeight (List.range N0) sizes (globalRSChainCheck sizes roots challenges oracles) i)
    (oracles i) (roots i) (roots (i+1)) tailWeights w0 w1 sent even odd de do_
    h2 nonzero squared negative agree identity
  refine ⟨p,?_,?_,?_⟩
  · rw [degreeStep]; exact degree
  · rw [parentWeights,parentClaim]; exact residual
  · rw [sizeStep]; exact mass

/-- Concrete all-round interactive algebra skeleton. Outside the explicitly
defined concentration bad events, a false initial candidate implies fewer
than T accepted global query seeds. Every transition is proved above; there
is no abstract candidate-preservation or verifier-soundness premise. -/
theorem global_chain_query_bound_outside_extraction_bad
    (N0 : Nat) (sizes degrees : Nat → Nat) (roots challenges : Nat → K)
    (oracles : Nat → Nat → K) (allWeights : Nat → List K) (claims : Nat → K)
    (tailWeights : Nat → List K) (w0 w1 : Nat → K) (sent : Nat → Poly K)
    (T rounds : Nat) (positive : ∀ j≤rounds,0<sizes j)
    (sizeSteps : ∀ i<rounds,sizes i=2*sizes (i+1))
    (degreeSteps : ∀ i<rounds,degrees i=2*degrees (i+1))
    (parentWeights : ∀ i<rounds,allWeights i=rsInterleave
      ((tailWeights i).map (fun w => w0 i*w)) ((tailWeights i).map (fun w => w1 i*w)))
    (nextWeights : ∀ i<rounds,allWeights (i+1)=(tailWeights i).map
      (fun w => ((1-challenges i)*w0 i+challenges i*w1 i)*w))
    (parentClaims : ∀ i<rounds,claims i=(sent i).eval 0+(sent i).eval 1)
    (nextClaims : ∀ i<rounds,claims (i+1)=(sent i).eval (challenges i))
    (h2 : (2:K)≠0)
    (nonzero : ∀ i<rounds,∀ y<sizes (i+1),roots i^y≠0)
    (squared : ∀ i<rounds,∀ y<sizes (i+1),roots (i+1)^y=roots i^y*roots i^y)
    (negative : ∀ i<rounds,∀ y<sizes (i+1),roots i^(y+sizes (i+1))= -(roots i^y))
    (coefficients : List K) (shape : coefficients.length≤degrees rounds)
    (terminalValues : ∀ y<sizes rounds,oracles rounds y=(Poly.mk coefficients).eval (roots rounds^y))
    (terminalResidual : scalarRSResidual (allWeights rounds) (Poly.mk coefficients)=claims rounds)
    (initial : ¬indexedChainCandidate N0 sizes degrees roots challenges oracles allWeights claims T 0)
    (noBad : ∀ i<rounds,¬indexedFoldBad (sizes (i+1)) (degrees (i+1)) T
      (globalChainWeight (List.range N0) sizes (globalRSChainCheck sizes roots challenges oracles) i)
      (oracles i) (roots i) (roots (i+1)) (tailWeights i) (w0 i) (w1 i) (sent i) (challenges i)) :
    count (List.range N0)
      (globalChainPass sizes (globalRSChainCheck sizes roots challenges oracles) rounds)<T := by
  rcases global_chain_terminal_decomposition N0 sizes degrees roots challenges oracles allWeights claims
    T rounds positive sizeSteps coefficients shape terminalValues terminalResidual initial with few|transition
  · exact few
  · obtain ⟨i,hi,noParent,child⟩ := transition
    have success := indexed_child_implies_fold_success N0 sizes degrees roots challenges oracles
      allWeights claims T i (tailWeights i) (w0 i) (w1 i) (sent i)
      (nextWeights i hi) (nextClaims i hi) child
    have noOutcome : ¬indexedFoldOutcome (sizes (i+1)) (degrees (i+1)) T
        (globalChainWeight (List.range N0) sizes (globalRSChainCheck sizes roots challenges oracles) i)
        (oracles i) (roots i) (roots (i+1)) (tailWeights i) (w0 i) (w1 i) (sent i) := by
      intro outcome
      exact noParent (indexed_outcome_implies_parent N0 sizes degrees roots challenges oracles
        allWeights claims T i (tailWeights i) (w0 i) (w1 i) (sent i)
        (sizeSteps i hi) (degreeSteps i hi) (parentWeights i hi) (parentClaims i hi)
        h2 (nonzero i hi) (squared i hi) (negative i hi) outcome)
    exact False.elim (noBad i hi ⟨success,noOutcome⟩)

end NearCompression
