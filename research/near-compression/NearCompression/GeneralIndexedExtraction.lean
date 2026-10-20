import NearCompression.GeneralIndexedParent
import NearCompression.IndexedFoldExtraction
import NearCompression.FiniteIndexTransport
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

noncomputable def generalIndexedFoldSuccess (N D T : Nat) (weight : Nat → Nat)
    (source : Nat → K) (root childRoot : K) (evenWeights oddWeights : List K)
    (sent : Poly K) (r : K) : Prop :=
  ∃ p : Poly K,p.DegLt D ∧
    T≤consistencyMass (List.range N) (fun y => weight y+weight (y+N))
      (fun y => indexedPairFold N source root r y=p.eval (childRoot^y)) ∧
    (1-r)*scalarRSResidual evenWeights p+r*scalarRSResidual oddWeights p=sent.eval r

noncomputable def generalIndexedFoldOutcome (N D T : Nat) (weight : Nat → Nat)
    (source : Nat → K) (root childRoot : K) (evenWeights oddWeights : List K)
    (sent : Poly K) : Prop :=
  ∃ even odd : Poly K,even.DegLt D ∧ odd.DegLt D ∧
    T≤consistencyMass (List.range N) (fun y => weight y+weight (y+N))
      (fun y => rsPairDecode (root^y) (source y,source (y+N))=
        (even.eval (childRoot^y),odd.eval (childRoot^y))) ∧
    (sent-generalFoldResidualPolynomial evenWeights oddWeights even odd).IsZero

/-- Same nonlinear concentration obligation in the implementation's natural
integer index coordinates. Root-domain validity is required to prove it from
the primary theorem; this definition does not assert it holds. -/
noncomputable def GeneralIndexedFoldExtraction (sample : List K) (error N D T : Nat)
    (weight : Nat → Nat) (source : Nat → K) (root childRoot : K)
    (evenWeights oddWeights : List K) (sent : Poly K) : Prop :=
  error<count sample (generalIndexedFoldSuccess N D T weight source root childRoot evenWeights oddWeights sent) →
    generalIndexedFoldOutcome N D T weight source root childRoot evenWeights oddWeights sent

noncomputable def generalIndexedFoldBad (N D T : Nat) (weight : Nat → Nat)
    (source : Nat → K) (root childRoot : K) (evenWeights oddWeights : List K)
    (sent : Poly K) (r : K) : Prop :=
  generalIndexedFoldSuccess N D T weight source root childRoot evenWeights oddWeights sent r ∧
    ¬generalIndexedFoldOutcome N D T weight source root childRoot evenWeights oddWeights sent

theorem general_indexed_fold_bad_count (sample : List K) (error N D T : Nat)
    (weight : Nat → Nat) (source : Nat → K) (root childRoot : K)
    (evenWeights oddWeights : List K) (sent : Poly K)
    (extraction : GeneralIndexedFoldExtraction sample error N D T weight source root childRoot evenWeights oddWeights sent) :
    count sample (generalIndexedFoldBad N D T weight source root childRoot evenWeights oddWeights sent)≤error := by
  classical
  by_cases outcome : generalIndexedFoldOutcome N D T weight source root childRoot evenWeights oddWeights sent
  · simp [generalIndexedFoldBad,outcome,count]
  · have bound : count sample (generalIndexedFoldSuccess N D T weight source root childRoot evenWeights oddWeights sent)≤error := by
      have h : ¬error<count sample (generalIndexedFoldSuccess N D T weight source root childRoot evenWeights oddWeights sent) :=
        fun many => outcome (extraction many)
      omega
    apply Nat.le_trans _ bound
    apply count_mono
    intro r h
    exact h.1

theorem general_indexed_unique_extraction (sample : List K) (sampleDistinct : sample.Nodup)
    (N D T B : Nat) (weight : Nat → Nat) (source : Nat → K)
    (root childRoot : K) (evenWeights oddWeights : List K) (sent : Poly K)
    (pointInjective : ∀ i<N,∀ j<N,childRoot^i=childRoot^j → i=j)
    (bounded : ∀ i<N,weight i+weight (i+N)≤B)
    (sentDegree : sent.DegLt 3)
    (separation : 2*((List.range N).map (fun i => weight i+weight (i+N))).sum+B*(D-1)<3*T) :
    GeneralIndexedFoldExtraction sample (max N 2) N D T weight source root childRoot evenWeights oddWeights sent := by
  classical
  intro many
  let point : Nat → K := fun i => childRoot^i
  let index := finitePointIndex N point
  let domain := (List.range N).map point
  let projected : Nat → Nat := fun i => weight i+weight (i+N)
  let evenSource : K → K := fun x => (rsPairDecode (root^(index x)) (source (index x),source (index x+N))).1
  let oddSource : K → K := fun x => (rsPairDecode (root^(index x)) (source (index x),source (index x+N))).2
  have transport (event : Nat → K → Prop) :
      consistencyMass domain (fun x => projected (index x)) (fun x => event (index x) x)=
      consistencyMass (List.range N) projected (fun i => event i (point i)) :=
    finite_index_mass_transport N point pointInjective projected event
  have fieldBound : ∀ x∈domain,projected (index x)≤B := by
    intro x hx
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
    change projected (finitePointIndex N point (point i))≤B
    rw [finite_point_index_inverse N point pointInjective i (List.mem_range.mp hi)]
    exact bounded i (List.mem_range.mp hi)
  have fieldSeparation : 2*(domain.map (fun x => projected (index x))).sum+B*(D-1)<3*T := by
    rw [finite_index_weight_sum N point pointInjective projected]
    exact separation
  have successTransfer (r : K)
      (success : generalIndexedFoldSuccess N D T weight source root childRoot evenWeights oddWeights sent r) :
      generalWeightedCurveSuccess domain (fun x => projected (index x)) evenSource oddSource D T evenWeights oddWeights sent r := by
    obtain ⟨p,degree,agree,residual⟩ := success
    refine ⟨p,degree,?_,residual⟩
    change T≤consistencyMass domain (fun x => projected (index x))
      (fun x => p.eval x=(1-r)*(rsPairDecode (root^(index x)) (source (index x),source (index x+N))).1+
        r*(rsPairDecode (root^(index x)) (source (index x),source (index x+N))).2)
    rw [transport (fun i x => p.eval x=(1-r)*(rsPairDecode (root^i) (source i,source (i+N))).1+
      r*(rsPairDecode (root^i) (source i,source (i+N))).2)]
    apply Nat.le_trans agree
    apply consistency_mass_mono
    intro i hi eq
    exact eq.symm
  have fieldMany : max domain.length 2<count sample
      (generalWeightedCurveSuccess domain (fun x => projected (index x)) evenSource oddSource D T evenWeights oddWeights sent) := by
    have subset : count sample (generalIndexedFoldSuccess N D T weight source root childRoot evenWeights oddWeights sent)≤
        count sample (generalWeightedCurveSuccess domain (fun x => projected (index x)) evenSource oddSource D T evenWeights oddWeights sent) := by
      apply count_mono
      exact successTransfer
    have length : domain.length=N := by simp [domain]
    rw [length]
    omega
  obtain ⟨even,odd,de,do_,agree,identity⟩ := general_weighted_extraction_count domain sample
    (finite_point_domain_nodup N point pointInjective) sampleDistinct
    (fun x => projected (index x)) B D T fieldBound evenSource oddSource evenWeights oddWeights sent
    sentDegree fieldSeparation fieldMany
  refine ⟨even,odd,de,do_,?_,identity⟩
  change T≤consistencyMass domain (fun x => projected (index x))
    (fun x => (rsPairDecode (root^(index x)) (source (index x),source (index x+N))).1=even.eval x ∧
      (rsPairDecode (root^(index x)) (source (index x),source (index x+N))).2=odd.eval x) at agree
  rw [transport (fun i x => (rsPairDecode (root^i) (source i,source (i+N))).1=even.eval x ∧
    (rsPairDecode (root^i) (source i,source (i+N))).2=odd.eval x)] at agree
  apply Nat.le_trans agree
  apply consistency_mass_mono
  intro i hi h
  exact Prod.ext h.1 h.2

/-- The formerly conditional per-round concentration bad count now has a
proved max(N,2) bound under explicit finite-domain and separation certificates. -/
theorem general_indexed_unique_bad_count (sample : List K) (sampleDistinct : sample.Nodup)
    (N D T B : Nat) (weight : Nat → Nat) (source : Nat → K)
    (root childRoot : K) (evenWeights oddWeights : List K) (sent : Poly K)
    (pointInjective : ∀ i<N,∀ j<N,childRoot^i=childRoot^j → i=j)
    (bounded : ∀ i<N,weight i+weight (i+N)≤B)
    (sentDegree : sent.DegLt 3)
    (separation : 2*((List.range N).map (fun i => weight i+weight (i+N))).sum+B*(D-1)<3*T) :
    count sample (generalIndexedFoldBad N D T weight source root childRoot evenWeights oddWeights sent)≤max N 2 :=
  general_indexed_fold_bad_count sample (max N 2) N D T weight source root childRoot evenWeights oddWeights sent
    (general_indexed_unique_extraction sample sampleDistinct N D T B weight source root childRoot evenWeights oddWeights sent pointInjective bounded sentDegree separation)

theorem general_indexed_child_implies_success (N0 : Nat) (sizes degrees : Nat → Nat)
    (roots challenges : Nat → K) (oracles : Nat → Nat → K)
    (allWeights : Nat → List K) (claims : Nat → K) (T i : Nat)
    (evenWeights oddWeights : List K) (weightShape : evenWeights.length=oddWeights.length) (sent : Poly K)
    (nextWeights : allWeights (i+1)=generalFoldWeights evenWeights oddWeights (challenges i))
    (nextClaim : claims (i+1)=sent.eval (challenges i))
    (child : indexedChainCandidate N0 sizes degrees roots challenges oracles allWeights claims T (i+1)) :
    generalIndexedFoldSuccess (sizes (i+1)) (degrees (i+1)) T
      (globalChainWeight (List.range N0) sizes (globalRSChainCheck sizes roots challenges oracles) i)
      (oracles i) (roots i) (roots (i+1)) evenWeights oddWeights sent (challenges i) := by
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
  · rw [nextWeights,general_fold_weights_functional _ _ _ _ weightShape,nextClaim] at residual
    exact residual

theorem general_indexed_outcome_implies_parent (N0 : Nat) (sizes degrees : Nat → Nat)
    (roots challenges : Nat → K) (oracles : Nat → Nat → K)
    (allWeights : Nat → List K) (claims : Nat → K) (T i : Nat)
    (evenWeights oddWeights : List K) (weightShape : evenWeights.length=oddWeights.length) (sent : Poly K)
    (sizeStep : sizes i=2*sizes (i+1)) (degreeStep : degrees i=2*degrees (i+1))
    (parentWeights : allWeights i=rsInterleave evenWeights oddWeights)
    (parentClaim : claims i=sent.eval 0+sent.eval 1)
    (h2 : (2:K)≠0) (nonzero : ∀ y<sizes (i+1),roots i^y≠0)
    (squared : ∀ y<sizes (i+1),roots (i+1)^y=roots i^y*roots i^y)
    (negative : ∀ y<sizes (i+1),roots i^(y+sizes (i+1))= -(roots i^y))
    (outcome : generalIndexedFoldOutcome (sizes (i+1)) (degrees (i+1)) T
      (globalChainWeight (List.range N0) sizes (globalRSChainCheck sizes roots challenges oracles) i)
      (oracles i) (roots i) (roots (i+1)) evenWeights oddWeights sent) :
    indexedChainCandidate N0 sizes degrees roots challenges oracles allWeights claims T i := by
  obtain ⟨even,odd,de,do_,agree,identity⟩ := outcome
  obtain ⟨p,degree,mass,residual⟩ := general_indexed_parent (sizes (i+1)) (degrees (i+1)) T
    (globalChainWeight (List.range N0) sizes (globalRSChainCheck sizes roots challenges oracles) i)
    (oracles i) (roots i) (roots (i+1)) evenWeights oddWeights weightShape sent even odd de do_
    h2 nonzero squared negative agree identity
  refine ⟨p,?_,?_,?_⟩
  · rw [degreeStep]; exact degree
  · rw [parentWeights,parentClaim]; exact residual
  · rw [sizeStep]; exact mass


/-- Deterministic all-round continuation for arbitrary public weight vectors.
Adaptive challenge counting and hash binding remain separate. -/
theorem general_chain_query_bound_outside_bad
    (N0 : Nat) (sizes degrees : Nat → Nat) (roots challenges : Nat → K)
    (oracles : Nat → Nat → K) (allWeights : Nat → List K) (claims : Nat → K)
    (evenWeights oddWeights : Nat → List K) (sent : Nat → Poly K)
    (T rounds : Nat) (positive : ∀ j≤rounds,0<sizes j)
    (sizeSteps : ∀ i<rounds,sizes i=2*sizes (i+1))
    (degreeSteps : ∀ i<rounds,degrees i=2*degrees (i+1))
    (weightShapes : ∀ i<rounds,(evenWeights i).length=(oddWeights i).length)
    (parentWeights : ∀ i<rounds,allWeights i=rsInterleave (evenWeights i) (oddWeights i))
    (nextWeights : ∀ i<rounds,allWeights (i+1)=generalFoldWeights (evenWeights i) (oddWeights i) (challenges i))
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
    (noBad : ∀ i<rounds,¬generalIndexedFoldBad (sizes (i+1)) (degrees (i+1)) T
      (globalChainWeight (List.range N0) sizes (globalRSChainCheck sizes roots challenges oracles) i)
      (oracles i) (roots i) (roots (i+1)) (evenWeights i) (oddWeights i) (sent i) (challenges i)) :
    count (List.range N0)
      (globalChainPass sizes (globalRSChainCheck sizes roots challenges oracles) rounds)<T := by
  rcases global_chain_terminal_decomposition N0 sizes degrees roots challenges oracles allWeights claims
    T rounds positive sizeSteps coefficients shape terminalValues terminalResidual initial with few|transition
  · exact few
  · obtain ⟨i,hi,noParent,child⟩ := transition
    have success := general_indexed_child_implies_success N0 sizes degrees roots challenges oracles
      allWeights claims T i (evenWeights i) (oddWeights i) (weightShapes i hi) (sent i)
      (nextWeights i hi) (nextClaims i hi) child
    have noOutcome : ¬generalIndexedFoldOutcome (sizes (i+1)) (degrees (i+1)) T
        (globalChainWeight (List.range N0) sizes (globalRSChainCheck sizes roots challenges oracles) i)
        (oracles i) (roots i) (roots (i+1)) (evenWeights i) (oddWeights i) (sent i) := by
      intro outcome
      exact noParent (general_indexed_outcome_implies_parent N0 sizes degrees roots challenges oracles
        allWeights claims T i (evenWeights i) (oddWeights i) (weightShapes i hi) (sent i)
        (sizeSteps i hi) (degreeSteps i hi) (parentWeights i hi) (parentClaims i hi)
        h2 (nonzero i hi) (squared i hi) (negative i hi) outcome)
    exact False.elim (noBad i hi ⟨success,noOutcome⟩)

end NearCompression
