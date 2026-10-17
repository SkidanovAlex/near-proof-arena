import NearCompression.FunctionalOpeningReduction
import NearCompression.CheckedInteractiveFoldSoundness

/-! The initial folding oracle, weight functional, and claim are assigned by
construction. This is an ideal oracle interface; authenticating its evaluation
from the committed packed source remains an implementation/binding obligation. -/
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

def bindFunctionalOpening (omega : K) (n : Nat) (tables : List (Nat → K))
    (sources : List (K → K)) (claim : List K → K) (point : List K)
    (tr : FoldTranscript K) : FoldTranscript K :=
  { tr with
    roots := fun i => match i with | 0 => omega | j+1 => tr.roots (j+1)
    oracles := fun i => match i with
      | 0 => fun y => weightedVirtualOracle
        (functionalBatchCoefficients n tables (fun k => point.getD k 0)) sources (omega^y)
      | j+1 => tr.oracles (j+1)
    weights := fun i => match i with | 0 => equalityWeights point | j+1 => tr.weights (j+1)
    claims := fun i => match i with | 0 => claim point | j+1 => tr.claims (j+1) }

def functionalOpeningCandidate (domain : List K) (n D T : Nat)
    (tables : List (Nat → K)) (sources : List (K → K)) (claim : List K → K)
    (point : List K) : Prop :=
  ∃ candidate : Poly K,candidate.DegLt D ∧
    scalarRSResidual (equalityWeights point) candidate=claim point ∧
    T≤count domain (fun x => weightedVirtualOracle
      (functionalBatchCoefficients n tables (fun i => point.getD i 0)) sources x=candidate.eval x)

omit [Field K] in
private theorem unit_cap_mass (domain : List Nat) (weight : Nat → Nat) (event : Nat → Prop)
    (cap : ∀ x∈domain,weight x≤1) : consistencyMass domain weight event≤count domain event := by
  classical
  induction domain with
  | nil => simp [consistencyMass,count]
  | cons x xs ih =>
    have head := cap x (by simp)
    have tail := ih (fun y hy => cap y (by simp [hy]))
    simp only [consistencyMass,count,List.map_cons,List.sum_cons,List.countP_cons] at tail ⊢
    by_cases h : event x <;> simp_all <;> omega

/-- A candidate in the actual initial folding predicate is a candidate for the
structured weighted opening. No honest polynomial is posited or extracted here. -/
theorem bound_opening_initial_candidate (omega : K) (n N D T : Nat)
    (tables : List (Nat → K)) (sources : List (K → K)) (claim : List K → K)
    (point : List K) (tr : FoldTranscript K) (sizes degrees : Nat → Nat)
    (sizeInitial : sizes 0=N) (degreeInitial : degrees 0=D)
    (candidate : indexedChainCandidate N sizes degrees
      (bindFunctionalOpening omega n tables sources claim point tr).roots
      (bindFunctionalOpening omega n tables sources claim point tr).challenges
      (bindFunctionalOpening omega n tables sources claim point tr).oracles
      (bindFunctionalOpening omega n tables sources claim point tr).weights
      (bindFunctionalOpening omega n tables sources claim point tr).claims T 0) :
    functionalOpeningCandidate ((List.range N).map (fun i => omega^i)) n D T tables sources claim point := by
  classical
  obtain ⟨p,degree,residual,mass⟩ := candidate
  let bound := bindFunctionalOpening omega n tables sources claim point tr
  have cap : ∀ y∈List.range N,globalChainWeight (List.range N) sizes
      (globalRSChainCheck sizes bound.roots bound.challenges bound.oracles) 0 y≤1 := by
    intro y hy
    simpa using global_chain_weight_cap N sizes
      (globalRSChainCheck sizes bound.roots bound.challenges bound.oracles)
      0 sizeInitial (by intro j hj; omega) y (by rw [sizeInitial]; exact List.mem_range.mp hy)
  rw [sizeInitial] at mass
  have agreement := Nat.le_trans mass (unit_cap_mass _ _ _ cap)
  refine ⟨p,by simpa [degreeInitial] using degree,residual,?_⟩
  have transfer : count (List.range N) (fun y => bound.oracles 0 y=p.eval (bound.roots 0^y))=
      count ((List.range N).map (fun i => omega^i)) (fun x => weightedVirtualOracle
        (functionalBatchCoefficients n tables (fun i => point.getD i 0)) sources x=p.eval x) := by
    simp only [count,List.countP_map,Function.comp_def]
    apply List.countP_congr
    intro y hy
    constructor <;> intro h <;> exact @_root_.decide_eq_true _ (Classical.propDecidable _)
      (@_root_.of_decide_eq_true _ (Classical.propDecidable _) h)
  rw [←transfer]
  exact agreement

/-- The raw strategy may be arbitrary on rejected histories. Only its initial
oracle/functional is supplied by the preceding weighted opening. -/
def functionalFoldStrategy (omega : K) (n : Nat) (tables : List (Nat → K))
    (sources : List (K → K)) (claim : List K → K)
    (raw : List K → List K → FoldTranscript K) (point history : List K) : FoldTranscript K :=
  bindFunctionalOpening omega n tables sources claim point (raw point history)

def functionalFoldSamples (sample : List K) (N rounds q : Nat) : List (List K × List Nat) :=
  (uniformTuples sample rounds).flatMap (fun path =>
    (uniformTuples (List.range N) q).map (fun queries => (path,queries)))

def functionalOpeningAccept (omega : K) (n N T rounds : Nat)
    (sizes degrees : Nat → Nat) (tables : List (Nat → K)) (sources : List (K → K))
    (sent : List K → Poly K) (claim : List K → K)
    (raw : List K → List K → FoldTranscript K)
    (point : List K) (fold : List K × List Nat) : Prop :=
  weightedSumcheckChecks sent claim [] point ∧
  checkedFoldAccept (functionalFoldStrategy omega n tables sources claim raw point)
    N sizes degrees T rounds fold.1 fold.2

omit [Field K] in
private theorem map_sum_const {A : Type} (xs : List A) (k : Nat) :
    (xs.map (fun _ => k)).sum=xs.length*k := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons,List.sum_cons,List.length_cons,ih]; grind

omit [Field K] in
private theorem scaled_fiber_bound {A B : Type} (outer : List A) (inner : List B)
    (accept : A → B → Prop) (bad : A → Prop) (scale limit : Nat)
    (good : ∀ a∈outer,¬bad a → count inner (accept a)*scale≤limit) :
    count (outer.flatMap (fun a => inner.map (fun b => (a,b))))
      (fun pair => accept pair.1 pair.2)*scale≤
      count outer bad*inner.length*scale+outer.length*limit := by
  classical
  induction outer with
  | nil => simp [count]
  | cons a rest ih =>
    have tail := ih (fun b hb => good b (by simp [hb]))
    have head := good a (by simp)
    have maximum : count inner (accept a)≤inner.length := List.countP_le_length
    have maxScaled := Nat.mul_le_mul_right scale maximum
    simp only [List.flatMap_cons,List.length_cons,count,List.countP_cons,
      List.countP_append,List.countP_map,Function.comp_def] at tail head maxScaled ⊢
    by_cases h : bad a <;> simp_all <;> grind

/-- Complete finite ideal-interactive accepted-leaf count. The stage-zero
source/residual match is definitional. The bound has opening error A/|S|,
fold error E/|S|, and with-replacement query error ((T-1)/N)^q.
The source and weight family precede the weighted sumcheck; this does not
assert that they precede upstream GKR challenges or authenticate real trees. -/
theorem functional_opening_fold_count (sample : List K) (sampleDistinct : sample.Nodup)
    (omega : K) (n N D T rounds q : Nat) (sizes degrees : Nat → Nat)
    (domainDistinct : ((List.range N).map (fun i => omega^i)).Nodup)
    (sizeInitial : sizes 0=N) (degreeInitial : degrees 0=D)
    (positive : ∀ i≤rounds,0<sizes i)
    (sizeHalves : ∀ i<rounds,sizes i=2*sizes (i+1))
    (degreeHalves : ∀ i<rounds,degrees i=2*degrees (i+1))
    (h2 : (2:K)≠0) (regime : 2*N+D<3*T)
    (threshold : T≤N) (interpolation : D-1<T)
    (uniqueness : 2*(N-T)+D≤N)
    (tables : List (Nat → K)) (sources : List (K → K)) (shape : tables.length=sources.length)
    (sent : List K → Poly K) (claim : List K → K)
    (raw : List K → List K → FoldTranscript K)
    (causal : ∀ point∈uniformTuples sample n,∀ path∈uniformTuples sample rounds,∀ i<rounds,
      (functionalFoldStrategy omega n tables sources claim raw point path).snapshot N sizes i=
      (functionalFoldStrategy omega n tables sources claim raw point (path.take i)).snapshot N sizes i)
    (challengeValues : ∀ point∈uniformTuples sample n,∀ path∈uniformTuples sample rounds,∀ i<rounds,
      (functionalFoldStrategy omega n tables sources claim raw point path).challenges i=path[i]?.getD 0)
    (falseStatement : ¬∃ lanes : List (Poly K),
      fixedWeightFamilyRepresentative ((List.range N).map (fun i => omega^i)) (fun _ => 1)
        n D T (fun _ : Unit => tables) sources lanes ∧
      claim []=coefficientTableFunctional n tables lanes) :
    count ((uniformTuples sample n).flatMap (fun point =>
      (functionalFoldSamples sample N rounds q).map (fun fold => (point,fold))))
      (fun pair => functionalOpeningAccept omega n N T rounds sizes degrees tables sources
        sent claim raw pair.1 pair.2)*sample.length≤
      (n*max N 2+2*n)*sample.length^n*(sample.length^rounds*N^q)+
      sample.length^n*(((List.range rounds).map (fun i => max (sizes (i+1)) 2)).sum*
        sample.length^rounds*N^q+sample.length^(rounds+1)*(T-1)^q) := by
  classical
  let domain := (List.range N).map (fun i => omega^i)
  let bad := fun point => weightedSumcheckChecks sent claim [] point ∧
    functionalOpeningCandidate domain n D T tables sources claim point
  let strategy := functionalFoldStrategy omega n tables sources claim raw
  have opening := functional_opening_reduction_count domain sample domainDistinct sampleDistinct
    n D T tables sources shape (by simpa [domain] using threshold) interpolation
    (by simpa [domain] using (show 2*N+(D-1)<3*T by omega))
    (by simpa [domain] using uniqueness) sent claim falseStatement
  change count (uniformTuples sample n) bad*sample.length≤_ at opening
  simp only [domain,List.length_map,List.length_range] at opening
  have good : ∀ point∈uniformTuples sample n,¬bad point →
      count (functionalFoldSamples sample N rounds q)
        (functionalOpeningAccept omega n N T rounds sizes degrees tables sources sent claim raw point)*sample.length≤
      ((List.range rounds).map (fun i => max (sizes (i+1)) 2)).sum*
        sample.length^rounds*N^q+sample.length^(rounds+1)*(T-1)^q := by
    intro point hp notBad
    by_cases checks : weightedSumcheckChecks sent claim [] point
    · have initial : ∀ path∈uniformTuples sample rounds,
          foldPathChecks (strategy point) N sizes degrees T rounds path →
          ¬indexedChainCandidate N sizes degrees (strategy point path).roots
            (strategy point path).challenges (strategy point path).oracles (strategy point path).weights
            (strategy point path).claims T 0 := by
        intro path hpath valid candidate
        apply notBad
        refine ⟨checks,?_⟩
        exact bound_opening_initial_candidate omega n N D T tables sources claim point (raw point path)
          sizes degrees sizeInitial degreeInitial candidate
      have foldBound := checked_interactive_unique_fold_soundness sample sampleDistinct (strategy point)
        N T rounds q sizes degrees sizeInitial positive sizeHalves degreeHalves h2
        (by simpa [degreeInitial] using regime) (causal point hp) (challengeValues point hp) initial
      have subset : count (functionalFoldSamples sample N rounds q)
          (functionalOpeningAccept omega n N T rounds sizes degrees tables sources sent claim raw point)≤
          count (functionalFoldSamples sample N rounds q)
          (fun pair => checkedFoldAccept (strategy point) N sizes degrees T rounds pair.1 pair.2) :=
        count_mono _ (fun _ h => h.2)
      exact Nat.le_trans (Nat.mul_le_mul_right sample.length subset) foldBound
    · have zero : count (functionalFoldSamples sample N rounds q)
          (functionalOpeningAccept omega n N T rounds sizes degrees tables sources sent claim raw point)=0 := by
        simp [count,functionalOpeningAccept,checks]
      rw [zero]
      omega
  have total := scaled_fiber_bound (uniformTuples sample n) (functionalFoldSamples sample N rounds q)
    (functionalOpeningAccept omega n N T rounds sizes degrees tables sources sent claim raw)
    bad sample.length _ good
  have innerLength : (functionalFoldSamples sample N rounds q).length=sample.length^rounds*N^q := by
    simp only [functionalFoldSamples,List.length_flatMap,List.length_map,uniform_tuples_length,List.length_range]
    rw [map_sum_const,uniform_tuples_length]
  rw [uniform_tuples_length,innerLength] at total
  have scaledOpening := Nat.mul_le_mul_right (sample.length^rounds*N^q) opening
  apply Nat.le_trans total
  have rearrange : count (uniformTuples sample n) bad*(sample.length^rounds*N^q)*sample.length=
      (count (uniformTuples sample n) bad*sample.length)*(sample.length^rounds*N^q) := by ac_rfl
  rw [rearrange]
  exact Nat.add_le_add_right scaledOpening _

end NearCompression
