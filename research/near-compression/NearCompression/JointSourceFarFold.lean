import NearCompression.GKRJointTensorCandidate
import NearCompression.FunctionalOpeningFold

/-! Far-case accepted-count composition for fixed joint source families.
Only the initial ideal oracle is assigned; weights/claims/round messages can
be adversarial and are constrained by the existing checked folding predicate.
This is not a near-case AIR theorem or a Merkle/Fiat--Shamir reduction. -/
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

def bindJointSource (omega : K) (betas : List ((Nat → K) → K)) (sources : List (K → K))
    (point : List K) (tr : FoldTranscript K) : FoldTranscript K :=
  { tr with
    roots := fun i => match i with | 0 => omega | j+1 => tr.roots (j+1)
    oracles := fun i => match i with
      | 0 => fun y => jointBetaSource betas sources (omega^y) point
      | j+1 => tr.oracles (j+1) }

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


omit [Field K] in
private theorem unit_mass_count (domain : List K) (event : K → Prop) :
    consistencyMass domain (fun _ => 1) event=count domain event := by
  classical
  induction domain with
  | nil => simp [consistencyMass,count]
  | cons x xs ih =>
    simp only [consistencyMass,List.map_cons,List.sum_cons] at *
    simp only [count,List.countP_cons] at *
    by_cases h : event x <;> simp [h] at * <;> omega

/-- A literal indexed folding candidate implies the joint scalar candidate
whose bad-event count was proved from the universal beta tensor. -/
theorem joint_source_initial_candidate (omega : K) (N D T : Nat)
    (betas : List ((Nat → K) → K)) (sources : List (K → K)) (point : List K)
    (tr : FoldTranscript K) (sizes degrees : Nat → Nat)
    (sizeInitial : sizes 0=N) (degreeInitial : degrees 0=D)
    (candidate : indexedChainCandidate N sizes degrees
      (bindJointSource omega betas sources point tr).roots
      (bindJointSource omega betas sources point tr).challenges
      (bindJointSource omega betas sources point tr).oracles
      (bindJointSource omega betas sources point tr).weights
      (bindJointSource omega betas sources point tr).claims T 0) :
    ∃ p : Poly K,p.DegLt D ∧ T≤consistencyMass ((List.range N).map (fun i => omega^i))
      (fun _ => 1) (fun x => jointBetaSource betas sources x point=p.eval x) := by
  classical
  obtain ⟨p,degree,residual,mass⟩ := candidate
  let trb := bindJointSource omega betas sources point tr
  have cap : ∀ y∈List.range N,globalChainWeight (List.range N) sizes
      (globalRSChainCheck sizes trb.roots trb.challenges trb.oracles) 0 y≤1 := by
    intro y hy
    simpa using global_chain_weight_cap N sizes
      (globalRSChainCheck sizes trb.roots trb.challenges trb.oracles)
      0 sizeInitial (by intro j hj; omega) y (by rw [sizeInitial]; exact List.mem_range.mp hy)
  rw [sizeInitial] at mass
  have agreement := Nat.le_trans mass (unit_cap_mass _ _ _ cap)
  refine ⟨p,by simpa [degreeInitial] using degree,?_⟩
  have transfer : count (List.range N) (fun y => trb.oracles 0 y=p.eval (trb.roots 0^y))=
      consistencyMass ((List.range N).map (fun i => omega^i)) (fun _ => 1)
        (fun x => jointBetaSource betas sources x point=p.eval x) := by
    simp only [unit_mass_count,count,List.countP_map,Function.comp_def]
    rfl
  rw [←transfer]
  exact agreement

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



def jointSourceStrategy (omega : K) (betas : List ((Nat → K) → K)) (sources : List (K → K))
    (raw : List K → List K → FoldTranscript K) (point path : List K) : FoldTranscript K :=
  bindJointSource omega betas sources point (raw point path)

/-- Literal checked-fold acceptance count in the far-source branch. The
initial oracle is the actual fixed beta contraction by definition. No initial
candidate-absence or tensor-identity hypothesis is assumed. Other upstream
checks can only shrink this event; matching their Python transcript still
requires the separate implementation/commitment refinement. -/
theorem joint_source_far_checked_count (sample : List K) (sampleDistinct : sample.Nodup)
    (omega : K) (q N D T rounds queries : Nat) (sizes degrees : Nat → Nat)
    (domainDistinct : ((List.range N).map (fun i => omega^i)).Nodup)
    (sizeInitial : sizes 0=N) (degreeInitial : degrees 0=D)
    (positive : ∀ i≤rounds,0<sizes i)
    (sizeHalves : ∀ i<rounds,sizes i=2*sizes (i+1))
    (degreeHalves : ∀ i<rounds,degrees i=2*degrees (i+1))
    (h2 : (2:K)≠0) (regime : 2*N+D<3*T) (threshold : D-1<T)
    (betas : List ((Nat → K) → K)) (sources : List (K → K))
    (affine : ∀ beta∈betas,∀ point coordinate,coordinate<q → ∀ r,
      beta (gkrSetCoordinate point coordinate r)=
        (1-r)*beta (gkrSetCoordinate point coordinate 0)+r*beta (gkrSetCoordinate point coordinate 1))
    (far : ¬∃ lanes,JointBetaRepresentative ((List.range N).map (fun i => omega^i))
      (fun _ => 1) q D T betas sources lanes)
    (raw : List K → List K → FoldTranscript K)
    (causal : ∀ point∈uniformTuples sample q,∀ path∈uniformTuples sample rounds,∀ i<rounds,
      (jointSourceStrategy omega betas sources raw point path).snapshot N sizes i=
      (jointSourceStrategy omega betas sources raw point (path.take i)).snapshot N sizes i)
    (challengeValues : ∀ point∈uniformTuples sample q,∀ path∈uniformTuples sample rounds,∀ i<rounds,
      (jointSourceStrategy omega betas sources raw point path).challenges i=path[i]?.getD 0) :
    count ((uniformTuples sample q).flatMap (fun point =>
      (functionalFoldSamples sample N rounds queries).map (fun pair => (point,pair))))
      (fun pair => checkedFoldAccept (jointSourceStrategy omega betas sources raw pair.1)
        N sizes degrees T rounds pair.2.1 pair.2.2)*sample.length ≤
      q*max N 2*sample.length^(q-1)*(sample.length^rounds*N^queries)*sample.length+
      sample.length^q*(((List.range rounds).map (fun i => max (sizes (i+1)) 2)).sum*
        sample.length^rounds*N^queries+sample.length^(rounds+1)*(T-1)^queries) := by
  classical
  let domain := (List.range N).map (fun i => omega^i)
  let bad := fun point => ∃ p : Poly K,p.DegLt D ∧
    T≤consistencyMass domain (fun _ => 1) (fun x => jointBetaSource betas sources x point=p.eval x)
  have totalWeight : (domain.map (fun _ => (1:Nat))).sum=N := by
    rw [map_sum_const]
    simp [domain]
  have opening := joint_beta_candidate_far_count domain sample domainDistinct sampleDistinct
    (fun _ => 1) 1 D T q (by intro x hx; omega)
    (by rw [totalWeight]; omega) (by omega) betas sources affine far
  change count (uniformTuples sample q) bad≤q*max domain.length 2*sample.length^(q-1) at opening
  have domainLength : domain.length=N := by simp [domain]
  rw [domainLength] at opening
  let accept : List K → (List K × List Nat) → Prop := fun point pair => checkedFoldAccept
    (jointSourceStrategy omega betas sources raw point) N sizes degrees T rounds pair.1 pair.2
  have good : ∀ point∈uniformTuples sample q,¬bad point →
      count (functionalFoldSamples sample N rounds queries) (accept point)*sample.length≤
        ((List.range rounds).map (fun i => max (sizes (i+1)) 2)).sum*
          sample.length^rounds*N^queries+sample.length^(rounds+1)*(T-1)^queries := by
    intro point hp absent
    apply checked_interactive_unique_fold_soundness sample sampleDistinct
      (jointSourceStrategy omega betas sources raw point) N T rounds queries sizes degrees
      sizeInitial positive sizeHalves degreeHalves h2 (by simpa [degreeInitial] using regime)
      (causal point hp) (challengeValues point hp)
    intro path hpath checks candidate
    exact absent (joint_source_initial_candidate omega N D T betas sources point (raw point path)
      sizes degrees sizeInitial degreeInitial candidate)
  have total := scaled_fiber_bound (uniformTuples sample q) (functionalFoldSamples sample N rounds queries)
    accept bad sample.length _ good
  have innerLength : (functionalFoldSamples sample N rounds queries).length=sample.length^rounds*N^queries := by
    simp only [functionalFoldSamples,List.length_flatMap,List.length_map,uniform_tuples_length,List.length_range]
    rw [map_sum_const,uniform_tuples_length]
  rw [uniform_tuples_length,innerLength] at total
  apply Nat.le_trans total
  exact Nat.add_le_add_right
    (Nat.mul_le_mul_right sample.length (Nat.mul_le_mul_right (sample.length^rounds*N^queries) opening)) _

end NearCompression
