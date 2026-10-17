import NearCompression.JointSourceAcceptance
import NearCompression.CloseFamilySumcheck
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

/-- A wrong functional of one shared representative bounds actual checked
sumcheck plus adaptive folding acceptance. The entire folding strategy can
depend on the preceding sumcheck challenges. Terminal authentication and
ideal independent sampling are explicit. -/
theorem near_functional_fold_acceptance_count [DecidableEq K]
    (sample : List K) (sampleDistinct : sample.Nodup)
    (n N T queries : Nat) (sizes degrees : Nat → Nat) (roots : Nat → K)
    (tables : List (Nat → K)) (sources : List (K → K)) (lanes : List (Poly K))
    (domainDistinct : ((List.range N).map (fun i => roots 0^i)).Nodup)
    (representative : SharedFunctionalRepresentative
      ((List.range N).map (fun i => roots 0^i)) n (degrees 0) (N-T)
      (fun _ : Unit => tables) sources lanes)
    (threshold : T≤N) (separation : 2*(N-T)+degrees 0≤N)
    (sent : List K → Poly K) (claim : List K → K)
    (wrong : claim []≠coefficientTableFunctional n tables lanes)
    (provers : List K → WeightedPrefixProver K)
    (sourceValues : ∀ z,∀ i<N,(provers z).oracle 0 [] i=
      weightedVirtualOracle (functionalBatchCoefficients n tables (fun j => z.getD j 0)) sources (roots 0^i))
    (sizeInitial : sizes 0=N) (positive : ∀ i≤n,0<sizes i)
    (sizeHalves : ∀ i<n,sizes i=2*sizes (i+1))
    (degreeHalves : ∀ i<n,degrees i=2*degrees (i+1))
    (h2 : (2:K)≠0) (regime : 2*N+degrees 0<3*T)
    (pointInjective : ∀ i<n,∀ a<sizes (i+1),∀ b<sizes (i+1),roots (i+1)^a=roots (i+1)^b → a=b)
    (nonzero : ∀ i<n,∀ y<sizes (i+1),roots i^y≠0)
    (squared : ∀ i<n,∀ y<sizes (i+1),roots (i+1)^y=roots i^y*roots i^y)
    (negative : ∀ i<n,∀ y<sizes (i+1),roots i^(y+sizes (i+1))= -(roots i^y))
    (terminalDegree : 1≤degrees n)
    (terminalAuthenticated : ∀ z,∀ path∈uniformTuples sample n,
      weightedReplayCheck z path ((provers z).messages n path)
        (claim z) ((provers z).terminal path)=true →
      ∀ y<sizes n,(provers z).oracles path n y=(provers z).terminal path) :
    let outer := uniformTuples sample n
    let inner := (uniformTuples sample n).flatMap (fun path =>
      (uniformTuples (List.range N) queries).map (fun qs => (path,qs)))
    count (outer.flatMap (fun z => inner.map (fun pair => (z,pair))))
      (fun pair => weightedSumcheckChecks sent claim [] pair.1 ∧
        weightedReplayAccept pair.1 (claim pair.1) ((provers pair.1).messages n)
          (provers pair.1).terminal roots (provers pair.1).oracles sizes pair.2.1 pair.2.2)*sample.length≤
      (2*n)*sample.length^n*inner.length+
      outer.length*(((List.range n).map (fun i => max (sizes (i+1)) 2)).sum*
        sample.length^n*N^queries+sample.length^(n+1)*(T-1)^queries) := by
  classical
  dsimp only
  let domain := (List.range N).map (fun i => roots 0^i)
  let good := fun z => weightedSumcheckChecks sent claim [] z ∧
    ∃ candidate : Poly K,candidate.DegLt (degrees 0) ∧
      scalarRSResidual (equalityWeights z) candidate=claim z ∧
      T≤count domain (fun x => weightedVirtualOracle
        (functionalBatchCoefficients n tables (fun i => z.getD i 0)) sources x=candidate.eval x)
  have nearBound := close_family_sumcheck_residual_count domain sample domainDistinct sampleDistinct
    n (degrees 0) T tables sources lanes
    (by simpa [domain] using representative) (by simpa [domain] using threshold)
    (by simpa [domain] using separation) sent claim wrong
  let inner := (uniformTuples sample n).flatMap (fun path =>
    (uniformTuples (List.range N) queries).map (fun qs => (path,qs)))
  have tupleLength : ∀ m,∀ z∈uniformTuples sample m,z.length=m := by
    intro m
    induction m with
    | zero => simp [uniformTuples]
    | succ m ih =>
      intro z hz
      simp only [uniformTuples,List.mem_flatMap,List.mem_map] at hz
      obtain ⟨r,hr,rest,hrest,rfl⟩ := hz
      simp [ih rest hrest]
  have bound := finite_product_acceptance_budget (uniformTuples sample n) inner
    (fun z pair => weightedSumcheckChecks sent claim [] z ∧
      weightedReplayAccept z (claim z) ((provers z).messages n) (provers z).terminal roots
        (provers z).oracles sizes pair.1 pair.2) good sample.length
    (((List.range n).map (fun i => max (sizes (i+1)) 2)).sum*
      sample.length^n*N^queries+sample.length^(n+1)*(T-1)^queries) (by
    intro z hz absent
    have length := tupleLength n z hz
    by_cases checked : weightedSumcheckChecks sent claim [] z
    · have noCandidate : ¬weightedReplayInitialCandidate z N (degrees 0) T
          (roots 0) (claim z) ((provers z).oracle 0 []) := by
        rintro ⟨candidate,degree,residual,agreement⟩
        apply absent
        refine ⟨checked,candidate,degree,residual,?_⟩
        have transfer : count (List.range N)
            (fun i => (provers z).oracle 0 [] i=candidate.eval (roots 0^i))=
            count domain (fun x => weightedVirtualOracle
              (functionalBatchCoefficients n tables (fun j => z.getD j 0)) sources x=candidate.eval x) := by
          simp only [domain,count,List.countP_map,Function.comp_def]
          apply List.countP_congr
          intro i hi
          simp [sourceValues z i (List.mem_range.mp hi)]
        rwa [transfer] at agreement
      have pcs := weighted_prefix_no_candidate_count sample sampleDistinct z (claim z)
        (provers z) roots N T queries sizes degrees sizeInitial
        (by simpa [length] using positive) (by simpa [length] using sizeHalves)
        (by simpa [length] using degreeHalves) h2 regime
        (by simpa [length] using pointInjective) (by simpa [length] using nonzero)
        (by simpa [length] using squared) (by simpa [length] using negative)
        (by simpa [length] using terminalDegree)
        (by simpa [length] using terminalAuthenticated z)
      simpa only [length,noCandidate,not_false_eq_true,and_true,checked,true_and] using pcs
    · simp [count,checked])
  apply Nat.le_trans bound
  have scaled := Nat.mul_le_mul_right inner.length nearBound
  have rearrange : count (uniformTuples sample n) good*inner.length*sample.length=
      count (uniformTuples sample n) good*sample.length*inner.length := by ac_rfl
  rw [rearrange]
  exact Nat.add_le_add_right scaled _

end NearCompression
