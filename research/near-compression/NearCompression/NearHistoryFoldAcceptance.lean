import NearCompression.NearFunctionalFoldAcceptance
import NearCompression.ChronologicalChallengeCount
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

/-- Near-case checked acceptance on the full earlier-history/PCS coordinate
space. One fixed source tuple represents all history-dependent weights.
A wrong initial claim is part of the counted event, not assumed for every
history. This uses independent ideal draws and explicit oracle authentication. -/
theorem near_history_fold_acceptance_count [DecidableEq K]
    (sample : List K) (sampleDistinct : sample.Nodup)
    (earlier n N T queries : Nat) (sizes degrees : Nat → Nat) (roots : Nat → K)
    (tables : List K → List (Nat → K)) (sources : List (K → K)) (lanes : List (Poly K))
    (domainDistinct : ((List.range N).map (fun i => roots 0^i)).Nodup)
    (representative : SharedFunctionalRepresentative
      ((List.range N).map (fun i => roots 0^i)) n (degrees 0) (N-T)
      tables sources lanes)
    (threshold : T≤N) (separation : 2*(N-T)+degrees 0≤N)
    (sent : List K → List K → Poly K) (claim : List K → List K → K)
    (provers : List K → List K → WeightedPrefixProver K)
    (sourceValues : ∀ h z,∀ i<N,(provers h z).oracle 0 [] i=
      weightedVirtualOracle (functionalBatchCoefficients n (tables h) (fun j => z.getD j 0)) sources (roots 0^i))
    (sizeInitial : sizes 0=N) (positive : ∀ i≤n,0<sizes i)
    (sizeHalves : ∀ i<n,sizes i=2*sizes (i+1))
    (degreeHalves : ∀ i<n,degrees i=2*degrees (i+1))
    (h2 : (2:K)≠0) (regime : 2*N+degrees 0<3*T)
    (pointInjective : ∀ i<n,∀ a<sizes (i+1),∀ b<sizes (i+1),roots (i+1)^a=roots (i+1)^b → a=b)
    (nonzero : ∀ i<n,∀ y<sizes (i+1),roots i^y≠0)
    (squared : ∀ i<n,∀ y<sizes (i+1),roots (i+1)^y=roots i^y*roots i^y)
    (negative : ∀ i<n,∀ y<sizes (i+1),roots i^(y+sizes (i+1))= -(roots i^y))
    (terminalDegree : 1≤degrees n)
    (terminalAuthenticated : ∀ h z,∀ path∈uniformTuples sample n,
      weightedReplayCheck z path ((provers h z).messages n path)
        (claim h z) ((provers h z).terminal path)=true →
      ∀ y<sizes n,(provers h z).oracles path n y=(provers h z).terminal path) :
    let inner := (uniformTuples sample n).flatMap (fun path =>
      (uniformTuples (List.range N) queries).map (fun qs => (path,qs)))
    count ((uniformTuples sample (earlier+n)).flatMap (fun z => inner.map (fun pair => (z,pair))))
      (fun pair =>
        let h := pair.1.take earlier
        let z := pair.1.drop earlier
        claim h []≠coefficientTableFunctional n (tables h) lanes ∧
        weightedSumcheckChecks (sent h) (claim h) [] z ∧
        weightedReplayAccept z (claim h z) ((provers h z).messages n)
          (provers h z).terminal roots (provers h z).oracles sizes pair.2.1 pair.2.2)*sample.length≤
      sample.length^earlier*((2*n)*sample.length^n*inner.length+
        (uniformTuples sample n).length*(((List.range n).map (fun i => max (sizes (i+1)) 2)).sum*
          sample.length^n*N^queries+sample.length^(n+1)*(T-1)^queries)) := by
  classical
  dsimp only
  apply chronological_suffix_count sample earlier n
    ((uniformTuples sample n).flatMap (fun path =>
      (uniformTuples (List.range N) queries).map (fun qs => (path,qs))))
    (fun h z pair => claim h []≠coefficientTableFunctional n (tables h) lanes ∧
      weightedSumcheckChecks (sent h) (claim h) [] z ∧
      weightedReplayAccept z (claim h z) ((provers h z).messages n)
        (provers h z).terminal roots (provers h z).oracles sizes pair.1 pair.2) sample.length _
  intro h hh
  by_cases wrong : claim h []≠coefficientTableFunctional n (tables h) lanes
  · have shared : SharedFunctionalRepresentative
        ((List.range N).map (fun i => roots 0^i)) n (degrees 0) (N-T)
        (fun _ : Unit => tables h) sources lanes :=
      ⟨representative.1,representative.2.1,fun _ => representative.2.2.1 h,
        fun _ => representative.2.2.2 h⟩
    have bound := near_functional_fold_acceptance_count sample sampleDistinct n N T queries
      sizes degrees roots (tables h) sources lanes domainDistinct shared threshold separation
      (sent h) (claim h) wrong (provers h) (sourceValues h) sizeInitial positive sizeHalves
      degreeHalves h2 regime pointInjective nonzero squared negative terminalDegree
      (terminalAuthenticated h)
    apply Nat.le_trans _ bound
    apply Nat.mul_le_mul_right sample.length
    exact count_mono _ (fun pair accepted => accepted.2)
  · simp [wrong,count]

end NearCompression
