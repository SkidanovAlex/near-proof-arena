import NearCompression.WeightedPCSPrefixStrategy
import NearCompression.FunctionalBatchRepresentative

/-! Fixed-representative soundness in the unique-decoding basin. Existence of
one representative close to the committed oracle is still an external premise;
it is not implied by a Merkle root or by honest source generation. -/
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

/-- A wrong functional of a fixed close representative excludes every initial
candidate. The candidate can be selected after seeing the opening point. -/
theorem weighted_replay_representative_no_candidate
    (point : List K) (N D R T : Nat) (omega initial : K)
    (source : Nat → K) (received : K → K) (representative : Poly K)
    (sourceValues : ∀ i<N,source i=received (omega^i))
    (distinct : ((List.range N).map (fun i => omega^i)).Nodup)
    (degree : representative.DegLt D)
    (close : finiteRSMismatches ((List.range N).map (fun i => omega^i))
      received representative.eval≤R)
    (threshold : T≤N) (separation : R+(N-T)+D≤N)
    (wrong : scalarRSResidual (equalityWeights point) representative≠initial) :
    ¬weightedReplayInitialCandidate point N D T omega initial source := by
  classical
  rintro ⟨candidate,hdegree,residual,agreement⟩
  have transfer : count (List.range N) (fun i => source i=candidate.eval (omega^i))=
      count ((List.range N).map (fun i => omega^i)) (fun x => received x=candidate.eval x) := by
    simp only [count,List.countP_map,Function.comp_def]
    apply List.countP_congr
    intro i hi
    simp [sourceValues i (List.mem_range.mp hi)]
  rw [transfer] at agreement
  have partition := finite_rs_agreement_partition
    ((List.range N).map (fun i => omega^i)) received candidate.eval
  have near : finiteRSMismatches ((List.range N).map (fun i => omega^i))
      received candidate.eval≤N-T := by
    simp only [List.length_map,List.length_range] at partition
    omega
  have zero := finite_rs_unique_candidate ((List.range N).map (fun i => omega^i))
    distinct received candidate representative D (N-T) R hdegree degree near close
    (by simp only [List.length_map,List.length_range]; omega)
  have coefficients : ∀ i,candidate.coeff i=representative.coeff i := by
    intro i
    have h := zero i
    rw [Poly.coeff_sub] at h
    grind
  have same := scalar_rs_residual_congr candidate representative (equalityWeights point) coefficients
  exact wrong (same.symm.trans residual)

/-- Incorrect evaluation of a fixed close polynomial has the existing adaptive
fold/query bound, with candidate absence discharged. Source proximity and terminal
authentication remain explicit; this theorem is ideal-interactive, not QROM. -/
theorem weighted_prefix_representative_wrong_count [DecidableEq K]
    (sample : List K) (sampleDistinct : sample.Nodup) (point : List K) (initial : K)
    (p : WeightedPrefixProver K) (roots : Nat→K)
    (N T q R : Nat) (sizes degrees : Nat→Nat)
    (received : K → K) (representative : Poly K)
    (sourceValues : ∀ i<N,p.oracle 0 [] i=received (roots 0^i))
    (distinct : ((List.range N).map (fun i => roots 0^i)).Nodup)
    (degree : representative.DegLt (degrees 0))
    (close : finiteRSMismatches ((List.range N).map (fun i => roots 0^i))
      received representative.eval≤R)
    (threshold : T≤N) (separation : R+(N-T)+degrees 0≤N)
    (wrong : scalarRSResidual (equalityWeights point) representative≠initial)
    (sizeInitial : sizes 0=N) (positive : ∀ i≤point.length,0<sizes i)
    (sizeHalves : ∀ i<point.length,sizes i=2*sizes (i+1))
    (degreeHalves : ∀ i<point.length,degrees i=2*degrees (i+1))
    (h2 : (2:K)≠0) (regime : 2*N+degrees 0<3*T)
    (pointInjective : ∀ i<point.length,∀ a<sizes (i+1),∀ b<sizes (i+1),roots (i+1)^a=roots (i+1)^b → a=b)
    (nonzero : ∀ i<point.length,∀ y<sizes (i+1),roots i^y≠0)
    (squared : ∀ i<point.length,∀ y<sizes (i+1),roots (i+1)^y=roots i^y*roots i^y)
    (negative : ∀ i<point.length,∀ y<sizes (i+1),roots i^(y+sizes (i+1))= -(roots i^y))
    (terminalDegree : 1≤degrees point.length)
    (terminalAuthenticated : ∀ path∈uniformTuples sample point.length,
      weightedReplayCheck point path ((p.messages point.length) path) initial (p.terminal path)=true →
      ∀ y<sizes point.length,p.oracles path point.length y=p.terminal path) :
    count ((uniformTuples sample point.length).flatMap (fun path=>
      (uniformTuples (List.range N) q).map (fun queries=>(path,queries))))
      (fun pair=>weightedReplayAccept point initial (p.messages point.length)
        p.terminal roots p.oracles sizes pair.1 pair.2)*sample.length≤
      ((List.range point.length).map (fun i=>max (sizes (i+1)) 2)).sum*
        sample.length^point.length*N^q+sample.length^(point.length+1)*(T-1)^q := by
  have absent := weighted_replay_representative_no_candidate point N (degrees 0) R T
    (roots 0) initial (p.oracle 0 []) received representative sourceValues distinct degree
    close threshold separation wrong
  have bound := weighted_prefix_no_candidate_count sample sampleDistinct point initial p roots
    N T q sizes degrees sizeInitial positive sizeHalves degreeHalves h2 regime pointInjective
    nonzero squared negative terminalDegree terminalAuthenticated
  simpa only [absent,not_false_eq_true,and_true] using bound

end NearCompression
