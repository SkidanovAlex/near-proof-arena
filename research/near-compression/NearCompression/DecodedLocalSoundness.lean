import NearCompression.DecodedTraceSemantics
import NearCompression.AirLocalSoundness
import NearCompression.ChronologicalChallengeCount
namespace NearCompression
open Lean.Grind ZkFormal.Air ZkFormal.Algebra ArenaCore.Security

/-- Local acceptance expressed using the compiler accumulator on decoded
columns. The terminal equality is still a semantic/authentication obligation. -/
noncomputable def decodedLocalAcceptedCount {K : Type} [Field K]
    (sample : List K) (rowLog : Nat) (decoded : Nat → Nat → K) (publicValues : List K)
    (residuals : List (AIRBusResidual K × Nat)) (d : Nat)
    (sent : K → List K → List K → Poly K) (claim : K → List K → List K → K) : Nat :=
  ((airLocalInitialChallenges sample rowLog).map (fun initial =>
    count (uniformTuples sample rowLog) (fun path =>
      polynomialSumcheckChecks (d+1) (sent initial.1 initial.2) (claim initial.1 initial.2) [] path ∧
      claim initial.1 initial.2 path=whirKernel initial.2 path*
        airBusMixValue (decodedRowEnvironment rowLog decoded path) publicValues initial.1 1 residuals))).sum

theorem decoded_local_accepted_count_eq {K : Type} [Field K]
    (sample : List K) (rowLog : Nat) (decoded : Nat → Nat → K) (publicValues : List K)
    (source : List Expr) (auxiliary : List (BusProgramFormula K))
    (residuals : List (AIRBusResidual K × Nat))
    (order : residuals.map Prod.fst=source.map Sum.inl++auxiliary.map Sum.inr) (d : Nat)
    (sent : K → List K → List K → Poly K) (claim : K → List K → List K → K) :
    decodedLocalAcceptedCount sample rowLog decoded publicValues residuals d sent claim=
      airLocalAcceptedCount sample (decodedTableTrace rowLog decoded) 0 publicValues source auxiliary d sent claim := by
  unfold decodedLocalAcceptedCount airLocalAcceptedCount
  change (List.map _ (airLocalInitialChallenges sample rowLog)).sum=(List.map _ (airLocalInitialChallenges sample rowLog)).sum
  congr 1
  apply List.map_congr_left
  intro initial _
  have value (path : List K) (member : path∈uniformTuples sample rowLog) :
      whirKernel initial.2 path*airBusMixValue (decodedRowEnvironment rowLog decoded path) publicValues initial.1 1 residuals=
      airTraceWeightedValue (decodedTableTrace rowLog decoded) 0 publicValues source auxiliary initial.1 initial.2 path := by
    rw [decoded_combined_mixture rowLog decoded publicValues path
      (uniform_tuple_member_length sample rowLog path member) source auxiliary residuals order]
    rfl
  apply Nat.le_antisymm
  · apply count_mono_mem
    intro path member accepted
    exact ⟨accepted.1,accepted.2.trans (value path member)⟩
  · apply count_mono_mem
    intro path member accepted
    exact ⟨accepted.1,accepted.2.trans (value path member).symm⟩

/-- Initial batching and all adaptive sumcheck rounds, with the terminal
check stated in terms of the decoded compiler accumulator. Strategies may
depend on initial mixing/tau and all prior round challenges. -/
theorem decoded_local_invalid_trace_count {K : Type} [Field K]
    (sample : List K) (distinct : sample.Nodup)
    (decoded : Nat → Nat → K) (publicValues : List K)
    (source : List Expr) (auxiliary : List (BusProgramFormula K))
    (residuals : List (AIRBusResidual K × Nat))
    (order : residuals.map Prod.fst=source.map Sum.inl++auxiliary.map Sum.inr)
    (d n row lane : Nat) (positive : 0<source.length+auxiliary.length)
    (rowBound : row<2^(n+1))
    (wrong : (airCombinedRowResiduals (decodedTableTrace (n+1) decoded) 0 publicValues source auxiliary row).getD lane 0≠0)
    (sourceDegrees : ∀ e∈source,e.degree≤d) (auxDegrees : ∀ e∈auxiliary,busFormulaDegree e≤d)
    (sent : K → List K → List K → Poly K) (claim : K → List K → List K → K)
    (initialZero : ∀ mixing tau,claim mixing tau []=0) :
    decodedLocalAcceptedCount sample (n+1) decoded publicValues residuals d sent claim*sample.length≤
      (source.length+auxiliary.length-1+(n+1)+(d+1)*(n+1))*sample.length^(2*(n+1)+1) := by
  rw [decoded_local_accepted_count_eq sample (n+1) decoded publicValues source auxiliary residuals order]
  exact air_local_invalid_trace_count sample distinct (decodedTableTrace (n+1) decoded) 0
    publicValues source auxiliary d n row lane rfl positive rowBound wrong sourceDegrees auxDegrees sent claim initialZero

/-- Exact local experiment count for an arbitrary verifier event. -/
noncomputable def decodedLocalEventCount {K : Type} [Field K]
    (sample : List K) (rowLog : Nat) (event : (K × List K) → List K → Prop) : Nat :=
  ((airLocalInitialChallenges sample rowLog).map (fun initial =>
    count (uniformTuples sample rowLog) (event initial))).sum

/-- Acceptance splits into the bounded honest-terminal event and accepted
terminal mismatch on the same experiment. No independence is assumed. -/
theorem decoded_local_acceptance_split {K : Type} [Field K]
    (sample : List K) (rowLog : Nat) (decoded : Nat → Nat → K) (publicValues : List K)
    (residuals : List (AIRBusResidual K × Nat)) (d : Nat)
    (sent : K → List K → List K → Poly K) (claim : K → List K → List K → K)
    (accept : (K × List K) → List K → Prop)
    (checks : ∀ initial∈airLocalInitialChallenges sample rowLog,∀ path∈uniformTuples sample rowLog,
      accept initial path → polynomialSumcheckChecks (d+1) (sent initial.1 initial.2) (claim initial.1 initial.2) [] path) :
    decodedLocalEventCount sample rowLog accept≤
      decodedLocalAcceptedCount sample rowLog decoded publicValues residuals d sent claim+
      decodedLocalEventCount sample rowLog (fun initial path => accept initial path ∧
        claim initial.1 initial.2 path≠whirKernel initial.2 path*
          airBusMixValue (decodedRowEnvironment rowLog decoded path) publicValues initial.1 1 residuals) := by
  classical
  unfold decodedLocalEventCount decodedLocalAcceptedCount
  let terminal := fun (initial : K × List K) path =>
    claim initial.1 initial.2 path=whirKernel initial.2 path*
      airBusMixValue (decodedRowEnvironment rowLog decoded path) publicValues initial.1 1 residuals
  have each (initial : K × List K) (hi : initial∈airLocalInitialChallenges sample rowLog) :
      count (uniformTuples sample rowLog) (accept initial)≤
      count (uniformTuples sample rowLog) (fun path =>
        polynomialSumcheckChecks (d+1) (sent initial.1 initial.2) (claim initial.1 initial.2) [] path ∧ terminal initial path)+
      count (uniformTuples sample rowLog) (fun path => accept initial path ∧ ¬terminal initial path) := by
    apply Nat.le_trans (count_mono_mem _ (fun path hp ha => ?_)) (count_or_le _ _ _)
    by_cases ht : terminal initial path
    · exact Or.inl ⟨checks initial hi path hp ha,ht⟩
    · exact Or.inr ⟨ha,ht⟩
  clear checks
  generalize airLocalInitialChallenges sample rowLog=initials at *
  induction initials with
  | nil => simp
  | cons initial rest ih =>
    have head := each initial (by simp)
    have tail := ih (fun a ha => each a (by simp [ha]))
    simp only [List.map_cons,List.sum_cons]
    dsimp only [terminal] at head tail
    simp only [ne_eq] at *
    omega

end NearCompression
