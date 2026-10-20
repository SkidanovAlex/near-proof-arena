import NearCompression.AveragedTerminalFailure
namespace NearCompression
open Lean.Grind ZkFormal.Air ZkFormal.Algebra ArenaCore.Security

abbrev LocalChallengePrefix (K : Type) := (K × List K) × List K

def decodedLocalPrefixes {K : Type} (sample : List K) (rowLog : Nat) : List (LocalChallengePrefix K) :=
  (airLocalInitialChallenges sample rowLog).flatMap (fun initial =>
    (uniformTuples sample rowLog).map (fun path => (initial,path)))

def decodedLocalChecks {K : Type} [Field K] (d : Nat)
    (sent : K → List K → List K → Poly K) (claim : K → List K → List K → K)
    (p : LocalChallengePrefix K) : Prop :=
  polynomialSumcheckChecks (d+1) (sent p.1.1 p.1.2) (claim p.1.1 p.1.2) [] p.2

def decodedLocalTerminalCorrect {K : Type} [Field K]
    (rowLog : Nat) (decoded : Nat → Nat → K) (publicValues : List K)
    (residuals : List (AIRBusResidual K × Nat)) (claim : K → List K → List K → K)
    (p : LocalChallengePrefix K) : Prop :=
  claim p.1.1 p.1.2 p.2=whirKernel p.1.2 p.2*
    airBusMixValue (decodedRowEnvironment rowLog decoded p.2) publicValues p.1.1 1 residuals

theorem decoded_local_prefix_count {K : Type} [Field K]
    (sample : List K) (rowLog : Nat) (decoded : Nat → Nat → K) (publicValues : List K)
    (residuals : List (AIRBusResidual K × Nat)) (d : Nat)
    (sent : K → List K → List K → Poly K) (claim : K → List K → List K → K) :
    count (decodedLocalPrefixes sample rowLog) (fun p => decodedLocalChecks d sent claim p ∧
      decodedLocalTerminalCorrect rowLog decoded publicValues residuals claim p)=
    decodedLocalAcceptedCount sample rowLog decoded publicValues residuals d sent claim := by
  classical
  simp only [decodedLocalPrefixes,decodedLocalChecks,decodedLocalTerminalCorrect,decodedLocalAcceptedCount,
    count,List.countP_flatMap,List.countP_map,Function.comp_def]
  congr 1

/-- Compose a local bound with downstream repair while retaining the exact
sum of downstream errors over every mixing/tau/path prefix. The repair bound
is needed only when the local terminal claim is wrong. -/
theorem decoded_local_continuation_split {K R : Type} [Field K]
    (sample : List K) (rowLog : Nat) (decoded : Nat → Nat → K) (publicValues : List K)
    (residuals : List (AIRBusResidual K × Nat)) (d : Nat)
    (sent : K → List K → List K → Poly K) (claim : K → List K → List K → K)
    (continuations : List R) (accept : LocalChallengePrefix K → R → Prop)
    (checks : ∀ p∈decodedLocalPrefixes sample rowLog,∀ r∈continuations,
      accept p r → decodedLocalChecks d sent claim p)
    (repair : Nat) (errors : LocalChallengePrefix K → Nat)
    (wrongTerminal : ∀ p∈decodedLocalPrefixes sample rowLog,
      ¬decodedLocalTerminalCorrect rowLog decoded publicValues residuals claim p →
      count continuations (accept p)*sample.length≤repair+errors p*sample.length) :
    ((decodedLocalPrefixes sample rowLog).map (fun p => count continuations (accept p))).sum*sample.length≤
      decodedLocalAcceptedCount sample rowLog decoded publicValues residuals d sent claim*continuations.length*sample.length+
      (decodedLocalPrefixes sample rowLog).length*repair+
      ((decodedLocalPrefixes sample rowLog).map errors).sum*sample.length := by
  classical
  have split := conditional_scaled_accept_errors (decodedLocalPrefixes sample rowLog) continuations
    (fun p => decodedLocalChecks d sent claim p ∧ decodedLocalTerminalCorrect rowLog decoded publicValues residuals claim p)
    accept sample.length repair errors (by
      intro p hp notGood
      by_cases localChecks : decodedLocalChecks d sent claim p
      · exact wrongTerminal p hp (fun correct => notGood ⟨localChecks,correct⟩)
      · have zero : count continuations (accept p)≤count continuations (fun _ => False) :=
          count_mono_mem _ (fun r hr ha => localChecks (checks p hp r hr ha))
        simp only [count,decide_false,List.countP_false] at zero
        have empty : count continuations (accept p)=0 := Nat.eq_zero_of_le_zero zero
        rw [empty,Nat.zero_mul]
        exact Nat.zero_le _)
  rw [decoded_local_prefix_count] at split
  exact split

/-- Actual invalid decoded-trace local budget plus downstream repair and one
joint error total. No per-rowpoint PCS estimate is assumed. The joint error
bound must still be instantiated on the matching full sample space. -/
theorem decoded_invalid_trace_continuation_budget {K R : Type} [Field K]
    (sample : List K) (distinct : sample.Nodup) (decoded : Nat → Nat → K) (publicValues : List K)
    (source : List Expr) (auxiliary : List (BusProgramFormula K))
    (residuals : List (AIRBusResidual K × Nat))
    (order : residuals.map Prod.fst=source.map Sum.inl++auxiliary.map Sum.inr)
    (d n row lane : Nat) (positive : 0<source.length+auxiliary.length) (rowBound : row<2^(n+1))
    (wrong : (airCombinedRowResiduals (decodedTableTrace (n+1) decoded) 0 publicValues source auxiliary row).getD lane 0≠0)
    (sourceDegrees : ∀ e∈source,e.degree≤d) (auxDegrees : ∀ e∈auxiliary,busFormulaDegree e≤d)
    (sent : K → List K → List K → Poly K) (claim : K → List K → List K → K)
    (initialZero : ∀ mixing tau,claim mixing tau []=0)
    (continuations : List R) (accept : LocalChallengePrefix K → R → Prop)
    (checks : ∀ p∈decodedLocalPrefixes sample (n+1),∀ r∈continuations,accept p r → decodedLocalChecks d sent claim p)
    (repair pcsBudget : Nat) (errors : LocalChallengePrefix K → Nat)
    (wrongTerminal : ∀ p∈decodedLocalPrefixes sample (n+1),
      ¬decodedLocalTerminalCorrect (n+1) decoded publicValues residuals claim p →
      count continuations (accept p)*sample.length≤repair+errors p*sample.length)
    (jointErrors : ((decodedLocalPrefixes sample (n+1)).map errors).sum*sample.length≤pcsBudget) :
    ((decodedLocalPrefixes sample (n+1)).map (fun p => count continuations (accept p))).sum*sample.length≤
      ((source.length+auxiliary.length-1+(n+1)+(d+1)*(n+1))*sample.length^(2*(n+1)+1))*continuations.length+
      (decodedLocalPrefixes sample (n+1)).length*repair+pcsBudget := by
  have split := decoded_local_continuation_split sample (n+1) decoded publicValues residuals d sent claim
    continuations accept checks repair errors wrongTerminal
  have localBound := decoded_local_invalid_trace_count sample distinct decoded publicValues source auxiliary residuals
    order d n row lane positive rowBound wrong sourceDegrees auxDegrees sent claim initialZero
  have scaled := Nat.mul_le_mul_right continuations.length localBound
  rw [Nat.mul_right_comm _ continuations.length sample.length] at split
  exact Nat.le_trans split (Nat.add_le_add (Nat.add_le_add_right scaled _) jointErrors)

end NearCompression
