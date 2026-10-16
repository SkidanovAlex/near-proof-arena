import NearCompression.VirtualFoldTransfer
import NearCompression.WHIRRoundRecurrence
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

/-- Verifier-computed arbitrary weights; only previous challenges are read. -/
def virtualPrefixWeights (initial : List K) (history : List K) : Nat→List K
  | 0=>initial
  | i+1=>generalFoldWeights (monomialEvenCoefficients (virtualPrefixWeights initial history i))
      (monomialOddCoefficients (virtualPrefixWeights initial history i)) (history.getD i 0)

def virtualPrefixSent (prover : Nat→List K→WhirQuadratic K) (history : List K) (i : Nat) : Poly K :=
  let sent:=prover i (history.take i)
  Poly.mk [sent.c0,sent.c1,sent.c2]

def virtualPrefixTranscript (sizes : Nat→Nat) (roots : Nat→K) (source : Nat→K)
    (weights : List K) (claim : K) (prover : Nat→List K→WhirQuadratic K)
    (history : List K) : GeneralFoldTranscript K where
  roots:=roots
  challenges:=fun i=>history.getD i 0
  oracles:=virtualFoldOracles sizes roots (fun i=>history.getD i 0) source
  weights:=virtualPrefixWeights weights history
  claims:=fun i=>match i with | 0=>claim | j+1=>(virtualPrefixSent prover history j).eval (history.getD j 0)
  evenWeights:=fun i=>monomialEvenCoefficients (virtualPrefixWeights weights history i)
  oddWeights:=fun i=>monomialOddCoefficients (virtualPrefixWeights weights history i)
  sent:=virtualPrefixSent prover history
  terminal:=[]

private theorem prefix_get (history : List K) {j i : Nat} (h : j<i) :
    (history.take i).getD j 0=history.getD j 0 := by simp [List.getD,h]

theorem virtual_weights_prefix (weights history : List K) (i j : Nat) (h : j≤i) :
    virtualPrefixWeights weights (history.take i) j=virtualPrefixWeights weights history j := by
  induction j with
  | zero=>rfl
  | succ j ih=>rw [virtualPrefixWeights,virtualPrefixWeights,ih (by omega),prefix_get history (by omega)]

theorem virtual_oracles_prefix (sizes : Nat→Nat) (roots : Nat→K) (source : Nat→K)
    (history : List K) (i j : Nat) (h : j≤i) :
    virtualFoldOracles sizes roots (fun k=>(history.take i).getD k 0) source j=
      virtualFoldOracles sizes roots (fun k=>history.getD k 0) source j := by
  induction j with
  | zero=>rfl
  | succ j ih=>rw [virtualFoldOracles,virtualFoldOracles,ih (by omega),prefix_get history (by omega)]

/-- The actual snapshot is prefix-causal by construction, including its
transcript-generated query measure. No causality premise is supplied. -/
theorem virtual_snapshot_prefix (sizes : Nat→Nat) (roots : Nat→K) (source : Nat→K)
    (weights : List K) (claim : K) (prover : Nat→List K→WhirQuadratic K)
    (history : List K) (N i : Nat) :
    (virtualPrefixTranscript sizes roots source weights claim prover history).snapshot N sizes i=
      (virtualPrefixTranscript sizes roots source weights claim prover (history.take i)).snapshot N sizes i := by
  have checks : globalRSChainCheck sizes roots (fun k=>history.getD k 0)
      (virtualFoldOracles sizes roots (fun k=>history.getD k 0) source)=
      globalRSChainCheck sizes roots (fun k=>(history.take i).getD k 0)
        (virtualFoldOracles sizes roots (fun k=>(history.take i).getD k 0) source) := by
    funext j y
    apply propext
    exact ⟨fun _=>virtual_fold_consistency _ _ _ _ _ _,fun _=>virtual_fold_consistency _ _ _ _ _ _⟩
  simp only [GeneralFoldTranscript.snapshot,virtualPrefixTranscript,virtual_weights_prefix weights history i i (Nat.le_refl i),
    virtual_oracles_prefix sizes roots source history i i (Nat.le_refl i),virtualPrefixSent,List.take_take,Nat.min_self,checks]

private theorem adaptive_bounds_from_index {A : Type} (sample : List A)
    (bad : List A→A→Prop) (error : Nat→Nat) (history : List A) (remaining : Nat)
    (bound : ∀ h : List A,h.length<history.length+remaining→count sample (bad h)≤error h.length) :
    AdaptiveRoundBounds sample bad history ((List.range remaining).map (fun i=>error (history.length+i))) := by
  induction remaining generalizing history with
  | zero=>trivial
  | succ n ih=>
    rw [List.range_succ_eq_map]
    simp only [List.map_cons,List.map_map,Nat.add_zero]
    constructor
    · exact bound history (by omega)
    · intro a ha
      have next:=ih (history++[a]) (by
        intro h hh;apply bound h
        simp only [List.length_append,List.length_singleton] at hh
        omega)
      simpa [List.length_append,Function.comp_def,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using next

/-- Adaptive bad-path count for the literal virtual-prefix strategy. Source
and initial weights are arbitrary; quadratics may adapt to every prior draw. -/
theorem virtual_prefix_bad_path_bound
    (sample : List K) (distinct : sample.Nodup) (N T rounds : Nat) (sizes degrees : Nat→Nat)
    (roots : Nat→K) (source : Nat→K) (weights : List K) (claim : K)
    (prover : Nat→List K→WhirQuadratic K)
    (initial : sizes 0=N) (positive : ∀ i≤rounds,0<sizes i)
    (halves : ∀ i<rounds,sizes i=2*sizes (i+1))
    (degreeHalves : ∀ i<rounds,degrees i=2*degrees (i+1))
    (injective : ∀ i<rounds,∀ a<sizes (i+1),∀ b<sizes (i+1),roots (i+1)^a=roots (i+1)^b→a=b)
    (regime : 2*N+degrees 0<3*T) :
    count (uniformTuples sample rounds)
      (adaptivePathBad (generalFoldHistoryBad (virtualPrefixTranscript sizes roots source weights claim prover)
        N sizes degrees T) [])*sample.length≤
      ((List.range rounds).map (fun i=>max (sizes (i+1)) 2)).sum*sample.length^rounds := by
  let bad:=generalFoldHistoryBad (virtualPrefixTranscript sizes roots source weights claim prover) N sizes degrees T
  have localBound : ∀ history : List K,history.length<rounds→count sample (bad history)≤max (sizes (history.length+1)) 2 := by
    intro history hh
    apply general_global_chain_bad_count sample distinct N sizes degrees roots (fun i=>history.getD i 0)
      (virtualFoldOracles sizes roots (fun i=>history.getD i 0) source) history.length T initial
      (fun j hj=>positive j (by omega)) (fun j hj=>halves j (by omega))
      (fun j hj=>degreeHalves j (by omega)) (injective history.length hh)
    · exact Poly.degLt_length _
    · exact regime
  have bounds:=adaptive_bounds_from_index sample bad (fun i=>max (sizes (i+1)) 2) [] rounds (by simpa using localBound)
  have result:=adaptive_round_failure_budget sample bad []
    ((List.range rounds).map (fun i=>max (sizes (i+1)) 2)) (by simpa using bounds)
  rw [←adaptive_failure_leaves_exact] at result
  simpa only [List.length_map,List.length_range] using result
private theorem path_no_bad {A : Type} (bad : List A → A → Prop)
    (history path : List A) (default : A) (good : ¬adaptivePathBad bad history path) :
    ∀ i<path.length,¬bad (history++path.take i) (path[i]?.getD default) := by
  induction path generalizing history with
  | nil => simp
  | cons a rest ih =>
    intro i hi
    have first : ¬bad history a := fun h => good (Or.inl h)
    have tail : ¬adaptivePathBad bad (history++[a]) rest := fun h => good (Or.inr h)
    cases i with
    | zero => simpa using first
    | succ i =>
      have h := ih (history++[a]) tail i (by simpa using hi)
      simpa [List.take_succ_cons,List.append_assoc] using h


/-- The counted history event covers the concrete completed transcript's
bad transitions; this uses derived snapshot causality, not an extra premise. -/
theorem virtual_prefix_no_bad_transitions (sizes degrees : Nat→Nat) (roots : Nat→K) (source : Nat→K)
    (weights : List K) (claim : K) (prover : Nat→List K→WhirQuadratic K)
    (path : List K) (N T : Nat)
    (good : ¬adaptivePathBad (generalFoldHistoryBad
      (virtualPrefixTranscript sizes roots source weights claim prover) N sizes degrees T) [] path) :
    ∀ i<path.length,¬((virtualPrefixTranscript sizes roots source weights claim prover path).snapshot N sizes i).bad
      (sizes (i+1)) (degrees (i+1)) T (path.getD i 0) := by
  have absent:=path_no_bad (generalFoldHistoryBad
    (virtualPrefixTranscript sizes roots source weights claim prover) N sizes degrees T) [] path (0:K) good
  intro i hi
  have h:=absent i hi
  have length : (path.take i).length=i := by simp [List.length_take,Nat.min_eq_left (by omega : i≤path.length)]
  rw [virtual_snapshot_prefix]
  simpa [generalFoldHistoryBad,length,List.getD] using h

end NearCompression
