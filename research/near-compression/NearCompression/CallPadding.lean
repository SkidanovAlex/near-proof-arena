import NearCompression.CallArrayCompilation
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

/-- A missing equation is a self-copy with zero constant, not a constraint
forcing an actual private cell to zero. -/
def callPaddingEquation : CallBatchEquation K := ⟨0,some 0,0⟩

def callPaddedEquation (equations : List (CallBatchEquation K)) (i : Nat) :=
  equations.getD i callPaddingEquation

def callShortBatch (n : Nat) (equations : List (CallBatchEquation K)) (point : Nat→K) :=
  (List.range equations.length).map (fun i=>(rowEqualityWeight n point i,callPaddedEquation equations i))

theorem call_padding_residual (v : Nat→K) : (callPaddingEquation : CallBatchEquation K).residual v=0 := by
  simp [callPaddingEquation,CallBatchEquation.residual]
  grind

theorem call_padded_residual (equations : List (CallBatchEquation K)) (v : Nat→K)
    (i : Nat) (outside : equations.length≤i) : (callPaddedEquation equations i).residual v=0 := by
  simp [callPaddedEquation,List.getD, List.getElem?_eq_none outside, call_padding_residual]

private theorem sum_append (a b : List K) : (a++b).sum=a.sum+b.sum := by
  induction a with
  | nil => simp;grind
  | cons x xs ih => simp only [List.cons_append,List.sum_cons,ih];grind

private theorem sum_range_cut (f : Nat→K) (length total : Nat)
    (bound : length≤total) (zero : ∀ i,length≤i → f i=0) :
    ((List.range total).map f).sum=((List.range length).map f).sum := by
  induction total with
  | zero =>
    have h : length=0 := by omega
    subst length
    rfl
  | succ total ih =>
    by_cases equal : length=total+1
    · rw [equal]
    · have le : length≤total := by omega
      rw [List.range_succ,List.map_append,sum_append,ih le]
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,zero total le]
      grind

/-- Truncating the challenge-weight list at the real equation count gives
exactly the multilinear extension of the zero-padded residual table. -/
theorem call_short_batch_mle (n : Nat) (equations : List (CallBatchEquation K))
    (v point : Nat→K) (fits : equations.length≤2^n) :
    ((callShortBatch n equations point).map (fun pair=>pair.1*pair.2.residual v)).sum=
      genericRowMLE n (fun i=>(callPaddedEquation equations i).residual v) point := by
  have cut:=sum_range_cut (fun i=>rowEqualityWeight n point i*(callPaddedEquation equations i).residual v)
    equations.length (2^n) fits (by
      intro i hi
      rw [call_padded_residual equations v i hi]
      grind)
  have mle:=row_equality_dot n point (fun i=>(callPaddedEquation equations i).residual v)
  simp only [callShortBatch,List.map_map,Function.comp_def]
  exact cut.symm.trans mle

def callShortArrayScore (capacity n : Nat) (equations : List (CallBatchEquation K))
    (v point : Nat→K) : K :=
  let compiled:=callArrayRun (callShortBatch n equations point) (Array.replicate capacity 0,0)
  ((List.range capacity).map (fun i=>compiled.1.getD i 0*v i)).sum-compiled.2

/-- Composition with the sequential array program; no padded writes are needed. -/
theorem call_short_array_mle (capacity n : Nat) (equations : List (CallBatchEquation K))
    (v point : Nat→K) (fits : equations.length≤2^n)
    (bounds : ∀ e∈callCompiledEntries (callShortBatch n equations point),e.1<capacity) :
    callShortArrayScore capacity n equations v point=
      genericRowMLE n (fun i=>(callPaddedEquation equations i).residual v) point := by
  unfold callShortArrayScore
  rw [call_array_functional capacity _ v bounds]
  exact call_short_batch_mle n equations v point fits

/-- Ideal cancellation bound for the unpadded sequential compiler itself.
The equation list and private vector are fixed before the sampled point. -/
theorem call_short_array_zero_count (capacity n index : Nat)
    (equations : List (CallBatchEquation K)) (v : Nat→K)
    (fits : equations.length≤2^(n+1)) (indexBound : index<equations.length)
    (wrong : (callPaddedEquation equations index).residual v≠0)
    (bounds : ∀ point,∀ e∈callCompiledEntries (callShortBatch (n+1) equations point),e.1<capacity)
    (sample : List K) (distinct : sample.Nodup) :
    count (packedGrid sample (n+1)) (fun point=>
      callShortArrayScore capacity (n+1) equations v (fun i=>point.getD i 0)=0)≤
      (n+1)*sample.length^n := by
  have same : (fun point : List K=>callShortArrayScore capacity (n+1) equations v (fun i=>point.getD i 0)=0)=
      (fun point=>packedGridEval (n+1) (fun i=>(callPaddedEquation equations i).residual v) point=0) := by
    funext point
    rw [call_short_array_mle capacity (n+1) equations v _ fits (bounds _)]
    rfl
  rw [same]
  exact call_residual_batch_zero_count n index _ (by omega) wrong sample distinct
end NearCompression
