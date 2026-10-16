import NearCompression.GKRPrivateVectorGlue
import NearCompression.GenericPackedGridCounting
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

/-- Algebraic form of left-minus-optional-right-minus-constant equations.
Copy descriptors use constant zero; constant descriptors have no right slot. -/
structure CallBatchEquation (K : Type) where
  left : Nat
  right : Option Nat
  value : K

def CallBatchEquation.residual (e : CallBatchEquation K) (v : Nat→K) : K :=
  v e.left-(e.right.map v).getD 0-e.value

def callEquationEntries (w : K) (e : CallBatchEquation K) : List (Nat × K) :=
  (e.left,w)::match e.right with | none=>[] | some i=>[(i,-w)]

def callCompiledEntries (equations : List (K × CallBatchEquation K)) : List (Nat × K) :=
  equations.flatMap (fun pair=>callEquationEntries pair.1 pair.2)

def callCompiledClaim (equations : List (K × CallBatchEquation K)) : K :=
  (equations.map (fun pair=>pair.1*pair.2.value)).sum

def callCompiledDot (capacity : Nat) (entries : List (Nat × K)) (v : Nat→K) : K :=
  ((List.range capacity).map (fun i=>gkrScatter entries i*v i)).sum

private theorem sum_append (a b : List K) : (a++b).sum=a.sum+b.sum := by
  induction a with
  | nil => simp;grind
  | cons x xs ih => simp only [List.cons_append,List.sum_cons,ih];grind

private theorem sum_add (indices : List Nat) (f g : Nat→K) :
    (indices.map (fun i=>f i+g i)).sum=(indices.map f).sum+(indices.map g).sum := by
  induction indices with
  | nil => simp;grind
  | cons i is ih => simp only [List.map_cons,List.sum_cons,ih];grind

private theorem delta_sum (N slot : Nat) (f : Nat→K) :
    ((List.range N).map (fun i=>if i=slot then f i else 0)).sum=
      if slot<N then f slot else 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ,List.map_append,sum_append,ih]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
    by_cases a : slot<N <;> by_cases b : N=slot <;> by_cases c : slot<N+1 <;> simp_all <;> grind

/-- Accumulating repeated slots by addition preserves their whole functional.
No uniqueness-of-slot assumption: shared state cells occur in many equations. -/
theorem call_scatter_dot (capacity : Nat) (entries : List (Nat × K)) (v : Nat→K)
    (bounds : ∀ e∈entries,e.1<capacity) :
    callCompiledDot capacity entries v=(entries.map (fun e=>e.2*v e.1)).sum := by
  induction entries with
  | nil =>
    simp only [callCompiledDot,gkrScatter,List.map_nil,List.sum_nil]
    induction List.range capacity with
    | nil => rfl
    | cons i is ih => simp only [List.map_cons,List.sum_cons];grind
  | cons e es ih =>
    have head:=bounds e (by simp)
    have tail:=ih (by intro x hx;exact bounds x (by simp [hx]))
    have expand : (fun i=>gkrScatter (e::es) i*v i)=
        (fun i=>(if i=e.1 then e.2*v i else 0)+gkrScatter es i*v i) := by
      funext i
      cases e
      simp only [gkrScatter]
      split <;> grind
    unfold callCompiledDot
    rw [expand,sum_add,delta_sum,ite_eq_left head]
    change e.2*v e.1+callCompiledDot capacity es v=_
    rw [tail]
    simp only [List.map_cons,List.sum_cons]

private theorem expanded_entries (equations : List (K × CallBatchEquation K)) (v : Nat→K) :
    ((callCompiledEntries equations).map (fun e=>e.2*v e.1)).sum-callCompiledClaim equations=
      (equations.map (fun pair=>pair.1*pair.2.residual v)).sum := by
  induction equations with
  | nil => simp [callCompiledEntries,callCompiledClaim];grind
  | cons e es ih =>
    have head : ((callEquationEntries e.1 e.2).map (fun x=>x.2*v x.1)).sum-e.1*e.2.value=
        e.1*e.2.residual v := by
      cases hr:e.2.right <;> simp [callEquationEntries,CallBatchEquation.residual,hr] <;> grind
    simp only [callCompiledEntries,List.flatMap_cons,List.map_append,sum_append,
      callCompiledClaim,List.map_cons,List.sum_cons] at ih ⊢
    grind only

/-- Exact coefficient-scattering/claim accumulation identity, for ANY weights
including0and1. Soundness of random weights is a separate theorem below. -/
theorem call_linear_compilation (capacity : Nat) (equations : List (K × CallBatchEquation K))
    (v : Nat→K) (bounds : ∀ e∈callCompiledEntries equations,e.1<capacity) :
    callCompiledDot capacity (callCompiledEntries equations) v-callCompiledClaim equations=
      (equations.map (fun pair=>pair.1*pair.2.residual v)).sum := by
  rw [call_scatter_dot capacity _ v bounds]
  exact expanded_entries equations v

/-- A fixed nonzero residual table cannot vanish often under independent
multilinear-equality batching. Residuals must precede the sampled point. -/
theorem call_residual_batch_zero_count (n index : Nat) (residual : Nat→K)
    (bound : index<2^(n+1)) (wrong : residual index≠0)
    (sample : List K) (distinct : sample.Nodup) :
    count (packedGrid sample (n+1)) (fun point=>packedGridEval (n+1) residual point=0)≤
      (n+1)*sample.length^n := by
  have result:=packed_claim_grid_bad_count n index residual (fun _=>(0:K)) bound wrong sample distinct
  have zero (point : List K) : packedGridEval (n+1) (fun _=>(0:K)) point=0:=generic_row_mle_zero _ _
  simpa only [zero] using result

/-- Equality weights for a full Boolean table. Unused equation positions can
be filled by left-minus-the-same-left with zero constant. -/
def callEqualityBatch (n : Nat) (equations : Nat→CallBatchEquation K) (point : Nat→K) :=
  (List.range (2^n)).map (fun i=>(rowEqualityWeight n point i,equations i))

def callCompiledScore (capacity n : Nat) (equations : Nat→CallBatchEquation K)
    (v point : Nat→K) : K :=
  callCompiledDot capacity (callCompiledEntries (callEqualityBatch n equations point)) v-
    callCompiledClaim (callEqualityBatch n equations point)

theorem call_compiled_score_mle (capacity n : Nat) (equations : Nat→CallBatchEquation K)
    (v point : Nat→K)
    (bounds : ∀ e∈callCompiledEntries (callEqualityBatch n equations point),e.1<capacity) :
    callCompiledScore capacity n equations v point=
      genericRowMLE n (fun i=>(equations i).residual v) point := by
  unfold callCompiledScore
  rw [call_linear_compilation capacity _ v bounds]
  simpa only [callEqualityBatch,List.map_map,Function.comp_def,cubeSum] using
    row_equality_dot n point (fun i=>(equations i).residual v)

/-- The bound applies to the compiled coefficient functional itself, not
merely an abstract residual expression. All equations/values are fixed before
the challenge. This is ideal-field sampling; no Fiat-Shamir/QROM conclusion. -/
theorem call_compiled_batch_zero_count (capacity n index : Nat)
    (equations : Nat→CallBatchEquation K) (v : Nat→K)
    (indexBound : index<2^(n+1)) (wrong : (equations index).residual v≠0)
    (bounds : ∀ point,∀ e∈callCompiledEntries (callEqualityBatch (n+1) equations point),e.1<capacity)
    (sample : List K) (distinct : sample.Nodup) :
    count (packedGrid sample (n+1)) (fun point=>
      callCompiledScore capacity (n+1) equations v (fun i=>point.getD i 0)=0)≤
      (n+1)*sample.length^n := by
  have same : (fun point : List K=>callCompiledScore capacity (n+1) equations v (fun i=>point.getD i 0)=0)=
      (fun point=>packedGridEval (n+1) (fun i=>(equations i).residual v) point=0) := by
    funext point
    rw [call_compiled_score_mle capacity (n+1) equations v _ (bounds _)]
    rfl
  rw [same]
  exact call_residual_batch_zero_count n index (fun i=>(equations i).residual v)
    indexBound wrong sample distinct

end NearCompression
