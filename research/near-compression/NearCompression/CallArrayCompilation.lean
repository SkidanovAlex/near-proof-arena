import NearCompression.CallLinearBatch
namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

/-- Actual sequential writes: the subtraction reads the already updated array.
This matters when the left and right slots coincide. -/
def callArrayUpdate (a : Array K) (w : K) (e : CallBatchEquation K) : Array K :=
  let added:=a.modify e.left (fun x=>x+w)
  match e.right with | none=>added | some i=>added.modify i (fun x=>x-w)

def callArrayRun : List (K × CallBatchEquation K)→Array K×K→Array K×K
  | [],state=>state
  | (w,e)::rest,state=>callArrayRun rest (callArrayUpdate state.1 w e,state.2+w*e.value)

theorem call_array_update_size (a : Array K) (w : K) (e : CallBatchEquation K) :
    (callArrayUpdate a w e).size=a.size := by
  cases h:e.right <;> simp [callArrayUpdate,h]

private theorem modify_read (a : Array K) (slot i : Nat) (f : K→K) (hi : i<a.size) :
    (a.modify slot f).getD i 0=if slot=i then f (a.getD i 0) else a.getD i 0 := by
  simp [Array.getD, hi, Array.getElem_modify]

theorem call_array_update_read (a : Array K) (w : K) (e : CallBatchEquation K)
    (i : Nat) (hi : i<a.size) :
    (callArrayUpdate a w e).getD i 0=a.getD i 0+gkrScatter (callEquationEntries w e) i := by
  cases h:e.right with
  | none =>
    simp only [callArrayUpdate,h,callEquationEntries,gkrScatter]
    rw [modify_read a e.left i _ hi]
    by_cases eq:e.left=i <;> simp_all <;> grind
  | some right =>
    simp only [callArrayUpdate,h,callEquationEntries,gkrScatter]
    rw [modify_read _ right i _ (by simpa using hi),modify_read a e.left i _ hi]
    by_cases left:e.left=i <;> by_cases rhs:right=i <;> simp_all <;> grind

private theorem scatter_append (left right : List (Nat × K)) (i : Nat) :
    gkrScatter (left++right) i=gkrScatter left i+gkrScatter right i := by
  induction left with
  | nil => simp only [List.nil_append,gkrScatter];grind
  | cons entry rest ih =>
    cases entry
    simp only [List.cons_append,gkrScatter,ih]
    grind

/-- Refinement of the sequential array program to mathematical scatter and
constant accumulation. No disjointness premise and no changed read semantics. -/
theorem call_array_run_sound (equations : List (K × CallBatchEquation K)) (a : Array K) (claim : K) :
    (callArrayRun equations (a,claim)).1.size=a.size ∧
    (∀ i,i<a.size → (callArrayRun equations (a,claim)).1.getD i 0=
      a.getD i 0+gkrScatter (callCompiledEntries equations) i) ∧
    (callArrayRun equations (a,claim)).2=claim+callCompiledClaim equations := by
  induction equations generalizing a claim with
  | nil =>
    simp only [callArrayRun,callCompiledEntries,List.flatMap_nil,gkrScatter,
      callCompiledClaim,List.map_nil,List.sum_nil]
    constructor
    · trivial
    · constructor <;> intros <;> grind
  | cons pair rest ih =>
    obtain ⟨size,reads,constant⟩:=ih (callArrayUpdate a pair.1 pair.2) (claim+pair.1*pair.2.value)
    constructor
    · simpa only [callArrayRun,call_array_update_size] using size
    · constructor
      · intro i hi
        have read:=reads i (by simpa only [call_array_update_size] using hi)
        rw [call_array_update_read a pair.1 pair.2 i hi] at read
        simp only [callArrayRun,callCompiledEntries,List.flatMap_cons,scatter_append]
        simpa only [callCompiledEntries] using (show
          (callArrayRun rest (callArrayUpdate a pair.1 pair.2,claim+pair.1*pair.2.value)).1.getD i 0=
          a.getD i 0+(gkrScatter (callEquationEntries pair.1 pair.2) i+gkrScatter (callCompiledEntries rest) i) from by grind only)
      · simp only [callArrayRun,callCompiledClaim,List.map_cons,List.sum_cons] at constant ⊢
        grind only

/-- Starting with zeros yields exactly the compiler coefficients and claim. -/
theorem call_array_zero_compile (equations : List (K × CallBatchEquation K)) (capacity : Nat) :
    (∀ i,i<capacity → (callArrayRun equations (Array.replicate capacity 0,0)).1.getD i 0=
      gkrScatter (callCompiledEntries equations) i) ∧
    (callArrayRun equations (Array.replicate capacity 0,0)).2=callCompiledClaim equations := by
  have result:=call_array_run_sound equations (Array.replicate capacity 0) (0:K)
  constructor
  · intro i hi
    have read:=result.2.1 i (by simpa using hi)
    have zero : (Array.replicate capacity (0:K)).getD i 0 = 0 := by
      simp [Array.getD, hi]
    rw [zero] at read
    grind only
  · have c:=result.2.2;grind only

/-- The actual array accumulator computes the weighted residual functional.
Bounds are essential here: out-of-range writes must not silently drop terms. -/
theorem call_array_functional (capacity : Nat) (equations : List (K × CallBatchEquation K))
    (v : Nat→K) (bounds : ∀ e∈callCompiledEntries equations,e.1<capacity) :
    let compiled:=callArrayRun equations (Array.replicate capacity 0,0)
    ((List.range capacity).map (fun i=>compiled.1.getD i 0*v i)).sum-compiled.2=
      (equations.map (fun pair=>pair.1*pair.2.residual v)).sum := by
  have compiled:=call_array_zero_compile equations capacity
  have entries : (List.range capacity).map (fun i=>
      (callArrayRun equations (Array.replicate capacity 0,0)).1.getD i 0*v i)=
      (List.range capacity).map (fun i=>gkrScatter (callCompiledEntries equations) i*v i) := by
    apply List.map_congr_left
    intro i hi
    rw [compiled.1 i (List.mem_range.mp hi)]
  dsimp only
  rw [entries,compiled.2]
  exact call_linear_compilation capacity equations v bounds

end NearCompression
