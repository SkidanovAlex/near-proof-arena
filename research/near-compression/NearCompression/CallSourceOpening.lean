import NearCompression.GenericPackingIdentity
import NearCompression.GKRPrivateVectorGlue
import NearCompression.TerminalDAGLayerCertificate
namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

/-- The column weights include ALL high input coordinates, including the
zero-padded region beyond the compiler's private-input capacity. -/
def callSourceFunctional (rowLog columnLog width : Nat) (table : Nat→Nat→K) (point : Nat→K) : K :=
  ((List.range width).map (fun col=>rowEqualityWeight columnLog (fun i=>point (rowLog+i)) col*
    genericRowMLE rowLog (fun row=>table row col) point)).sum

private theorem sum_append (a b : List K) : (a++b).sum=a.sum+b.sum := by
  induction a with
  | nil => simp;grind
  | cons x xs ih => simp only [List.cons_append,List.sum_cons,ih];grind

private theorem cut (f : Nat→K) (width total : Nat) (bound : width≤total)
    (zero : ∀ i,width≤i → f i=0) :
    ((List.range total).map f).sum=((List.range width).map f).sum := by
  induction total with
  | zero =>
    have h : width=0 := by omega
    subst width
    rfl
  | succ total ih =>
    by_cases eq : width=total+1
    · rw [eq]
    · have le : width≤total := by omega
      rw [List.range_succ,List.map_append,sum_append,ih le]
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,zero total le]
      grind

/-- Exact terminal-private MLE to row-table functional, with no assumed
column ownership or unverified truncation of the high challenge bits. -/
theorem call_source_mle (rowLog columnLog width : Nat) (table : Nat→Nat→K) (point : Nat→K)
    (fits : width≤2^columnLog) :
    genericRowMLE (rowLog+columnLog) (genericPackedValues rowLog columnLog width 0 table) point=
      callSourceFunctional rowLog columnLog width table point := by
  rw [generic_packed_mle_identity,←row_equality_dot]
  unfold cubeSum callSourceFunctional
  have truncated:=cut (fun col=>rowEqualityWeight columnLog (fun i=>point (rowLog+i)) col*
    genericRowMLE rowLog (genericPackedColumn columnLog width 0 col table) point) width (2^columnLog) fits (by
      intro col outside
      have zero : genericPackedColumn columnLog width 0 col table=(fun _=>(0:K)) := by
        funext row
        simp [genericPackedColumn,show ¬col<width by omega]
      rw [zero,generic_row_mle_zero]
      grind)
  rw [truncated]
  congr 1
  apply List.map_congr_left
  intro col hc
  have inside:=List.mem_range.mp hc
  have same : genericPackedColumn columnLog width 0 col table=(fun row=>table row col) := by
    funext row
    simp [genericPackedColumn,inside]
  rw [same]

theorem call_source_two_queries (rowLog columnLog width : Nat) (table : Nat→Nat→K)
    (left right : Nat→K) (gamma : K) (fits : width≤2^columnLog) :
    gkrInputFunctional (rowLog+columnLog) left right gamma
      (genericPackedValues rowLog columnLog width 0 table)=
    callSourceFunctional rowLog columnLog width table left+
      gamma*callSourceFunctional rowLog columnLog width table right := by
  unfold gkrInputFunctional
  rw [call_source_mle _ _ _ _ _ fits,call_source_mle _ _ _ _ _ fits]

/-- Public constants are outside the private prefix and the private assignment
is zero after that prefix. These conditions give the exact full GKR input. -/
theorem call_initial_input_split (capacity : Nat) (privateValues constants : Nat→K)
    (privateZero : ∀ i,capacity≤i → privateValues i=0)
    (constantZero : ∀ i,i<capacity → constants i=0) :
    terminalInitialValues capacity privateValues constants=(fun i=>privateValues i+constants i) := by
  funext i
  by_cases hi : i<capacity
  · simp only [terminalInitialValues,hi,ite_true,constantZero i hi];grind
  · simp only [terminalInitialValues,hi,ite_false,privateZero i (by omega)];grind

/-- Padding beyond the private column capacity really is zero, even when
GKR has a larger input dimension because of public constant slots. -/
theorem call_source_outside_private (rowLog columnLog privateColumnLog width : Nat)
    (table : Nat→Nat→K) (fits : width≤2^privateColumnLog) (i : Nat)
    (outside : 2^(rowLog+privateColumnLog)≤i) :
    genericPackedValues rowLog columnLog width 0 table i=0 := by
  have capacity : 2^privateColumnLog*2^rowLog≤i := by
    simpa [Nat.pow_add,Nat.mul_comm] using outside
  have quotient : 2^privateColumnLog≤i/2^rowLog :=
    (Nat.le_div_iff_mul_le (Nat.two_pow_pos rowLog)).mpr capacity
  simp [genericPackedValues,genericPackedColumn,show ¬i/2^rowLog<width by omega]

theorem call_source_initial_split (rowLog columnLog privateColumnLog width : Nat)
    (table : Nat→Nat→K) (constants : Nat→K) (fits : width≤2^privateColumnLog)
    (constantZero : ∀ i,i<2^(rowLog+privateColumnLog) → constants i=0) :
    terminalInitialValues (2^(rowLog+privateColumnLog))
      (genericPackedValues rowLog columnLog width 0 table) constants=
      (fun i=>genericPackedValues rowLog columnLog width 0 table i+constants i) := by
  exact call_initial_input_split _ _ _
    (call_source_outside_private rowLog columnLog privateColumnLog width table fits) constantZero

/-- Incorrect full-input opening iff the constant-subtracted claim is an
incorrect source-table opening. Cryptographic commitment binding is separate. -/
theorem call_source_opening_mismatch (rowLog columnLog width : Nat) (table : Nat→Nat→K)
    (left right constants : Nat→K) (gamma claim : K) (fits : width≤2^columnLog) :
    claim≠gkrInputFunctional (rowLog+columnLog) left right gamma
      (fun i=>genericPackedValues rowLog columnLog width 0 table i+constants i) ↔
    claim-gkrInputFunctional (rowLog+columnLog) left right gamma constants≠
      callSourceFunctional rowLog columnLog width table left+
        gamma*callSourceFunctional rowLog columnLog width table right := by
  have source:=call_source_two_queries rowLog columnLog width table left right gamma fits
  unfold gkrInputFunctional at source ⊢
  rw [generic_row_mle_add,generic_row_mle_add]
  constructor <;> intro h eq <;> apply h <;> grind only
end NearCompression
