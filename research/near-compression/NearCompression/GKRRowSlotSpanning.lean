import NearCompression.GKRCommonInputBoundary
import NearCompression.PackedDualMobiusWeights

/-! Universal rowpoint/current-slot separation. A fixed table is quantified
before all challenges. Theorems here identify the universal family needed by
extraction; they do not assert that a sampled transcript establishes it. -/
namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

/-- A single table's private current/next block, with p low column bits and
one high current/next flag. This is the block layout of compile_terminal. -/
def gkrTableSlots (n p : Nat) (table : Nat → Nat → K) (rowpoint : Nat → K)
    (slot : Nat) : K :=
  if slot<2^p then genericRowMLE n (fun row => table row slot) rowpoint
  else genericRowNextMLE n (fun row => table row (slot-2^p)) rowpoint

/-- Universal terminal equality at each rowpoint determines every original
source cell, even though a single fixed-rowpoint obligation need not do so. -/
theorem gkr_universal_rows_slots_separate (n p : Nat) (a b : Nat → Nat → K)
    (same : ∀ rowpoint left right gamma,
      gkrInputFunctional (p+1) left right gamma (gkrTableSlots n p a rowpoint)=
      gkrInputFunctional (p+1) left right gamma (gkrTableSlots n p b rowpoint))
    (row col : Nat) (hr : row<2^n) (hc : col<2^p) : a row col=b row col := by
  obtain ⟨bits,index⟩ := packed_claim_lane_bits n row hr
  have h := gkr_universal_functionals_separate (p+1)
    (gkrTableSlots n p a (genericRowBooleanPoint bits))
    (gkrTableSlots n p b (genericRowBooleanPoint bits))
    (same (genericRowBooleanPoint bits)) col (by rw [Nat.pow_succ]; omega)
  simp only [gkrTableSlots,hc,ite_true,generic_row_mle_boolean,index] at h
  exact h

/-- The all-obligations relation has a shared table, not one table per rowpoint
or per functional. Once established it transports any extensional trace rule. -/
theorem gkr_universal_rows_predicate (n p : Nat) (a b : Nat → Nat → K)
    (same : ∀ rowpoint left right gamma,
      gkrInputFunctional (p+1) left right gamma (gkrTableSlots n p a rowpoint)=
      gkrInputFunctional (p+1) left right gamma (gkrTableSlots n p b rowpoint))
    (predicate : (Nat → Nat → K) → Prop)
    (extensional : ∀ x y,(∀ row col,row<2^n → col<2^p → x row col=y row col) →
      predicate x → predicate y)
    (valid : predicate a) : predicate b := by
  apply extensional a b _ valid
  exact gkr_universal_rows_slots_separate n p a b same

/-- Fixed universal current/next coefficient weights induced by one table's
GKR input block. Rowpoint, both GKR points and gamma are independent arguments;
this definition cannot select a new source tuple after they are chosen. -/
def gkrUniversalTableWeight (n p : Nat) (rowpoint left right : Nat → K)
    (gamma : K) : Nat → K :=
  packedDualWeight n p rowpoint
    (fun col => rowEqualityWeight (p+1) left col+gamma*rowEqualityWeight (p+1) right col)
    (fun col => rowEqualityWeight (p+1) left (col+2^p)+
      gamma*rowEqualityWeight (p+1) right (col+2^p))


private theorem cube_high_split (p : Nat) (f : Nat → K) :
    cubeSum (p+1) f=cubeSum p f+cubeSum p (fun i => f (i+2^p)) := by
  rw [cube_sum_split_axes p 1]
  change cubeSum p (fun row => f (row+2^p*0))+
    (cubeSum p (fun row => f (row+2^p*1))+0)=_
  simp only [Nat.mul_zero,Nat.add_zero,Nat.mul_one]
  grind

private theorem cube_add (p : Nat) (f g : Nat → K) :
    cubeSum p (fun i => f i+g i)=cubeSum p f+cubeSum p g := by
  unfold cubeSum
  induction List.range (2^p) with
  | nil => simp; grind
  | cons i rest ih => simp only [List.map_cons,List.sum_cons,ih]; grind

/-- Exact join between the universal coefficient-weight family and GKR's
current/next input obligation, with the same fixed source polynomial. -/
theorem gkr_universal_weight_functional (n p : Nat) (table : Nat → Nat → K)
    (polynomial : Poly K)
    (coefficients : ∀ i,i<2^(n+p) → polynomial.coeff i=
      mobiusCoefficients (n+p) (fun j => table (j%2^n) (j/2^n)) i)
    (rowpoint left right : Nat → K) (gamma : K) :
    coefficientTableFunctional (n+p) [gkrUniversalTableWeight n p rowpoint left right gamma] [polynomial]=
      gkrInputFunctional (p+1) left right gamma (gkrTableSlots n p table rowpoint) := by
  unfold gkrUniversalTableWeight
  rw [packed_full_mobius_functional n p rowpoint _ _ table polynomial coefficients,
    ←gkr_input_functional_weights,cube_high_split,←cube_add]
  unfold cubeSum
  congr 1
  apply List.map_congr_left
  intro col hcol
  have bound := List.mem_range.mp hcol
  simp only [gkrTableSlots,bound,ite_true,
    show ¬col+2^p<2^p by omega,ite_false,Nat.add_sub_cancel]


/-- The universal PCS functional family eliminates the harmless kernels of
individual openings: two fixed represented tables agreeing on ALL row/GKR
obligations are the same table at every in-range source cell. -/
theorem gkr_universal_coefficient_family_separates (n p : Nat)
    (a b : Nat → Nat → K) (pa pb : Poly K)
    (ha : ∀ i,i<2^(n+p) → pa.coeff i=
      mobiusCoefficients (n+p) (fun j => a (j%2^n) (j/2^n)) i)
    (hb : ∀ i,i<2^(n+p) → pb.coeff i=
      mobiusCoefficients (n+p) (fun j => b (j%2^n) (j/2^n)) i)
    (same : ∀ rowpoint left right gamma,
      coefficientTableFunctional (n+p) [gkrUniversalTableWeight n p rowpoint left right gamma] [pa]=
      coefficientTableFunctional (n+p) [gkrUniversalTableWeight n p rowpoint left right gamma] [pb])
    (row col : Nat) (hr : row<2^n) (hc : col<2^p) : a row col=b row col := by
  apply gkr_universal_rows_slots_separate n p a b _ row col hr hc
  intro rowpoint left right gamma
  have h := same rowpoint left right gamma
  rw [gkr_universal_weight_functional n p a pa ha,
    gkr_universal_weight_functional n p b pb hb] at h
  exact h

end NearCompression
