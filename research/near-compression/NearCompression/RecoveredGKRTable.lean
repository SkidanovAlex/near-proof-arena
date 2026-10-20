import NearCompression.RecoveredProjectedEvaluation
import NearCompression.GKRRowSlotSpanning
import NearCompression.HeterogeneousGKRWeights
namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

/-- The inverse direction needed to construct a table from arbitrary decoded
coefficients. No assumption that the original committed oracle was a table
polynomial is used. -/
theorem mobius_lower_zeta (n : Nat) (coefficients : Nat → K) (i : Nat) (bound : i<2^n) :
    mobiusCoefficients n (lowerZeta n coefficients) i=coefficients i := by
  induction n generalizing coefficients i with
  | zero => have h : i=0 := by simpa using bound
            subst i
            rfl
  | succ n ih =>
    have even (j : Nat) : (2*j)%2=0 := by omega
    have odd (j : Nat) : (2*j+1)%2=1 := by omega
    have de (j : Nat) : (2*j)/2=j := by omega
    have do_ (j : Nat) : (2*j+1)/2=j := by omega
    have evens : (fun j => lowerZeta (n+1) coefficients (2*j))=
        lowerZeta n (fun j => coefficients (2*j)) := by
      funext j
      simp only [lowerZeta,even,de,ite_true]
    have differences : (fun j => lowerZeta (n+1) coefficients (2*j+1)-lowerZeta (n+1) coefficients (2*j))=
        lowerZeta n (fun j => coefficients (2*j+1)) := by
      funext j
      simp only [lowerZeta,even,odd,de,do_,Nat.reduceEqDiff,ite_true,ite_false]
      rw [lower_zeta_add]
      grind
    have half : i/2<2^n := by rw [Nat.pow_succ] at bound; omega
    simp only [mobiusCoefficients]
    split
    · rename_i parity
      rw [evens,ih _ _ half]
      congr 1
      omega
    · rename_i parity
      rw [differences,ih _ _ half]
      congr 1
      omega

/-- The fixed decoded assignment, with row bits low and column bits high.
This definition depends only on the recovered polynomial, not an opening
rowpoint or GKR challenge. -/
def recoveredGKRTable (n p : Nat) (polynomial : Poly K) (row col : Nat) : K :=
  lowerZeta (n+p) polynomial.coeff (row+2^n*col)

theorem recovered_table_coefficients (n p : Nat) (polynomial : Poly K) (i : Nat)
    (bound : i<2^(n+p)) :
    polynomial.coeff i=mobiusCoefficients (n+p)
      (fun j => recoveredGKRTable n p polynomial (j%2^n) (j/2^n)) i := by
  have same : (fun j => recoveredGKRTable n p polynomial (j%2^n) (j/2^n))=
      lowerZeta (n+p) polynomial.coeff := by
    funext j
    unfold recoveredGKRTable
    rw [Nat.mod_add_div]
  rw [same,mobius_lower_zeta _ _ _ bound]

/-- Every current and cyclic-next row claim is a functional of the same
fixed decoded table. This is functional interpretation, not claim acceptance. -/
theorem recovered_table_current_next (n p : Nat) (polynomial : Poly K)
    (point current next : Nat → K) :
    coefficientTableFunctional (n+p) [packedDualWeight n p point current next] [polynomial]=
      cubeSum p (fun col => current col*genericRowMLE n (fun row => recoveredGKRTable n p polynomial row col) point+
        next col*genericRowNextMLE n (fun row => recoveredGKRTable n p polynomial row col) point) := by
  exact packed_full_mobius_functional n p point current next (recoveredGKRTable n p polynomial) polynomial
    (recovered_table_coefficients n p polynomial)

/-- Exact GKR private-input obligation for the decoded assignment, uniformly
in all row, ru,rv and gamma challenges. -/
theorem recovered_table_gkr_functional (n p : Nat) (polynomial : Poly K)
    (rowpoint left right : Nat → K) (gamma : K) :
    coefficientTableFunctional (n+p) [gkrUniversalTableWeight n p rowpoint left right gamma] [polynomial]=
      gkrInputFunctional (p+1) left right gamma (gkrTableSlots n p (recoveredGKRTable n p polynomial) rowpoint) := by
  exact gkr_universal_weight_functional n p (recoveredGKRTable n p polynomial) polynomial
    (recovered_table_coefficients n p polynomial) rowpoint left right gamma

private theorem cube_zero (n : Nat) : cubeSum n (fun _ => (0:K))=0 := by
  unfold cubeSum
  induction List.range (2^n) with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons,List.sum_cons,ih]; grind

/-- Repeated low-coordinate weights and sparse low-coordinate coefficients
cancel exactly in the coefficient functional, including zero factors. -/
theorem sparse_lift_weight_functional (k n : Nat) (weights coefficients : Nat → K) :
    cubeSum (k+n) (fun i => repeatLowWeights k weights i*sparseLowLift k coefficients i)=
      cubeSum n (fun i => weights i*coefficients i) := by
  induction k with
  | zero => simp only [Nat.zero_add,repeatLowWeights,sparseLowLift]
  | succ k ih =>
    rw [show k+1+n=(k+n)+1 by omega,cube_sum_split]
    have even (i : Nat) : (2*i)/2=i := by omega
    have odd (i : Nat) : (2*i+1)/2=i := by omega
    have em (i : Nat) : (2*i)%2=0 := by omega
    have om (i : Nat) : (2*i+1)%2=1 := by omega
    simp only [repeatLowWeights,sparseLowLift,even,odd,em,om,Nat.reduceEqDiff,ite_true,ite_false]
    have zero : (fun i => repeatLowWeights k weights i*0)=(fun _ => (0:K)) := by funext i; grind
    rw [ih,zero,cube_zero]
    grind

private theorem singleton_functional (n : Nat) (weights : Nat → K) (polynomial : Poly K) :
    coefficientTableFunctional n [weights] [polynomial]=cubeSum n (fun i => weights i*polynomial.coeff i) := by
  unfold coefficientTableFunctional cubeSum
  congr 1
  apply List.map_congr_left
  intro i hi
  simp only [List.map_cons,List.map_nil,weightedLaneValues]
  grind

/-- Common-domain recovered candidate → original-degree functional, using
actual sparse storage rather than assuming transform equality. -/
theorem recovered_lifted_functional (k n : Nat) (polynomial : Poly K)
    (degree : polynomial.DegLt (2^k*2^n))
    (sparse : ∀ i,¬2^k∣i → polynomial.coeff i=0) (weights : Nat → K) :
    coefficientTableFunctional (k+n) [repeatLowWeights k weights] [polynomial]=
      coefficientTableFunctional n [weights] [recoverProjectedPolynomial (2^k) (2^n) polynomial] := by
  rw [singleton_functional,singleton_functional]
  have coefficients : ∀ i,i<2^(k+n) → polynomial.coeff i=
      sparseLowLift k (recoverProjectedPolynomial (2^k) (2^n) polynomial).coeff i := by
    intro i hi
    rw [recovered_projected_sparse_storage k n polynomial degree sparse i]
    simp [sparseLiftPolynomial,coefficientPolynomial,Poly.coeff,List.getD,hi]
    rfl
  have same : cubeSum (k+n) (fun i => repeatLowWeights k weights i*polynomial.coeff i)=
      cubeSum (k+n) (fun i => repeatLowWeights k weights i*
        sparseLowLift k (recoverProjectedPolynomial (2^k) (2^n) polynomial).coeff i) := by
    unfold cubeSum
    congr 1
    apply List.map_congr_left
    intro i hi
    rw [coefficients i (List.mem_range.mp hi)]
  rw [same,sparse_lift_weight_functional]

/-- Complete deterministic recovered-private-input bridge: lifted PCS
functional equals the GKR current/next functional of one fixed decoded table.
It does not assert that an adversarially sent claim equals either side. -/
theorem recovered_lifted_gkr_functional (k n p : Nat) (polynomial : Poly K)
    (degree : polynomial.DegLt (2^k*2^(n+p)))
    (sparse : ∀ i,¬2^k∣i → polynomial.coeff i=0)
    (rowpoint left right : Nat → K) (gamma : K) :
    let recovered := recoverProjectedPolynomial (2^k) (2^(n+p)) polynomial
    coefficientTableFunctional (k+(n+p))
      [repeatLowWeights k (gkrUniversalTableWeight n p rowpoint left right gamma)] [polynomial]=
      gkrInputFunctional (p+1) left right gamma
        (gkrTableSlots n p (recoveredGKRTable n p recovered) rowpoint) := by
  dsimp only
  rw [recovered_lifted_functional k (n+p) polynomial degree sparse,recovered_table_gkr_functional]

/-- Actual heterogeneous private-slot weights, including source/aux offsets,
shared ru/rv/gamma and partial-lane masks, evaluated on the decoded table. -/
theorem recovered_lifted_heterogeneous_functional (k m : Nat) (lane : GKRSourceLane)
    (polynomial : Poly K)
    (degree : polynomial.DegLt (2^k*2^(lane.rowLog+lane.packingLog)))
    (sparse : ∀ i,¬2^k∣i → polynomial.coeff i=0)
    (rowpoint left right : Nat → K) (gamma : K) :
    let recovered := recoverProjectedPolynomial (2^k) (2^(lane.rowLog+lane.packingLog)) polynomial
    let table := recoveredGKRTable lane.rowLog lane.packingLog recovered
    coefficientTableFunctional (k+(lane.rowLog+lane.packingLog))
      [repeatLowWeights k (heterogeneousLaneWeight m lane rowpoint left right gamma)] [polynomial]=
      cubeSum lane.packingLog (fun col =>
        heterogeneousColumnWeight m lane false left right gamma col*
          genericRowMLE lane.rowLog (fun row => table row col) rowpoint+
        heterogeneousColumnWeight m lane true left right gamma col*
          genericRowNextMLE lane.rowLog (fun row => table row col) rowpoint) := by
  dsimp only
  rw [recovered_lifted_functional k _ polynomial degree sparse]
  exact recovered_table_current_next lane.rowLog lane.packingLog _ rowpoint _ _
end NearCompression
