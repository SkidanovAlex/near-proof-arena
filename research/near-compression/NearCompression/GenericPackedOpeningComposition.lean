import NearCompression.GenericPackingIdentity
import NearCompression.GenericPackedGridCounting
import NearCompression.GenericMonomialTensor

/-! Composition of packing, fixed-vector authentication, and an exact PCS
evaluation contract. Source table, row point, coefficients and sent vector
are fixed parameters, not functions of sampled column coordinates. Hash
binding, coefficient construction and transcript order are external duties. -/
namespace NearCompression
open Lean.Grind ArenaCore.Security
variable {K : Type} [Field K]

theorem packed_row_mle_point_congr (n : Nat) (values a b : Nat → K)
    (same : ∀ i, i<n → a i=b i) : genericRowMLE n values a=genericRowMLE n values b := by
  induction n generalizing values a b with
  | zero => rfl
  | succ n ih =>
    have first := same 0 (by omega)
    have tail : ∀ i, i<n → a (i+1)=b (i+1) := by
      intro i hi
      exact same (i+1) (by omega)
    simp only [genericRowMLE,first,ih _ _ _ tail]

def packedOpeningPoint (rows : Nat) (rowPoint : Nat → K) (columnPoint : List K)
    (i : Nat) : K :=
  if i<rows then rowPoint i else columnPoint.getD (i-rows) 0

def packedSourceClaims (rows pack width group : Nat) (table : Nat → Nat → K)
    (rowPoint : Nat → K) (col : Nat) : K :=
  genericRowMLE rows (genericPackedColumn pack width group col table) rowPoint

theorem packed_opening_point_identity (rows pack width group : Nat)
    (table : Nat → Nat → K) (rowPoint : Nat → K) (columnPoint : List K) :
    genericRowMLE (rows+pack) (genericPackedValues rows pack width group table)
      (packedOpeningPoint rows rowPoint columnPoint) =
      packedGridEval pack (packedSourceClaims rows pack width group table rowPoint) columnPoint := by
  rw [generic_packed_mle_identity]
  have rowsEq : ∀ col,
      genericRowMLE rows (genericPackedColumn pack width group col table)
        (packedOpeningPoint rows rowPoint columnPoint) =
      packedSourceClaims rows pack width group table rowPoint col := by
    intro col
    apply packed_row_mle_point_congr
    intro i hi
    simp only [packedOpeningPoint,hi,ite_true]
  have colsEq : (fun i => packedOpeningPoint rows rowPoint columnPoint (rows+i)) =
      (fun i => columnPoint.getD i 0) := by
    funext i
    have outside : ¬rows+i<rows := by omega
    simp only [packedOpeningPoint,outside,ite_false,Nat.add_sub_cancel_left]
  simp only [rowsEq,colsEq,packedGridEval]

theorem packed_source_claim_valid (rows pack width group lane : Nat)
    (table : Nat → Nat → K) (rowPoint : Nat → K)
    (present : group*2^pack+lane<width) :
    packedSourceClaims rows pack width group table rowPoint lane =
      genericRowMLE rows (fun row => table row (group*2^pack+lane)) rowPoint := by
  have eq : genericPackedColumn pack width group lane table =
      (fun row => table row (group*2^pack+lane)) := by
    funext row
    simp only [genericPackedColumn,present,ite_true]
  simp only [packedSourceClaims,eq]

theorem packed_source_claim_padding (rows pack width group lane : Nat)
    (table : Nat → Nat → K) (rowPoint : Nat → K)
    (missing : width≤group*2^pack+lane) :
    packedSourceClaims rows pack width group table rowPoint lane=0 :=
  generic_padded_column_mle_zero rows pack width group lane table rowPoint missing

/-- Exact contract for a particular opening verifier. Its return value must
be the fixed coefficient tensor's evaluation at the specified point. This
does not assume the claim-vector authentication conclusion. -/
def PackedPCSExact (rows pack : Nat) (coefficients : List K)
    (rowPoint : Nat → K) (accepts : List K → K → Prop) : Prop :=
  ∀ columnPoint value, accepts columnPoint value →
    value=genericMonomialTensor (rows+pack) coefficients
      (packedOpeningPoint rows rowPoint columnPoint)

/-- Accepted scalar opening plus equality with the sent vector can hide a
wrong lane on at most p*|S|^(p-1) independent column points (p=packPred+1).
The binding equation names the actual padded source polynomial explicitly. -/
theorem packed_opening_bad_count (rows packPred width group lane : Nat)
    (table : Nat → Nat → K) (rowPoint sent : Nat → K) (coefficients : List K)
    (sourceBinding : ∀ point,
      genericMonomialTensor (rows+(packPred+1)) coefficients point =
      genericRowMLE (rows+(packPred+1))
        (genericPackedValues rows (packPred+1) width group table) point)
    (accepts : List K → K → Prop)
    (pcs : PackedPCSExact rows (packPred+1) coefficients rowPoint accepts)
    (valid : lane<2^(packPred+1))
    (wrong : sent lane ≠ packedSourceClaims rows (packPred+1) width group table rowPoint lane)
    (sample : List K) (distinct : sample.Nodup) :
    count (packedGrid sample (packPred+1))
      (fun point => ∃ value, accepts point value ∧ packedGridEval (packPred+1) sent point=value) ≤
      (packPred+1)*sample.length^packPred := by
  have bound := packed_claim_grid_bad_count packPred lane sent
    (packedSourceClaims rows (packPred+1) width group table rowPoint) valid wrong sample distinct
  apply Nat.le_trans _ bound
  apply count_mono
  intro point accepted
  obtain ⟨value,hpcs,hsent⟩ := accepted
  have exactEval := pcs point value hpcs
  rw [sourceBinding,packed_opening_point_identity] at exactEval
  exact hsent.trans exactEval

/-- Convenience interface when the erroneous lane is an original source
column; absent columns remain zero in the packed polynomial. -/
theorem packed_opening_original_lane_bad_count (rows packPred width group lane : Nat)
    (table : Nat → Nat → K) (rowPoint sent : Nat → K) (coefficients : List K)
    (sourceBinding : ∀ point,
      genericMonomialTensor (rows+(packPred+1)) coefficients point =
      genericRowMLE (rows+(packPred+1))
        (genericPackedValues rows (packPred+1) width group table) point)
    (accepts : List K → K → Prop)
    (pcs : PackedPCSExact rows (packPred+1) coefficients rowPoint accepts)
    (valid : lane<2^(packPred+1)) (present : group*2^(packPred+1)+lane<width)
    (wrong : sent lane ≠ genericRowMLE rows
      (fun row => table row (group*2^(packPred+1)+lane)) rowPoint)
    (sample : List K) (distinct : sample.Nodup) :
    count (packedGrid sample (packPred+1))
      (fun point => ∃ value, accepts point value ∧ packedGridEval (packPred+1) sent point=value) ≤
      (packPred+1)*sample.length^packPred := by
  apply packed_opening_bad_count rows packPred width group lane table rowPoint sent
    coefficients sourceBinding accepts pcs valid _ sample distinct
  rw [packed_source_claim_valid rows (packPred+1) width group lane table rowPoint present]
  exact wrong

/-- With no column coordinates, authentication is an exact scalar equality,
so a wrong claim cannot pass an exact opening contract. -/
theorem packed_opening_zero_pack_rejects (rows width group : Nat)
    (table : Nat → Nat → K) (rowPoint sent : Nat → K) (coefficients : List K)
    (sourceBinding : ∀ point,
      genericMonomialTensor (rows+0) coefficients point =
      genericRowMLE (rows+0) (genericPackedValues rows 0 width group table) point)
    (accepts : List K → K → Prop)
    (pcs : PackedPCSExact rows 0 coefficients rowPoint accepts)
    (wrong : sent 0 ≠ packedSourceClaims rows 0 width group table rowPoint 0)
    (point : List K) :
    ¬ ∃ value, accepts point value ∧ packedGridEval 0 sent point=value := by
  intro accepted
  obtain ⟨value,hpcs,hsent⟩ := accepted
  have exactEval := pcs point value hpcs
  rw [sourceBinding,packed_opening_point_identity] at exactEval
  exact wrong (hsent.trans exactEval)

end NearCompression
