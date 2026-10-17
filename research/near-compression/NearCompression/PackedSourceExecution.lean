import NearCompression.LowerMobiusBitPass
import NearCompression.FFTMutableSchedule
import NearCompression.PackedDualMobiusWeights

/-! Composition of the packed initialization, mutable Mobius loop and complete
FFT model. These are exact field/state semantics, not a proof of native machine
arithmetic, memory operations, byte encoding or Merkle authentication. -/
namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

/-- The coefficient cache after transforming the row-low packed source lane.
The input includes the actual original-width check and zero padding. -/
def packedComputedCoefficients (n p width group : Nat) (table : Nat → Nat → K) : List K :=
  (List.range (2^(n+p))).map (fun i =>
    mobiusMutableRuns (n+p) 0 (n+p) (genericPackedValues n p width group table) i)

def packedComputedPolynomial (n p width group : Nat) (table : Nat → Nat → K) : Poly K :=
  Poly.mk (packedComputedCoefficients n p width group table)

/-- Fourfold zero padding followed by the actual modeled FFT schedule. -/
def packedComputedFFT (n p width group : Nat) (table : Nat → Nat → K) (omega : K) : Nat → K :=
  fftMutableSchedule (n+p+2) omega
    (fun i => (packedComputedCoefficients n p width group table).getD i 0) (n+p+2)

theorem packed_computed_coefficients_length (n p width group : Nat) (table : Nat → Nat → K) :
    (packedComputedCoefficients n p width group table).length=2^(n+p) := by
  simp [packedComputedCoefficients]

/-- Coefficients are derived from the sequential source transform, rather
than assumed as the premise of a packed functional theorem. -/
theorem packed_computed_coefficient (n p width group : Nat) (table : Nat → Nat → K)
    (i : Nat) (bound : i<2^(n+p)) :
    (packedComputedPolynomial n p width group table).coeff i=
      mobiusCoefficients (n+p) (genericPackedValues n p width group table) i := by
  simp only [packedComputedPolynomial,Poly.coeff,packedComputedCoefficients]
  have read : ((List.range (2^(n+p))).map (fun j =>
      mobiusMutableRuns (n+p) 0 (n+p) (genericPackedValues n p width group table) j)).getD i 0=
      mobiusMutableRuns (n+p) 0 (n+p) (genericPackedValues n p width group table) i := by
    simp [List.getD,bound]
  rw [read,mutable_lower_mobius (n+p) _ i bound]

theorem packed_computed_degree (n p width group : Nat) (table : Nat → Nat → K) :
    (packedComputedPolynomial n p width group table).DegLt (2^(n+p)) := by
  have h := Poly.degLt_length (packedComputedPolynomial n p width group table)
  simpa only [packedComputedPolynomial,packed_computed_coefficients_length] using h

/-- The same computed polynomial answers the packed current/cyclic-next
functional for the original source table and its partially occupied final lane. -/
theorem packed_computed_functional (n p width group : Nat) (table : Nat → Nat → K)
    (point current next : Nat → K) :
    coefficientTableFunctional (n+p) [packedDualWeight n p point current next]
      [packedComputedPolynomial n p width group table]=
      cubeSum p (fun col =>
        current col*genericRowMLE n (genericPackedColumn p width group col table) point+
        next col*genericRowNextMLE n (genericPackedColumn p width group col table) point) := by
  apply packed_full_mobius_functional n p point current next
    (fun row col => genericPackedColumn p width group col table row)
    (packedComputedPolynomial n p width group table)
  intro i hi
  exact packed_computed_coefficient n p width group table i hi

private theorem padding_bound (n p : Nat) : 2^(n+p)≤2^(n+p+2) := by
  simp only [Nat.pow_succ]
  omega

/-- Complete source execution yields the scalar RS oracle at every domain slot. -/
theorem packed_computed_fft_evaluation (n p width group : Nat) (table : Nat → Nat → K)
    (omega : K) (halfOrder : omega^(2^(n+p+1))= -1)
    (i : Nat) (bound : i<2^(n+p+2)) :
    packedComputedFFT n p width group table omega i=
      (packedComputedPolynomial n p width group table).eval (omega^i) := by
  apply fft_mutable_zero_padded_evaluation (n+p+2) omega
    (packedComputedCoefficients n p width group table)
  · rw [packed_computed_coefficients_length]
    exact padding_bound n p
  · intro positive
    simpa only [show n+p+2-1=n+p+1 by omega] using halfOrder
  · exact bound

/-- A computed lane's actual two leaf slots equal its polynomial at ±x. -/
theorem packed_computed_leaf_pair (n p width group : Nat) (table : Nat → Nat → K)
    (omega : K) (halfOrder : omega^(2^(n+p+1))= -1)
    (i : Nat) (bound : i<2^(n+p+1)) :
    (packedComputedFFT n p width group table omega i,
     packedComputedFFT n p width group table omega (i+2^(n+p+1)))=
      ((packedComputedPolynomial n p width group table).eval (omega^i),
       (packedComputedPolynomial n p width group table).eval (-(omega^i))) := by
  apply fft_mutable_rs_pair (n+p+1) omega (packedComputedCoefficients n p width group table)
  · rw [packed_computed_coefficients_length]
    exact padding_bound n p
  · exact halfOrder
  · exact bound


/-- Lane-major adjacent pairs, in the same ascending lane order as rs_commit.
The count is the ceiling of width / packing, including a partial final lane. -/
def packedComputedWideLeaf (n p width : Nat) (table : Nat → Nat → K)
    (omega : K) (i : Nat) : List (K×K) :=
  (List.range ((width+2^p-1)/2^p)).map (fun group =>
    (packedComputedFFT n p width group table omega i,
     packedComputedFFT n p width group table omega (i+2^(n+p+1))))

def packedComputedSources (n p width : Nat) (table : Nat → Nat → K) : List (K → K) :=
  (List.range ((width+2^p-1)/2^p)).map (fun group =>
    (packedComputedPolynomial n p width group table).eval)

/-- Exact sourceWideLeaf interface used by heterogeneous source-pair projection.
No authenticated-leaf premise is needed to identify honestly computed contents;
cryptographic binding of a received leaf remains a separate requirement. -/
theorem packed_computed_wide_leaf (n p width : Nat) (table : Nat → Nat → K)
    (omega : K) (halfOrder : omega^(2^(n+p+1))= -1)
    (i : Nat) (bound : i<2^(n+p+1)) :
    packedComputedWideLeaf n p width table omega i=
      sourceWideLeaf (packedComputedSources n p width table) (omega^i) := by
  simp only [packedComputedWideLeaf,packedComputedSources,sourceWideLeaf,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro group member
  exact packed_computed_leaf_pair n p width group table omega halfOrder i bound

/-- Actual wide leaf computation followed by the verifier's beta combination
is evaluation of the same fixed family of computed source polynomials. -/
theorem packed_computed_beta_pair (n p width : Nat) (table : Nat → Nat → K)
    (omega : K) (halfOrder : omega^(2^(n+p+1))= -1)
    (i : Nat) (bound : i<2^(n+p+1)) (beta : List K) :
    betaWidePair beta (packedComputedWideLeaf n p width table omega i)=
      (weightedVirtualOracle beta (packedComputedSources n p width table) (omega^i),
       weightedVirtualOracle beta (packedComputedSources n p width table) (-(omega^i))) := by
  rw [packed_computed_wide_leaf n p width table omega halfOrder i bound,beta_wide_pair_exact]


private theorem mobius_bounded_congr (n : Nat) (a b : Nat → K)
    (same : ∀ i,i<2^n → a i=b i) (j : Nat) :
    mobiusCoefficients n a j=mobiusCoefficients n b j := by
  induction n generalizing a b j with
  | zero => exact same 0 (by decide)
  | succ n ih =>
    simp only [mobiusCoefficients]
    split
    · apply ih
      intro i hi
      exact same (2*i) (by rw [Nat.pow_succ]; omega)
    · apply ih
      intro i hi
      rw [same (2*i+1) (by rw [Nat.pow_succ]; omega),
        same (2*i) (by rw [Nat.pow_succ]; omega)]

/-- The native transform never modifies the zero-filled LDE tail. -/
theorem mobius_mutable_runs_outside (dimension bit rounds : Nat) (values : Nat → K)
    (i : Nat) (outside : 2^dimension≤i) :
    mobiusMutableRuns dimension bit rounds values i=values i := by
  induction rounds generalizing bit values with
  | zero => rfl
  | succ rounds ih =>
    rw [mobiusMutableRuns,ih,sequential_mobius_pass_exact _ _ List.nodup_range]
    simp only [List.mem_range,show ¬i<2^dimension by omega,ite_false]

/-- The native allocation is initially zero, then its first D packed slots
are populated. Transforming that full buffer gives exactly the coefficient
list followed by zeros, with no assumed buffer/transform equivalence. -/
theorem packed_computed_buffer (n p width group : Nat) (table : Nat → Nat → K) (i : Nat) :
    mobiusMutableRuns (n+p) 0 (n+p)
      (fun j => if j<2^(n+p) then genericPackedValues n p width group table j else 0) i=
      (packedComputedCoefficients n p width group table).getD i 0 := by
  by_cases inside : i<2^(n+p)
  · rw [mutable_lower_mobius (n+p) _ i inside]
    have same : mobiusCoefficients (n+p)
        (fun j => if j<2^(n+p) then genericPackedValues n p width group table j else 0) i=
        mobiusCoefficients (n+p) (genericPackedValues n p width group table) i := by
      apply mobius_bounded_congr
      intro j hj
      simp only [hj,ite_true]
    rw [same]
    exact (packed_computed_coefficient n p width group table i inside).symm
  · rw [mobius_mutable_runs_outside (n+p) 0 (n+p) _ i (by omega)]
    simp only [inside,ite_false]
    simp [List.getD,packed_computed_coefficients_length,inside]

/-- Direct full-buffer pipeline: zero allocation, packed population, in-place
Mobius, then complete in-place FFT, equals the source execution interface. -/
theorem packed_computed_pipeline (n p width group : Nat) (table : Nat → Nat → K)
    (omega : K) (i : Nat) :
    fftMutableSchedule (n+p+2) omega
      (mobiusMutableRuns (n+p) 0 (n+p)
        (fun j => if j<2^(n+p) then genericPackedValues n p width group table j else 0))
      (n+p+2) i=packedComputedFFT n p width group table omega i := by
  have buffers := funext (packed_computed_buffer n p width group table)
  rw [buffers]
  rfl

end NearCompression
