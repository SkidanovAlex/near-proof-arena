import NearCompression.VectorTensorExtraction
import NearCompression.SharedLaneInterpolation

/-! Exact structured beta family/tensor correspondence on a COMMON coefficient
cube, and shared original-lane reconstruction. Sparse lifts and derived GKR
weight construction must instantiate these tables separately. Simultaneous
obligations use joint agreement; one scalar opening is the Unit specialization. -/
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K Obligation : Type} [Field K]

def tensorCubeIndex : (n : Nat) → TensorCube n → Nat
  | 0,_ => 0
  | n+1,(bit,rest) => (if bit then 1 else 0)+2*tensorCubeIndex n rest

def tensorCubeOfBits : (n : Nat) → (Nat → Bool) → TensorCube n
  | 0,_ => ()
  | n+1,bits => (bits 0,tensorCubeOfBits n (fun i => bits (i+1)))

theorem tensor_cube_index_bits (n : Nat) (bits : Nat → Bool) :
    tensorCubeIndex n (tensorCubeOfBits n bits)=genericRowBitIndex n bits := by
  induction n generalizing bits with
  | zero => rfl
  | succ n ih => simp only [tensorCubeIndex,tensorCubeOfBits,genericRowBitIndex,ih]

theorem tensor_cube_index_surjective (n i : Nat) (hi : i<2^n) :
    ∃ b : TensorCube n,tensorCubeIndex n b=i := by
  obtain ⟨bits,index⟩ := packed_claim_lane_bits n i hi
  exact ⟨tensorCubeOfBits n bits,(tensor_cube_index_bits n bits).trans index⟩

theorem tensor_evaluate_row_mle {I : Type} (n : Nat) (values : K → Nat → I → K)
    (point : List K) (shape : point.length=n) (x : K) (i : I) :
    tensorEvaluate n (fun y b j => values y (tensorCubeIndex n b) j) point x i=
      genericRowMLE n (fun b => values x b i) (fun j => point.getD j 0) := by
  induction n generalizing values point with
  | zero => rfl
  | succ n ih =>
    cases point with
    | nil => simp at shape
    | cons r rs =>
      have tail : rs.length=n := by simpa using shape
      have contract : tensorContract n (fun y b j => values y (tensorCubeIndex (n+1) b) j) r=
          (fun y b j => (1-r)*values y (2*tensorCubeIndex n b) j+r*values y (1+2*tensorCubeIndex n b) j) := by
        funext y b j
        simp [tensorContract,tensorCubeIndex]
      rw [tensorEvaluate,contract,ih (fun y b j => (1-r)*values y (2*b) j+r*values y (1+2*b) j) rs tail]
      rw [generic_row_mle_add,generic_row_mle_scale,generic_row_mle_scale]
      simp only [genericRowMLE,List.getD_cons_zero,List.getD_cons_succ,Nat.add_comm 1]

/-- Exact interchange of lane combination and multilinear extension. -/
theorem weighted_values_mle (n : Nat) (tables : List (Nat → K)) (values : List K)
    (point : Nat → K) :
    weightedLaneValues (functionalBatchCoefficients n tables point) values=
      genericRowMLE n (fun b => weightedLaneValues (tables.map (fun w => w b)) values) point := by
  induction tables generalizing values with
  | nil => simp [functionalBatchCoefficients,weightedLaneValues,generic_row_mle_zero]
  | cons w ws ih =>
    cases values with
    | nil => simp [functionalBatchCoefficients,weightedLaneValues,generic_row_mle_zero]
    | cons v vs =>
      simp only [functionalBatchCoefficients,List.map_cons,weightedLaneValues]
      rw [generic_row_mle_add]
      have commute : (fun b => w b*v)=(fun b => v*w b) := by funext b; grind
      rw [commute,generic_row_mle_scale]
      have prior := ih vs
      simp only [functionalBatchCoefficients] at prior
      rw [prior]
      grind

def compressedWeightTensor (n : Nat) (tables : Obligation → List (Nat → K))
    (sources : List (K → K)) : K → TensorCube n → Obligation → K :=
  fun x b obligation => weightedVirtualOracle ((tables obligation).map (fun w => w (tensorCubeIndex n b))) sources x

/-- The implementation's beta_j(u)=MLE(W_j)(u) gives precisely this tensor
contraction, not an independent alpha-power batching challenge. -/
theorem structured_beta_tensor_identity (n : Nat) (tables : Obligation → List (Nat → K))
    (sources : List (K → K)) (point : List K) (shape : point.length=n) (x : K) (obligation : Obligation) :
    tensorEvaluate n (compressedWeightTensor n tables sources) point x obligation=
      weightedVirtualOracle (functionalBatchCoefficients n (tables obligation) (fun i => point.getD i 0)) sources x := by
  unfold compressedWeightTensor
  rw [tensor_evaluate_row_mle n
    (fun y b obligation => weightedVirtualOracle ((tables obligation).map (fun w => w b)) sources y)
    point shape x obligation]
  exact (weighted_values_mle n (tables obligation) (sources.map (fun source => source x)) _).symm

/-- One tuple representing all compressed Boolean rows simultaneously. This
allows source noise in the common functional kernel and is weaker than joint
closeness of the original lanes. It is NOT existence of an AIR-valid assignment. -/
noncomputable def fixedWeightFamilyRepresentative (domain : List K) (weight : K → Nat)
    (n D T : Nat) (tables : Obligation → List (Nat → K)) (sources : List (K → K))
    (lanes : List (Poly K)) : Prop :=
  lanes.length=sources.length ∧ (∀ p∈lanes,p.DegLt D) ∧
    T≤consistencyMass domain weight (fun x => ∀ b obligation,
      weightedVirtualOracle ((tables obligation).map (fun w => w (tensorCubeIndex n b))) sources x=
      (weightedLanePolynomial ((tables obligation).map (fun w => w (tensorCubeIndex n b))) lanes).eval x)

/-- Tensor extraction really does yield ONE original-lane tuple, via common
points, rather than separately choosing representatives for each functional. -/
theorem compressed_tensor_reconstructs_lanes (domain : List K) (distinct : domain.Nodup)
    (weight : K → Nat) (B n D T : Nat) (bounded : ∀ x∈domain,weight x≤B)
    (tables : Obligation → List (Nat → K)) (sources : List (K → K))
    (threshold : B*(D-1)<T)
    (representative : tensorRepresentative domain weight D T n (compressedWeightTensor n tables sources)) :
    ∃ lanes : List (Poly K),fixedWeightFamilyRepresentative domain weight n D T tables sources lanes := by
  classical
  obtain ⟨decoded,degrees,agree⟩ := representative
  let coefficients : (TensorCube n × Obligation) → List K := fun bo =>
    (tables bo.2).map (fun w => w (tensorCubeIndex n bo.1))
  have mass : T≤consistencyMass domain weight (fun x => ∀ bo : TensorCube n × Obligation,
      weightedVirtualOracle (coefficients bo) sources x=(decoded bo.1 bo.2).eval x) := by
    apply Nat.le_trans agree
    apply consistency_mass_mono
    intro x hx equal bo
    exact equal bo.1 bo.2
  obtain ⟨points,unique,size,member,ds,equal⟩ := weighted_shared_lane_reconstruction domain distinct
    weight B D T bounded sources coefficients (fun bo => decoded bo.1 bo.2)
    (fun bo => degrees bo.1 bo.2) mass threshold
  refine ⟨interpolateSourceLanes points sources,interpolate_source_shape points sources,ds,?_⟩
  apply Nat.le_trans agree
  apply consistency_mass_mono
  intro x hx good b obligation
  have zero : (weightedLanePolynomial (coefficients (b,obligation)) (interpolateSourceLanes points sources)-decoded b obligation).IsZero := by
    intro i
    rw [Poly.coeff_sub,equal (b,obligation) i]
    grind
  have eval := Poly.eval_of_isZero zero x
  rw [Poly.eval_sub] at eval
  have atPoint := good b obligation
  change weightedVirtualOracle (coefficients (b,obligation)) sources x=(decoded b obligation).eval x at atPoint
  change weightedVirtualOracle (coefficients (b,obligation)) sources x=
    (weightedLanePolynomial (coefficients (b,obligation)) (interpolateSourceLanes points sources)).eval x
  grind

/-- A shared compressed-Boolean agreement set works at EVERY later point.
The representative tuple does not change when the coefficient family is evaluated. -/
theorem fixed_family_all_points_agree (domain : List K) (weight : K → Nat)
    (n D T : Nat) (tables : Obligation → List (Nat → K)) (sources : List (K → K))
    (lanes : List (Poly K))
    (representative : fixedWeightFamilyRepresentative domain weight n D T tables sources lanes)
    (point : Nat → K) :
    T≤consistencyMass domain weight (fun x => ∀ obligation,
      weightedVirtualOracle (functionalBatchCoefficients n (tables obligation) point) sources x=
        (weightedLanePolynomial (functionalBatchCoefficients n (tables obligation) point) lanes).eval x) := by
  apply Nat.le_trans representative.2.2
  apply consistency_mass_mono
  intro x hx good obligation
  rw [weighted_lane_eval]
  change weightedLaneValues (functionalBatchCoefficients n (tables obligation) point)
    (sources.map (fun source => source x))=_
  rw [weighted_values_mle,weighted_values_mle]
  apply generic_row_mle_congr
  intro i hi
  obtain ⟨b,index⟩ := tensor_cube_index_surjective n i hi
  have equal := good b obligation
  rw [weighted_lane_eval] at equal
  simpa only [weightedVirtualOracle,index] using equal

/-- Directly supplies the shared scalar-family basin used by the already
proved initial-candidate reduction. Unit cap is explicit; no weighted mass
is silently identified with a number of distinct points. -/
theorem fixed_family_scalar_representative (domain : List K) (weight : K → Nat)
    (n D T : Nat) (tables : Obligation → List (Nat → K)) (sources : List (K → K))
    (lanes : List (Poly K)) (cap : ∀ x∈domain,weight x≤1)
    (shape : ∀ obligation,(tables obligation).length=sources.length)
    (threshold : T≤domain.length)
    (representative : fixedWeightFamilyRepresentative domain weight n D T tables sources lanes) :
    SharedFunctionalRepresentative domain n D (domain.length-T) tables sources lanes := by
  refine ⟨representative.2.1,representative.1.symm,?_,?_⟩
  · intro obligation
    exact (shape obligation).trans representative.1.symm
  · intro obligation point
    have mass := fixed_family_all_points_agree domain weight n D T tables sources lanes representative point
    have individual : T≤consistencyMass domain weight (fun x =>
        weightedVirtualOracle (functionalBatchCoefficients n (tables obligation) point) sources x=
          (weightedLanePolynomial (functionalBatchCoefficients n (tables obligation) point) lanes).eval x) := by
      apply Nat.le_trans mass
      apply consistency_mass_mono
      intro x hx h
      exact h obligation
    have agreement : T≤count domain (fun x =>
        weightedVirtualOracle (functionalBatchCoefficients n (tables obligation) point) sources x=
          (weightedLanePolynomial (functionalBatchCoefficients n (tables obligation) point) lanes).eval x) := by
      cases T with
      | zero => omega
      | succ t =>
        apply weighted_mass_implies_enough_points domain weight _ 1 (t+1) (t+1) cap individual
        omega
    have partition := finite_rs_agreement_partition domain
      (weightedVirtualOracle (functionalBatchCoefficients n (tables obligation) point) sources)
      (weightedLanePolynomial (functionalBatchCoefficients n (tables obligation) point) lanes).eval
    omega

/-- Main far-family count with the ACTUAL structured beta source. For multiple
obligations, success is simultaneous joint agreement at the same random point.
The single-opening interpretation uses Obligation=Unit. -/
theorem structured_beta_far_count (domain sample : List K)
    (domainDistinct : domain.Nodup) (sampleDistinct : sample.Nodup)
    (weight : K → Nat) (B n D T : Nat) (bounded : ∀ x∈domain,weight x≤B)
    (tables : Obligation → List (Nat → K)) (sources : List (K → K))
    (threshold : B*(D-1)<T)
    (separation : 2*(domain.map weight).sum+B*(D-1)<3*T)
    (noRepresentative : ¬∃ lanes : List (Poly K),
      fixedWeightFamilyRepresentative domain weight n D T tables sources lanes) :
    count (uniformTuples sample n) (fun point => ∃ candidate : Obligation → Poly K,
      (∀ obligation,(candidate obligation).DegLt D) ∧
      T≤consistencyMass domain weight (fun x => ∀ obligation,
        weightedVirtualOracle (functionalBatchCoefficients n (tables obligation) (fun i => point.getD i 0)) sources x=
          (candidate obligation).eval x)) ≤ n*max domain.length 2*sample.length^(n-1) := by
  have absent : ¬tensorRepresentative domain weight D T n (compressedWeightTensor n tables sources) := by
    intro representative
    exact noRepresentative (compressed_tensor_reconstructs_lanes domain domainDistinct weight B n D T bounded
      tables sources threshold representative)
  have bound := tensor_far_success_count domain sample domainDistinct sampleDistinct weight B D T bounded
    separation n (compressedWeightTensor n tables sources) absent
  rw [tensor_bad_bound_closed] at bound
  have tupleLength : ∀ m : Nat,∀ point∈uniformTuples sample m,point.length=m := by
    intro m
    induction m with
    | zero => simp [uniformTuples]
    | succ m ih =>
      intro point hp
      simp only [uniformTuples,List.mem_flatMap,List.mem_map] at hp
      obtain ⟨r,hr,rest,hrest,rfl⟩ := hp
      simp [ih rest hrest]
  have equal : count (uniformTuples sample n) (fun point => ∃ candidate : Obligation → Poly K,
      (∀ obligation,(candidate obligation).DegLt D) ∧
      T≤consistencyMass domain weight (fun x => ∀ obligation,
        weightedVirtualOracle (functionalBatchCoefficients n (tables obligation) (fun i => point.getD i 0)) sources x=
          (candidate obligation).eval x))=
      count (uniformTuples sample n) (tensorTerminalSuccess domain weight D T n (compressedWeightTensor n tables sources)) := by
    classical
    unfold count
    apply List.countP_congr
    intro point hp
    have predicates : (fun x obligation => tensorEvaluate n (compressedWeightTensor n tables sources) point x obligation)=
        (fun x obligation => weightedVirtualOracle (functionalBatchCoefficients n (tables obligation) (fun i => point.getD i 0)) sources x) := by
      funext x obligation
      exact structured_beta_tensor_identity n tables sources point (tupleLength n point hp) x obligation
    simp only [tensorTerminalSuccess,predicates]
  rw [equal]
  exact bound

end NearCompression
