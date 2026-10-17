import NearCompression.MultiaffineTensorRealization
import NearCompression.SharedLaneInterpolation

/-! A fixed-envelope single-table joint family with every row/GKR/PCS
coordinate explicit. Sources are arbitrary fixed received oracles; no honest
polynomial or sparse-lift-image premise is used by the far-candidate bound. -/
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

def gkrPointBlock (offset size : Nat) (point : Nat → K) (i : Nat) : K :=
  if i<size then point (offset+i) else 0

def gkrJointDimension (n p : Nat) : Nat := n+2*(p+1)+1+(n+p)

def gkrJointBeta (n p : Nat) (point : Nat → K) : K :=
  gkrUniversalBeta n p
    (gkrPointBlock 0 n point)
    (gkrPointBlock n (p+1) point)
    (gkrPointBlock (n+(p+1)) (p+1) point)
    (gkrPointBlock (n+2*(p+1)+1) (n+p) point)
    (point (n+2*(p+1)))

private theorem block_update_outside (offset size coordinate : Nat) (point : Nat → K)
    (r : K) (outside : coordinate<offset ∨ offset+size≤coordinate) :
    gkrPointBlock offset size (gkrSetCoordinate point coordinate r)=gkrPointBlock offset size point := by
  funext i
  unfold gkrPointBlock gkrSetCoordinate
  by_cases hi : i<size
  · simp only [hi,ite_true,show offset+i≠coordinate by omega,ite_false]
  · simp only [hi,ite_false]

private theorem block_update_inside (offset size coordinate : Nat) (point : Nat → K)
    (r : K) (lower : offset≤coordinate) (upper : coordinate<offset+size) :
    gkrPointBlock offset size (gkrSetCoordinate point coordinate r)=
      gkrSetCoordinate (gkrPointBlock offset size point) (coordinate-offset) r := by
  funext i
  unfold gkrPointBlock gkrSetCoordinate
  by_cases same : i=coordinate-offset
  · subst i
    simp only [show coordinate-offset<size by omega,ite_true,
      show offset+(coordinate-offset)=coordinate by omega]
  · have distinct : offset+i≠coordinate := by omega
    by_cases hi : i<size <;> simp only [same,distinct,hi,ite_false,ite_true]

/-- Every global transcript coordinate maps to exactly one declared block.
This proves the fixed-envelope family is jointly multiaffine without assuming
an independent beta challenge or identifying variables across blocks. -/
theorem gkr_joint_beta_affine (n p : Nat) (point : Nat → K)
    (coordinate : Nat) (bound : coordinate<gkrJointDimension n p) (r : K) :
    gkrJointBeta n p (gkrSetCoordinate point coordinate r)=
      (1-r)*gkrJointBeta n p (gkrSetCoordinate point coordinate 0)+
      r*gkrJointBeta n p (gkrSetCoordinate point coordinate 1) := by
  unfold gkrJointDimension at bound
  unfold gkrJointBeta
  by_cases row : coordinate<n
  · have rb := fun t => block_update_inside 0 n coordinate point t (by omega) (by omega)
    have lb := fun t => block_update_outside n (p+1) coordinate point t (by omega)
    have vb := fun t => block_update_outside (n+(p+1)) (p+1) coordinate point t (by omega)
    have ub := fun t => block_update_outside (n+2*(p+1)+1) (n+p) coordinate point t (by omega)
    simp only [rb,lb,vb,ub,gkrSetCoordinate,show n+2*(p+1)≠coordinate by omega,ite_false]
    exact gkr_beta_coordinate_affine .row n p _ _ _ _ _ _ r
  · by_cases left : coordinate<n+(p+1)
    · have rb := fun t => block_update_outside 0 n coordinate point t (by omega)
      have lb := fun t => block_update_inside n (p+1) coordinate point t (by omega) (by omega)
      have vb := fun t => block_update_outside (n+(p+1)) (p+1) coordinate point t (by omega)
      have ub := fun t => block_update_outside (n+2*(p+1)+1) (n+p) coordinate point t (by omega)
      simp only [rb,lb,vb,ub,gkrSetCoordinate,show n+2*(p+1)≠coordinate by omega,ite_false]
      exact gkr_beta_coordinate_affine .left n p _ _ _ _ _ _ r
    · by_cases right : coordinate<n+2*(p+1)
      · have rb := fun t => block_update_outside 0 n coordinate point t (by omega)
        have lb := fun t => block_update_outside n (p+1) coordinate point t (by omega)
        have vb := fun t => block_update_inside (n+(p+1)) (p+1) coordinate point t (by omega) (by omega)
        have ub := fun t => block_update_outside (n+2*(p+1)+1) (n+p) coordinate point t (by omega)
        simp only [rb,lb,vb,ub,gkrSetCoordinate,show n+2*(p+1)≠coordinate by omega,ite_false]
        exact gkr_beta_coordinate_affine .right n p _ _ _ _ _ _ r
      · by_cases gamma : coordinate=n+2*(p+1)
        · have rb := fun t => block_update_outside 0 n coordinate point t (by omega)
          have lb := fun t => block_update_outside n (p+1) coordinate point t (by omega)
          have vb := fun t => block_update_outside (n+(p+1)) (p+1) coordinate point t (by omega)
          have ub := fun t => block_update_outside (n+2*(p+1)+1) (n+p) coordinate point t (by omega)
          have gv : ∀ t : K,gkrSetCoordinate point coordinate t (n+2*(p+1))=t := by
            intro t; simp [gkrSetCoordinate,gamma]
          simp only [rb,lb,vb,ub,gv]
          exact gkr_beta_coordinate_affine .gamma n p _ _ _ _ 0 0 r
        · have rb := fun t => block_update_outside 0 n coordinate point t (by omega)
          have lb := fun t => block_update_outside n (p+1) coordinate point t (by omega)
          have vb := fun t => block_update_outside (n+(p+1)) (p+1) coordinate point t (by omega)
          have ub := fun t => block_update_inside (n+2*(p+1)+1) (n+p) coordinate point t (by omega) (by omega)
          simp only [rb,lb,vb,ub,gkrSetCoordinate,show n+2*(p+1)≠coordinate by omega,ite_false]
          exact gkr_beta_coordinate_affine .pcs n p _ _ _ _ _ _ r


/-- A fixed list of source-contraction coefficients. The list and the source
oracles precede every coordinate; only their evaluation depends on the point. -/
def jointBetaSource (betas : List ((Nat → K) → K)) (sources : List (K → K))
    (x : K) (point : List K) : K :=
  weightedVirtualOracle (betas.map (fun beta => beta (fun i => point.getD i 0))) sources x

private theorem joint_source_affine (q : Nat) (betas : List ((Nat → K) → K))
    (sources : List (K → K))
    (affine : ∀ beta∈betas,∀ point coordinate,coordinate<q → ∀ r,
      beta (gkrSetCoordinate point coordinate r)=
        (1-r)*beta (gkrSetCoordinate point coordinate 0)+r*beta (gkrSetCoordinate point coordinate 1))
    (x : K) : ListMultiaffine q (jointBetaSource betas sources x) := by
  apply point_affine_list_multiaffine q
    (fun point => weightedVirtualOracle (betas.map (fun beta => beta point)) sources x)
  intro point coordinate bound r
  unfold weightedVirtualOracle
  induction betas generalizing sources with
  | nil => simp [weightedLaneValues]; grind
  | cons beta rest ih =>
    cases sources with
    | nil => simp [weightedLaneValues]; grind
    | cons source tail =>
      have head := affine beta (by simp) point coordinate bound r
      have remain := ih tail (fun b hb => affine b (by simp [hb]))
      simp only [List.map_cons,weightedLaneValues,head,remain]
      grind

/-- Actual fixed-envelope beta, not an assumed arbitrary multi-affine family. -/
theorem gkr_joint_source_tensor_identity (n p : Nat) (source : K → K)
    (point : List K) (shape : point.length=gkrJointDimension n p) (x : K) :
    tensorEvaluate (gkrJointDimension n p)
      (fun y b (_ : Unit) => jointBetaSource [gkrJointBeta n p] [source] y
        (tensorCubeValues (gkrJointDimension n p) b)) point x ()=
      jointBetaSource [gkrJointBeta n p] [source] x point := by
  apply multiaffine_tensor_realization _ _ _ point shape x
  intro y
  apply joint_source_affine
  intro beta member pt coordinate bound r
  have same : beta=gkrJointBeta n p := by simpa using member
  subst beta
  exact gkr_joint_beta_affine n p pt coordinate bound r

/-- One tuple and one agreement set serve every Boolean joint coordinate.
This definition imposes no original-branch sparse-lift image: recovering that
image is an additional near-case obligation, not part of the far bound. -/
noncomputable def JointBetaRepresentative (domain : List K) (weight : K → Nat)
    (q D T : Nat) (betas : List ((Nat → K) → K)) (sources : List (K → K))
    (lanes : List (Poly K)) : Prop :=
  lanes.length=sources.length ∧ (∀ p∈lanes,p.DegLt D) ∧
    T≤consistencyMass domain weight (fun x => ∀ b : TensorCube q,
      jointBetaSource betas sources x (tensorCubeValues q b)=
        (weightedLanePolynomial
          (betas.map (fun beta => beta (fun i => (tensorCubeValues q b).getD i 0))) lanes).eval x)

theorem joint_tensor_reconstruct (domain : List K) (distinct : domain.Nodup)
    (weight : K → Nat) (B q D T : Nat) (bounded : ∀ x∈domain,weight x≤B)
    (betas : List ((Nat → K) → K)) (sources : List (K → K))
    (threshold : B*(D-1)<T)
    (representative : tensorRepresentative domain weight D T q
      (fun x b (_ : Unit) => jointBetaSource betas sources x (tensorCubeValues q b))) :
    ∃ lanes,JointBetaRepresentative domain weight q D T betas sources lanes := by
  classical
  obtain ⟨decoded,degrees,agree⟩ := representative
  let coefficients : TensorCube q → List K := fun b =>
    betas.map (fun beta => beta (fun i => (tensorCubeValues q b).getD i 0))
  have mass : T≤consistencyMass domain weight (fun x => ∀ b : TensorCube q,
      weightedVirtualOracle (coefficients b) sources x=(decoded b ()).eval x) := by
    apply Nat.le_trans agree
    apply consistency_mass_mono
    intro x hx equal b
    exact equal b ()
  obtain ⟨points,unique,size,member,ds,equal⟩ := weighted_shared_lane_reconstruction domain distinct
    weight B D T bounded sources coefficients (fun b => decoded b ())
    (fun b => degrees b ()) mass threshold
  refine ⟨interpolateSourceLanes points sources,interpolate_source_shape points sources,ds,?_⟩
  apply Nat.le_trans mass
  apply consistency_mass_mono
  intro x hx good b
  have zero : (weightedLanePolynomial (coefficients b) (interpolateSourceLanes points sources)-decoded b ()).IsZero := by
    intro i
    rw [Poly.coeff_sub,equal b i]
    grind
  have eval := Poly.eval_of_isZero zero x
  rw [Poly.eval_sub] at eval
  have atPoint := good b
  change weightedVirtualOracle (coefficients b) sources x=
    (weightedLanePolynomial (coefficients b) (interpolateSourceLanes points sources)).eval x
  grind

/-- Explicit far event: no common prechallenge lane tuple, yet the actual
joint contraction has an adaptively selected close degree-bounded candidate.
Neither an honest source nor a tensor-evaluation identity is assumed. -/
theorem joint_beta_candidate_far_count (domain sample : List K)
    (domainDistinct : domain.Nodup) (sampleDistinct : sample.Nodup)
    (weight : K → Nat) (B D T q : Nat) (bounded : ∀ x∈domain,weight x≤B)
    (separation : 2*(domain.map weight).sum+B*(D-1)<3*T)
    (threshold : B*(D-1)<T)
    (betas : List ((Nat → K) → K)) (sources : List (K → K))
    (affine : ∀ beta∈betas,∀ point coordinate,coordinate<q → ∀ r,
      beta (gkrSetCoordinate point coordinate r)=
        (1-r)*beta (gkrSetCoordinate point coordinate 0)+r*beta (gkrSetCoordinate point coordinate 1))
    (far : ¬∃ lanes,JointBetaRepresentative domain weight q D T betas sources lanes) :
    count (uniformTuples sample q) (fun point => ∃ candidate : Poly K,
      candidate.DegLt D ∧ T≤consistencyMass domain weight
        (fun x => jointBetaSource betas sources x point=candidate.eval x)) ≤
      q*max domain.length 2*sample.length^(q-1) := by
  apply multiaffine_candidate_far_count domain sample domainDistinct sampleDistinct weight B D T q
    bounded separation (jointBetaSource betas sources) (joint_source_affine q betas sources affine)
  intro representative
  exact far (joint_tensor_reconstruct domain domainDistinct weight B q D T bounded betas sources threshold representative)

/-- Concrete one-table fixed-envelope specialization of the far bound. -/
theorem gkr_joint_candidate_far_count (domain sample : List K)
    (domainDistinct : domain.Nodup) (sampleDistinct : sample.Nodup)
    (weight : K → Nat) (B D T n p : Nat) (bounded : ∀ x∈domain,weight x≤B)
    (separation : 2*(domain.map weight).sum+B*(D-1)<3*T)
    (threshold : B*(D-1)<T) (source : K → K)
    (far : ¬∃ lanes,JointBetaRepresentative domain weight (gkrJointDimension n p) D T
      [gkrJointBeta n p] [source] lanes) :
    count (uniformTuples sample (gkrJointDimension n p)) (fun point => ∃ candidate : Poly K,
      candidate.DegLt D ∧ T≤consistencyMass domain weight
        (fun x => jointBetaSource [gkrJointBeta n p] [source] x point=candidate.eval x)) ≤
      gkrJointDimension n p*max domain.length 2*sample.length^(gkrJointDimension n p-1) := by
  apply joint_beta_candidate_far_count domain sample domainDistinct sampleDistinct weight B D T
    (gkrJointDimension n p) bounded separation threshold _ _ _ far
  intro beta member pt coordinate bound r
  have same : beta=gkrJointBeta n p := by simpa using member
  subst beta
  exact gkr_joint_beta_affine n p pt coordinate bound r

end NearCompression
