import NearCompression.GKRJointTensorCandidate

/-! Fixed-envelope heterogeneous private-slot weights. Shape and slot placement
are trusted/public inputs fixed before the joint random coordinates. The model
covers current/next slots, source/aux branch offsets and partial packed lanes.
It does not establish that the compiler generated the supplied slot placement. -/
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

structure GKRJointLayout where
  rowCoordinates : Nat
  inputLog : Nat
  commonLog : Nat
  privateCapacity : Nat

structure GKRSourceLane where
  rowLog : Nat
  packingLog : Nat
  rowOffset : Nat
  inputStart : Nat
  nextOffset : Nat
  width : Nat
  group : Nat

def GKRSourceLane.WellFormed (layout : GKRJointLayout) (lane : GKRSourceLane) : Prop :=
  lane.rowOffset+lane.rowLog≤layout.rowCoordinates ∧
  lane.rowLog+lane.packingLog≤layout.commonLog ∧
  lane.inputStart+lane.width≤layout.privateCapacity ∧
  lane.inputStart+lane.nextOffset+lane.width≤layout.privateCapacity ∧
  layout.privateCapacity≤2^layout.inputLog

def heterogeneousColumnWeight (m : Nat) (lane : GKRSourceLane) (next : Bool)
    (left right : Nat → K) (gamma : K) (col : Nat) : K :=
  let sourceColumn := lane.group*2^lane.packingLog+col
  let slot := lane.inputStart+(if next then lane.nextOffset else 0)+sourceColumn
  if sourceColumn<lane.width then
    rowEqualityWeight m left slot+gamma*rowEqualityWeight m right slot else 0

def heterogeneousLaneWeight (m : Nat) (lane : GKRSourceLane)
    (rowpoint left right : Nat → K) (gamma : K) : Nat → K :=
  packedDualWeight lane.rowLog lane.packingLog rowpoint
    (heterogeneousColumnWeight m lane false left right gamma)
    (heterogeneousColumnWeight m lane true left right gamma)

def heterogeneousLaneBeta (m : Nat) (lane : GKRSourceLane)
    (rowpoint left right u : Nat → K) (gamma : K) : K :=
  genericRowMLE (lane.rowLog+lane.packingLog) (heterogeneousLaneWeight m lane rowpoint left right gamma) u

/-- The exact private prefix returned by terminal_gkr.obligation after known
constant contributions have been removed from the scalar claim. -/
def gkrPrivateWeightVector (layout : GKRJointLayout) (left right : Nat → K) (gamma : K) : List K :=
  (List.range layout.privateCapacity).map (fun i =>
    rowEqualityWeight layout.inputLog left i+gamma*rowEqualityWeight layout.inputLog right i)

/-- Literal branch_lanes lookup, including source/aux start offset, next-block
stride, group offset, and zero padding of the final partial lane. -/
theorem heterogeneous_column_private_lookup (layout : GKRJointLayout) (lane : GKRSourceLane)
    (valid : lane.WellFormed layout) (next : Bool) (left right : Nat → K) (gamma : K) (col : Nat) :
    heterogeneousColumnWeight layout.inputLog lane next left right gamma col=
      if lane.group*2^lane.packingLog+col<lane.width then
        (gkrPrivateWeightVector layout left right gamma).getD
          (lane.inputStart+(if next then lane.nextOffset else 0)+lane.group*2^lane.packingLog+col) 0
      else 0 := by
  unfold heterogeneousColumnWeight
  by_cases inside : lane.group*2^lane.packingLog+col<lane.width
  · have bound : lane.inputStart+(if next then lane.nextOffset else 0)+lane.group*2^lane.packingLog+col<layout.privateCapacity := by
      cases next <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> obtain ⟨_,_,a,b,_⟩ := valid <;> omega
    simp only [inside,ite_true]
    simp [gkrPrivateWeightVector,List.getD,bound]
    <;> simp [Nat.add_assoc]
  · simp only [inside,ite_false]

private theorem upper_affine (n : Nat) (f : K → Nat → K)
    (affine : ∀ i r,f r i=(1-r)*f 0 i+r*f 1 i) (index : Nat) (r : K) :
    upperZeta n (f r) index=(1-r)*upperZeta n (f 0) index+r*upperZeta n (f 1) index := by
  induction n generalizing f index with
  | zero => exact affine 0 r
  | succ n ih =>
    simp only [upperZeta]
    split
    · apply ih
      intro i t
      rw [affine (2*i) t,affine (2*i+1) t]
      grind
    · exact ih _ (fun i t => affine (2*i+1) t) _

private theorem mle_affine (n : Nat) (f : K → Nat → K) (point : Nat → K)
    (affine : ∀ i r,f r i=(1-r)*f 0 i+r*f 1 i) (r : K) :
    genericRowMLE n (f r) point=(1-r)*genericRowMLE n (f 0) point+r*genericRowMLE n (f 1) point := by
  have same : f r=(fun i => (1-r)*f 0 i+r*f 1 i) := funext (fun i => affine i r)
  rw [same,generic_row_mle_add,generic_row_mle_scale,generic_row_mle_scale]

/-- Slot offsets and padding masks are fixed, so their application preserves
the coordinate degree of the shared final GKR equality weights. -/
theorem heterogeneous_column_affine (axis : GKRWeightAxis) (m : Nat) (lane : GKRSourceLane)
    (next : Bool) (left right : Nat → K) (gamma : K) (coordinate col : Nat)
    (allowed : axis=.left ∨ axis=.right ∨ axis=.gamma) (r : K) :
    let f := fun t => match axis with
      | .left => heterogeneousColumnWeight m lane next (gkrSetCoordinate left coordinate t) right gamma col
      | .right => heterogeneousColumnWeight m lane next left (gkrSetCoordinate right coordinate t) gamma col
      | .gamma => heterogeneousColumnWeight m lane next left right t col
      | _ => 0
    f r=(1-r)*f 0+r*f 1 := by
  cases axis with
  | row => dsimp only; grind
  | pcs => dsimp only; grind
  | left =>
    dsimp only
    dsimp only [heterogeneousColumnWeight]
    by_cases inside : lane.group*2^lane.packingLog+col<lane.width
    · simp only [inside,ite_true]
      rw [row_equality_coordinate_affine m left coordinate _ r]
      grind
    · simp only [inside,ite_false]; grind
  | right =>
    dsimp only
    dsimp only [heterogeneousColumnWeight]
    by_cases inside : lane.group*2^lane.packingLog+col<lane.width
    · simp only [inside,ite_true]
      rw [row_equality_coordinate_affine m right coordinate _ r]
      grind
    · simp only [inside,ite_false]; grind
  | gamma =>
    dsimp only [heterogeneousColumnWeight]
    by_cases inside : lane.group*2^lane.packingLog+col<lane.width <;>
      simp only [inside,ite_true,ite_false] <;> grind

def heterogeneousBetaCoordinate (axis : GKRWeightAxis) (m : Nat) (lane : GKRSourceLane)
    (rowpoint left right u : Nat → K) (gamma : K) (coordinate : Nat) (r : K) : K :=
  match axis with
  | .row => heterogeneousLaneBeta m lane (gkrSetCoordinate rowpoint coordinate r) left right u gamma
  | .left => heterogeneousLaneBeta m lane rowpoint (gkrSetCoordinate left coordinate r) right u gamma
  | .right => heterogeneousLaneBeta m lane rowpoint left (gkrSetCoordinate right coordinate r) u gamma
  | .gamma => heterogeneousLaneBeta m lane rowpoint left right u r
  | .pcs => heterogeneousLaneBeta m lane rowpoint left right (gkrSetCoordinate u coordinate r) gamma

theorem heterogeneous_beta_coordinate_affine (axis : GKRWeightAxis) (m : Nat) (lane : GKRSourceLane)
    (rowpoint left right u : Nat → K) (gamma : K) (coordinate : Nat) (r : K) :
    heterogeneousBetaCoordinate axis m lane rowpoint left right u gamma coordinate r=
      (1-r)*heterogeneousBetaCoordinate axis m lane rowpoint left right u gamma coordinate 0+
      r*heterogeneousBetaCoordinate axis m lane rowpoint left right u gamma coordinate 1 := by
  cases axis with
  | pcs => exact row_mle_coordinate_affine _ _ _ _ _
  | row =>
    simp only [heterogeneousBetaCoordinate,heterogeneousLaneBeta]
    apply mle_affine (lane.rowLog+lane.packingLog) (fun t => heterogeneousLaneWeight m lane (gkrSetCoordinate rowpoint coordinate t) left right gamma) u
    intro index t
    have a := upper_affine lane.rowLog
      (fun v => rowEqualityWeight lane.rowLog (gkrSetCoordinate rowpoint coordinate v))
      (fun i v => row_equality_coordinate_affine lane.rowLog rowpoint coordinate i v) (index%2^lane.rowLog) t
    have b := upper_affine lane.rowLog
      (fun v => cyclicRowWeight lane.rowLog (gkrSetCoordinate rowpoint coordinate v))
      (fun i v => row_equality_coordinate_affine lane.rowLog rowpoint coordinate _ v) (index%2^lane.rowLog) t
    simp only [heterogeneousLaneWeight,packedDualWeight]
    rw [a,b]
    grind
  | left =>
    simp only [heterogeneousBetaCoordinate,heterogeneousLaneBeta]
    apply mle_affine (lane.rowLog+lane.packingLog) (fun t => heterogeneousLaneWeight m lane rowpoint (gkrSetCoordinate left coordinate t) right gamma) u
    intro index t
    have a := upper_affine lane.packingLog _
      (fun i v => heterogeneous_column_affine .left m lane false left right gamma coordinate i (by simp) v) (index/2^lane.rowLog) t
    have b := upper_affine lane.packingLog _
      (fun i v => heterogeneous_column_affine .left m lane true left right gamma coordinate i (by simp) v) (index/2^lane.rowLog) t
    simp only [heterogeneousLaneWeight,packedDualWeight]
    rw [a,b]
    grind
  | right =>
    simp only [heterogeneousBetaCoordinate,heterogeneousLaneBeta]
    apply mle_affine (lane.rowLog+lane.packingLog) (fun t => heterogeneousLaneWeight m lane rowpoint left (gkrSetCoordinate right coordinate t) gamma) u
    intro index t
    have a := upper_affine lane.packingLog _
      (fun i v => heterogeneous_column_affine .right m lane false left right gamma coordinate i (by simp) v) (index/2^lane.rowLog) t
    have b := upper_affine lane.packingLog _
      (fun i v => heterogeneous_column_affine .right m lane true left right gamma coordinate i (by simp) v) (index/2^lane.rowLog) t
    simp only [heterogeneousLaneWeight,packedDualWeight]
    rw [a,b]
    grind
  | gamma =>
    simp only [heterogeneousBetaCoordinate,heterogeneousLaneBeta]
    apply mle_affine (lane.rowLog+lane.packingLog) (fun t => heterogeneousLaneWeight m lane rowpoint left right t) u
    intro index t
    have a := upper_affine lane.packingLog _
      (fun i v => heterogeneous_column_affine .gamma m lane false left right gamma coordinate i (by simp) v) (index/2^lane.rowLog) t
    have b := upper_affine lane.packingLog _
      (fun i v => heterogeneous_column_affine .gamma m lane true left right gamma coordinate i (by simp) v) (index/2^lane.rowLog) t
    simp only [heterogeneousLaneWeight,packedDualWeight]
    rw [a,b]
    grind
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



def heterogeneousJointDimension (layout : GKRJointLayout) : Nat :=
  layout.rowCoordinates+2*layout.inputLog+1+layout.commonLog

def heterogeneousJointBeta (layout : GKRJointLayout) (lane : GKRSourceLane) (point : Nat → K) : K :=
  heterogeneousLaneBeta layout.inputLog lane
    (gkrPointBlock lane.rowOffset lane.rowLog point)
    (gkrPointBlock layout.rowCoordinates layout.inputLog point)
    (gkrPointBlock (layout.rowCoordinates+layout.inputLog) layout.inputLog point)
    (gkrPointBlock (layout.rowCoordinates+2*layout.inputLog+1+
      (layout.commonLog-(lane.rowLog+lane.packingLog))) (lane.rowLog+lane.packingLog) point)
    (point (layout.rowCoordinates+2*layout.inputLog))

/-- All heterogeneous lanes share ru,rv,gamma and common PCS u. Each rowpoint
uses its table offset; smaller branches skip exactly commonLog-localLog low
PCS coordinates, matching derived_weight_joint.betas. -/
theorem heterogeneous_joint_beta_affine (layout : GKRJointLayout) (lane : GKRSourceLane)
    (valid : lane.WellFormed layout) (point : Nat → K) (coordinate : Nat)
    (bound : coordinate<heterogeneousJointDimension layout) (r : K) :
    heterogeneousJointBeta layout lane (gkrSetCoordinate point coordinate r)=
      (1-r)*heterogeneousJointBeta layout lane (gkrSetCoordinate point coordinate 0)+
      r*heterogeneousJointBeta layout lane (gkrSetCoordinate point coordinate 1) := by
  obtain ⟨rowBound,localBound,_,_,_⟩ := valid
  unfold heterogeneousJointDimension at bound
  let R := layout.rowCoordinates
  let m := layout.inputLog
  let d := lane.rowLog+lane.packingLog
  let offset := R+2*m+1+(layout.commonLog-d)
  have endpoint : offset+d=R+2*m+1+layout.commonLog := by dsimp [offset,R,m,d]; omega
  change coordinate<R+2*m+1+layout.commonLog at bound
  unfold heterogeneousJointBeta
  let f := fun t : K => heterogeneousLaneBeta m lane
    (gkrPointBlock lane.rowOffset lane.rowLog (gkrSetCoordinate point coordinate t))
    (gkrPointBlock R m (gkrSetCoordinate point coordinate t))
    (gkrPointBlock (R+m) m (gkrSetCoordinate point coordinate t))
    (gkrPointBlock offset d (gkrSetCoordinate point coordinate t))
    (gkrSetCoordinate point coordinate t (R+2*m))
  change f r=(1-r)*f 0+r*f 1
  dsimp only [f]
  by_cases row : coordinate<R
  · have lb := fun t => block_update_outside R m coordinate point t (by omega)
    have vb := fun t => block_update_outside (R+m) m coordinate point t (by omega)
    have ub := fun t => block_update_outside offset d coordinate point t (by dsimp [offset]; omega)
    have gv : ∀ t : K,gkrSetCoordinate point coordinate t (R+2*m)=point (R+2*m) := by
      intro t; simp [gkrSetCoordinate,show R+2*m≠coordinate by omega]
    by_cases inside : lane.rowOffset≤coordinate ∧ coordinate<lane.rowOffset+lane.rowLog
    · have rb := fun t => block_update_inside lane.rowOffset lane.rowLog coordinate point t inside.1 inside.2
      simp only [rb,lb,vb,ub,gv]
      exact heterogeneous_beta_coordinate_affine .row m lane _ _ _ _ _ _ r
    · have rb := fun t => block_update_outside lane.rowOffset lane.rowLog coordinate point t (by omega)
      simp only [rb,lb,vb,ub,gv]
      grind
  · have rb := fun t => block_update_outside lane.rowOffset lane.rowLog coordinate point t (by dsimp [R] at row; omega)
    by_cases left : coordinate<R+m
    · have lb := fun t => block_update_inside R m coordinate point t (by omega) left
      have vb := fun t => block_update_outside (R+m) m coordinate point t (by omega)
      have ub := fun t => block_update_outside offset d coordinate point t (by dsimp [offset]; omega)
      have gv : ∀ t : K,gkrSetCoordinate point coordinate t (R+2*m)=point (R+2*m) := by
        intro t; simp [gkrSetCoordinate,show R+2*m≠coordinate by omega]
      simp only [rb,lb,vb,ub,gv]
      exact heterogeneous_beta_coordinate_affine .left m lane _ _ _ _ _ _ r
    · by_cases right : coordinate<R+2*m
      · have lb := fun t => block_update_outside R m coordinate point t (by omega)
        have vb := fun t => block_update_inside (R+m) m coordinate point t (by omega) (by omega)
        have ub := fun t => block_update_outside offset d coordinate point t (by dsimp [offset]; omega)
        have gv : ∀ t : K,gkrSetCoordinate point coordinate t (R+2*m)=point (R+2*m) := by
          intro t; simp [gkrSetCoordinate,show R+2*m≠coordinate by omega]
        simp only [rb,lb,vb,ub,gv]
        exact heterogeneous_beta_coordinate_affine .right m lane _ _ _ _ _ _ r
      · have lb := fun t => block_update_outside R m coordinate point t (by omega)
        have vb := fun t => block_update_outside (R+m) m coordinate point t (by omega)
        by_cases gamma : coordinate=R+2*m
        · have ub := fun t => block_update_outside offset d coordinate point t (by dsimp [offset]; omega)
          have gv : ∀ t : K,gkrSetCoordinate point coordinate t (R+2*m)=t := by
            intro t; simp [gkrSetCoordinate,gamma]
          simp only [rb,lb,vb,ub,gv]
          exact heterogeneous_beta_coordinate_affine .gamma m lane _ _ _ _ 0 0 r
        · have gv : ∀ t : K,gkrSetCoordinate point coordinate t (R+2*m)=point (R+2*m) := by
            intro t; simp [gkrSetCoordinate,show R+2*m≠coordinate by omega]
          by_cases lower : offset≤coordinate
          · have ub := fun t => block_update_inside offset d coordinate point t lower (by omega)
            simp only [rb,lb,vb,ub,gv]
            exact heterogeneous_beta_coordinate_affine .pcs m lane _ _ _ _ _ _ r
          · have ub := fun t => block_update_outside offset d coordinate point t (by omega)
            simp only [rb,lb,vb,ub,gv]
            grind


/-- Exact product decomposition used by lane_weight_mle after branch_lanes
has selected and zero padded its current/next slot coefficient arrays. -/
theorem heterogeneous_lane_weight_mle (m : Nat) (lane : GKRSourceLane)
    (rowpoint left right u : Nat → K) (gamma : K) :
    heterogeneousLaneBeta m lane rowpoint left right u gamma=
      genericRowMLE lane.rowLog (upperZeta lane.rowLog (rowEqualityWeight lane.rowLog rowpoint)) u*
        genericRowMLE lane.packingLog (upperZeta lane.packingLog
          (heterogeneousColumnWeight m lane false left right gamma)) (fun i => u (lane.rowLog+i))+
      genericRowMLE lane.rowLog (upperZeta lane.rowLog (cyclicRowWeight lane.rowLog rowpoint)) u*
        genericRowMLE lane.packingLog (upperZeta lane.packingLog
          (heterogeneousColumnWeight m lane true left right gamma)) (fun i => u (lane.rowLog+i)) := by
  exact packed_dual_weight_mle lane.rowLog lane.packingLog rowpoint _ _ u

def heterogeneousBetas (layout : GKRJointLayout) (entries : List (GKRSourceLane × (K → K))) :
    List ((Nat → K) → K) := entries.map (fun entry => heterogeneousJointBeta layout entry.1)

/-- The source functions are projected to the common RS domain by the same
power used in sparse lifting. No property of the received source word is assumed. -/
def heterogeneousSources (layout : GKRJointLayout) (entries : List (GKRSourceLane × (K → K))) :
    List (K → K) := entries.map (fun entry => fun x =>
      entry.2 (x^(2^(layout.commonLog-(entry.1.rowLog+entry.1.packingLog)))))

def heterogeneousInitialOracle (layout : GKRJointLayout) (entries : List (GKRSourceLane × (K → K)))
    (point : Nat → K) (x : K) : K :=
  weightedVirtualOracle ((heterogeneousBetas layout entries).map (fun beta => beta point))
    (heterogeneousSources layout entries) x

/-- Every lane's actual map into the shared transcript coordinate vector
satisfies the general joint-source theorem's affinity premise. -/
theorem heterogeneous_betas_affine (layout : GKRJointLayout) (entries : List (GKRSourceLane × (K → K)))
    (valid : ∀ entry∈entries,entry.1.WellFormed layout) :
    ∀ beta∈heterogeneousBetas layout entries,∀ point coordinate,
      coordinate<heterogeneousJointDimension layout → ∀ r,
      beta (gkrSetCoordinate point coordinate r)=
        (1-r)*beta (gkrSetCoordinate point coordinate 0)+r*beta (gkrSetCoordinate point coordinate 1) := by
  intro beta member point coordinate bound r
  obtain ⟨entry,he,rfl⟩ := List.mem_map.mp member
  exact heterogeneous_joint_beta_affine layout entry.1 (valid entry he) point coordinate bound r

private theorem heterogeneous_oracle_affine (layout : GKRJointLayout)
    (entries : List (GKRSourceLane × (K → K))) (valid : ∀ entry∈entries,entry.1.WellFormed layout)
    (point : Nat → K) (coordinate : Nat) (bound : coordinate<heterogeneousJointDimension layout)
    (r x : K) :
    heterogeneousInitialOracle layout entries (gkrSetCoordinate point coordinate r) x=
      (1-r)*heterogeneousInitialOracle layout entries (gkrSetCoordinate point coordinate 0) x+
      r*heterogeneousInitialOracle layout entries (gkrSetCoordinate point coordinate 1) x := by
  induction entries with
  | nil => simp [heterogeneousInitialOracle,heterogeneousBetas,heterogeneousSources,weightedVirtualOracle,weightedLaneValues]; grind
  | cons entry rest ih =>
    have head := heterogeneous_joint_beta_affine layout entry.1 (valid entry (by simp)) point coordinate bound r
    have tail := ih (fun e he => valid e (by simp [he]))
    simp only [heterogeneousInitialOracle,heterogeneousBetas,heterogeneousSources,List.map_cons,
      weightedVirtualOracle,weightedLaneValues,head] at tail ⊢
    grind

/-- Exact complete initial virtual oracle, with all table and lane offsets,
realized by one prechallenge tensor. No arbitrary coefficient family premise. -/
theorem heterogeneous_source_tensor_identity (layout : GKRJointLayout)
    (entries : List (GKRSourceLane × (K → K))) (valid : ∀ entry∈entries,entry.1.WellFormed layout)
    (point : List K) (shape : point.length=heterogeneousJointDimension layout) (x : K) :
    tensorEvaluate (heterogeneousJointDimension layout)
      (fun y b (_ : Unit) => heterogeneousInitialOracle layout entries
        (fun i => (tensorCubeValues (heterogeneousJointDimension layout) b).getD i 0) y)
      point x ()=heterogeneousInitialOracle layout entries (fun i => point.getD i 0) x := by
  apply multiaffine_tensor_realization _
    (fun y ps => heterogeneousInitialOracle layout entries (fun i => ps.getD i 0) y) _ point shape x
  intro y
  apply point_affine_list_multiaffine (heterogeneousJointDimension layout) (fun pt => heterogeneousInitialOracle layout entries pt y)
  intro pt coordinate bound r
  exact heterogeneous_oracle_affine layout entries valid pt coordinate bound r y

/-- The actual heterogeneous candidate event inherits the joint far count.
All source/aux lanes share one tuple before row/GKR/PCS challenges. This is a
candidate-event theorem; checked-fold and causal upstream composition remain
separate. Reconstructed sparse-lift image is not asserted in the near branch. -/
theorem heterogeneous_candidate_far_count (domain sample : List K)
    (domainDistinct : domain.Nodup) (sampleDistinct : sample.Nodup)
    (weight : K → Nat) (B D T : Nat) (bounded : ∀ x∈domain,weight x≤B)
    (separation : 2*(domain.map weight).sum+B*(D-1)<3*T) (threshold : B*(D-1)<T)
    (layout : GKRJointLayout) (entries : List (GKRSourceLane × (K → K)))
    (valid : ∀ entry∈entries,entry.1.WellFormed layout)
    (far : ¬∃ lanes,JointBetaRepresentative domain weight (heterogeneousJointDimension layout) D T
      (heterogeneousBetas layout entries) (heterogeneousSources layout entries) lanes) :
    count (uniformTuples sample (heterogeneousJointDimension layout)) (fun point => ∃ candidate : Poly K,
      candidate.DegLt D ∧ T≤consistencyMass domain weight (fun x =>
        heterogeneousInitialOracle layout entries (fun i => point.getD i 0) x=candidate.eval x)) ≤
      heterogeneousJointDimension layout*max domain.length 2*
        sample.length^(heterogeneousJointDimension layout-1) := by
  exact joint_beta_candidate_far_count domain sample domainDistinct sampleDistinct weight B D T
    (heterogeneousJointDimension layout) bounded separation threshold
    (heterogeneousBetas layout entries) (heterogeneousSources layout entries)
    (heterogeneous_betas_affine layout entries valid) far

end NearCompression
