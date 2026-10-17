import NearCompression.GKRBooleanLaneSeparator
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

def jointSeparatorBits (layout : GKRJointLayout) (bits : Nat → Bool) (i : Nat) : Bool :=
  if layout.rowCoordinates≤i ∧ i<layout.rowCoordinates+layout.inputLog then bits (i-layout.rowCoordinates) else false

def boundedBits (n : Nat) (bits : Nat → Bool) (i : Nat) : Bool := if i<n then bits i else false

private theorem bit_index_congr (n : Nat) (a b : Nat → Bool) (same : ∀ i,i<n → a i=b i) :
    genericRowBitIndex n a=genericRowBitIndex n b := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih =>
    simp only [genericRowBitIndex,same 0 (by omega)]
    rw [ih (fun i => a (i+1)) (fun i => b (i+1)) (by intro i hi; exact same (i+1) (by omega))]

theorem bounded_bits_index (n : Nat) (bits : Nat → Bool) :
    genericRowBitIndex n (boundedBits n bits)=genericRowBitIndex n bits := by
  apply bit_index_congr
  intro i hi
  simp [boundedBits,hi]

/-- Embeds the local lane selector into the actual joint coordinate layout.
All row, rv, gamma and PCS coordinates are Boolean zero. -/
theorem joint_separator_local (layout : GKRJointLayout) (lane : GKRSourceLane)
    (bits : Nat → Bool) :
    heterogeneousJointBeta (K:=K) layout lane (genericRowBooleanPoint (jointSeparatorBits layout bits))=
      heterogeneousLaneBeta layout.inputLog lane
        (gkrPointBlock lane.rowOffset lane.rowLog (genericRowBooleanPoint (jointSeparatorBits layout bits)))
        (genericRowBooleanPoint (boundedBits layout.inputLog bits)) (fun _ => 0) (fun _ => 0) 0 := by
  have left : gkrPointBlock layout.rowCoordinates layout.inputLog
      (genericRowBooleanPoint (jointSeparatorBits layout bits))=
      (genericRowBooleanPoint (boundedBits layout.inputLog bits) : Nat → K) := by
    funext i
    simp only [gkrPointBlock,genericRowBooleanPoint,jointSeparatorBits,boundedBits]
    by_cases hi : i<layout.inputLog
    · have a : layout.rowCoordinates≤layout.rowCoordinates+i := by omega
      have b : layout.rowCoordinates+i<layout.rowCoordinates+layout.inputLog := by omega
      simp [hi,a,b]
    · simp [hi]
  have blockZero (start len : Nat) (after : layout.rowCoordinates+layout.inputLog≤start) :
      gkrPointBlock start len (genericRowBooleanPoint (jointSeparatorBits layout bits))=(fun _ => (0:K)) := by
    funext i
    simp only [gkrPointBlock,genericRowBooleanPoint,jointSeparatorBits]
    have out : ¬(layout.rowCoordinates≤start+i ∧ start+i<layout.rowCoordinates+layout.inputLog) := by omega
    simp [out]
  have gamma : (genericRowBooleanPoint (jointSeparatorBits layout bits) (layout.rowCoordinates+2*layout.inputLog) : K)=0 := by
    simp only [genericRowBooleanPoint,jointSeparatorBits]
    have out : ¬(layout.rowCoordinates≤layout.rowCoordinates+2*layout.inputLog ∧
      layout.rowCoordinates+2*layout.inputLog<layout.rowCoordinates+layout.inputLog) := by omega
    simp only [out,ite_false,Bool.false_eq_true]
  unfold heterogeneousJointBeta
  rw [left,blockZero (layout.rowCoordinates+layout.inputLog) layout.inputLog (by omega),
    blockZero (layout.rowCoordinates+2*layout.inputLog+1+(layout.commonLog-(lane.rowLog+lane.packingLog))) (lane.rowLog+lane.packingLog) (by omega),gamma]

def cubeFromBits : (q : Nat) → (Nat → Bool) → TensorCube q
  | 0,_ => ()
  | q+1,bits => (bits 0,cubeFromBits q (fun i => bits (i+1)))

theorem cube_from_bits_values (q : Nat) (bits : Nat → Bool) (i : Nat) :
    (tensorCubeValues (K:=K) q (cubeFromBits q bits)).getD i 0=
      if i<q then genericRowBooleanPoint bits i else 0 := by
  induction q generalizing bits i with
  | zero => simp [cubeFromBits,tensorCubeValues,List.getD]
  | succ q ih =>
    cases i with
    | zero => simp [cubeFromBits,tensorCubeValues,List.getD,genericRowBooleanPoint]
    | succ i =>
      simp only [cubeFromBits,tensorCubeValues,List.getD_cons_succ,ih]
      simp only [Nat.add_lt_add_iff_right,genericRowBooleanPoint]

theorem joint_separator_cube (layout : GKRJointLayout) (bits : Nat → Bool) :
    (fun i => (tensorCubeValues (K:=K) (heterogeneousJointDimension layout)
      (cubeFromBits (heterogeneousJointDimension layout) (jointSeparatorBits layout bits))).getD i 0)=
      genericRowBooleanPoint (jointSeparatorBits layout bits) := by
  funext i
  rw [cube_from_bits_values]
  split
  · rfl
  · rename_i outside
    simp only [genericRowBooleanPoint,jointSeparatorBits]
    have out : ¬(layout.rowCoordinates≤i ∧ i<layout.rowCoordinates+layout.inputLog) := by
      unfold heterogeneousJointDimension at outside
      omega
    simp [out]

/-- A concrete metadata certificate: each current lane has a private selector
slot absent from every other current/next lane and from its own next lane. -/
def CanonicalLaneSelectors (layout : GKRJointLayout) (lanes : List GKRSourceLane) : Prop :=
  ∀ i,∀ hi : i<lanes.length,∃ slot,slot<2^layout.inputLog ∧
    lanes[i].LiveSlot false slot ∧ (¬lanes[i].LiveSlot true slot) ∧
    ∀ j,∀ hj : j<lanes.length,i≠j → ∀ next,¬lanes[j].LiveSlot next slot

/-- Literal Boolean tensor coordinate selecting each lane. The certificate
contains only natural slot geometry, never a beta or polynomial identity. -/
theorem canonical_joint_lane_selector (layout : GKRJointLayout) (lanes : List GKRSourceLane)
    (valid : ∀ lane∈lanes,lane.WellFormed layout)
    (geometry : CanonicalLaneSelectors layout lanes) (i : Nat) (hi : i<lanes.length) :
    ∃ b : TensorCube (heterogeneousJointDimension layout),∀ j,∀ hj : j<lanes.length,
      heterogeneousJointBeta (K:=K) layout lanes[j]
        (fun k => (tensorCubeValues (heterogeneousJointDimension layout) b).getD k 0)=
        if j=i then 1 else 0 := by
  obtain ⟨slot,bound,live,noNext,others⟩ := geometry i hi
  obtain ⟨bits,hbits⟩ := packed_claim_lane_bits layout.inputLog slot bound
  refine ⟨cubeFromBits (heterogeneousJointDimension layout) (jointSeparatorBits layout bits),?_⟩
  intro j hj
  rw [joint_separator_cube,joint_separator_local]
  have index : genericRowBitIndex layout.inputLog (boundedBits layout.inputLog bits)=slot := by
    rw [bounded_bits_index,hbits]
  by_cases same : j=i
  · subst j
    simp only [ite_true]
    apply heterogeneous_beta_select_live layout _ (valid _ (List.getElem_mem _))
    · simpa only [index,List.get_eq_getElem] using live
    · simpa only [index,List.get_eq_getElem] using noNext
  · simp only [same,ite_false]
    apply heterogeneous_beta_select_absent layout _ (valid _ (List.getElem_mem _))
    intro next
    rw [index]
    exact others j hj (Ne.symm same) next

private theorem weighted_values_zero (cs vs : List K)
    (zero : ∀ j,j<cs.length → cs.getD j 0=0) : weightedLaneValues cs vs=0 := by
  induction cs generalizing vs with
  | nil => rfl
  | cons c cs ih =>
    cases vs with
    | nil => rfl
    | cons v vs =>
      have head := zero 0 (by simp)
      have tail := ih vs (by intro j hj; exact zero (j+1) (by simp; omega))
      simp only [List.getD_cons_zero] at head
      simp only [weightedLaneValues,head,tail]
      grind

private theorem weighted_values_delta (cs vs : List K) (i : Nat)
    (shape : cs.length=vs.length) (bound : i<cs.length)
    (delta : ∀ j,j<cs.length → cs.getD j 0=if j=i then 1 else 0) :
    weightedLaneValues cs vs=vs.getD i 0 := by
  induction cs generalizing vs i with
  | nil => simp at bound
  | cons c cs ih =>
    cases vs with
    | nil => simp at shape
    | cons v vs =>
      cases i with
      | zero =>
        have head := delta 0 (by simp)
        simp only [List.getD_cons_zero,ite_true] at head
        have tail : weightedLaneValues cs vs=0 := weighted_values_zero cs vs (by
          intro j hj
          have h := delta (j+1) (by simp; omega)
          simpa using h)
        simp only [weightedLaneValues,head,tail,List.getD_cons_zero]
        grind
      | succ i =>
        have head := delta 0 (by simp)
        simp at head
        have tail := ih vs i (by simpa using shape) (by simp at bound; omega) (by
          intro j hj
          have h := delta (j+1) (by simp; omega)
          simpa using h)
        simp only [weightedLaneValues,head,tail,List.getD_cons_succ]
        grind

/-- Universal Boolean contraction agreement entails simultaneous lane
agreement, using the actual heterogeneous beta and the slot certificate. -/
theorem joint_lane_pointwise_agreement (layout : GKRJointLayout) (metadata : List GKRSourceLane)
    (valid : ∀ lane∈metadata,lane.WellFormed layout)
    (geometry : CanonicalLaneSelectors layout metadata)
    (sources : List (K → K)) (polys : List (Poly K))
    (sourceShape : sources.length=metadata.length) (polyShape : polys.length=metadata.length)
    (x : K)
    (agree : ∀ b : TensorCube (heterogeneousJointDimension layout),
      jointBetaSource (metadata.map (heterogeneousJointBeta layout)) sources x (tensorCubeValues _ b)=
      (weightedLanePolynomial ((metadata.map (heterogeneousJointBeta layout)).map
        (fun beta => beta (fun k => (tensorCubeValues _ b).getD k 0))) polys).eval x) :
    ∀ i,i<metadata.length → (sources.map (fun f => f x)).getD i 0=(polys.map (fun p => p.eval x)).getD i 0 := by
  intro i hi
  obtain ⟨b,select⟩ := canonical_joint_lane_selector (K:=K) layout metadata valid geometry i hi
  let coefficients : List K := (metadata.map (heterogeneousJointBeta layout)).map
    (fun beta => beta (fun k => (tensorCubeValues _ b).getD k 0))
  have size : coefficients.length=metadata.length := by simp [coefficients]
  have delta : ∀ j,j<coefficients.length → coefficients.getD j 0=if j=i then 1 else 0 := by
    intro j hj
    have h : j<metadata.length := by simpa only [size] using hj
    simpa [coefficients,List.getD,h] using select j h
  have h := agree b
  change weightedVirtualOracle coefficients sources x=(weightedLanePolynomial coefficients polys).eval x at h
  rw [weighted_lane_eval] at h
  unfold weightedVirtualOracle at h
  rw [weighted_values_delta coefficients _ i (by simp [size,sourceShape]) (by omega) delta,
    weighted_values_delta coefficients _ i (by simp [size,polyShape]) (by omega) delta] at h
  exact h

/-- The SAME agreement set supports every recovered lane simultaneously.
No per-functional choice of a different representative is introduced. -/
theorem joint_representative_lane_mass (layout : GKRJointLayout) (metadata : List GKRSourceLane)
    (valid : ∀ lane∈metadata,lane.WellFormed layout)
    (geometry : CanonicalLaneSelectors layout metadata)
    (domain : List K) (weight : K → Nat) (D T : Nat)
    (sources : List (K → K)) (polys : List (Poly K))
    (sourceShape : sources.length=metadata.length)
    (representative : JointBetaRepresentative domain weight (heterogeneousJointDimension layout) D T
      (metadata.map (heterogeneousJointBeta layout)) sources polys) :
    T≤consistencyMass domain weight (fun x => ∀ i,i<metadata.length →
      (sources.map (fun f => f x)).getD i 0=(polys.map (fun p => p.eval x)).getD i 0) := by
  obtain ⟨shape,degrees,mass⟩ := representative
  apply Nat.le_trans mass
  apply consistency_mass_mono
  intro x hx agree
  exact joint_lane_pointwise_agreement layout metadata valid geometry sources polys sourceShape
    (by omega) x agree
end NearCompression
