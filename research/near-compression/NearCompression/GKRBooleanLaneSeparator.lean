import NearCompression.GKRMetadataValidity
namespace NearCompression
open Lean.Grind ZkFormal.Algebra ArenaCore.Security
variable {K : Type} [Field K]

theorem row_mle_at_zero (n : Nat) (f : Nat → K) : genericRowMLE n f (fun _ => 0)=f 0 := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih => simp only [genericRowMLE,ih]; grind

private theorem sum_add (xs : List Nat) (f g : Nat → K) :
    (xs.map (fun i => f i+g i)).sum=(xs.map f).sum+(xs.map g).sum := by
  induction xs with
  | nil => simp; grind
  | cons x xs ih => simp only [List.map_cons,List.sum_cons,ih]; grind

theorem upper_zeta_at_zero (n : Nat) (f : Nat → K) : upperZeta n f 0=cubeSum n f := by
  induction n generalizing f with
  | zero => simp [upperZeta,cubeSum]; grind
  | succ n ih =>
    simp only [upperZeta,Nat.zero_mod,Nat.zero_div,ite_true,ih]
    rw [cube_sum_split]
    exact sum_add _ _ _

theorem row_equality_mass (n : Nat) (point : Nat → K) :
    cubeSum n (rowEqualityWeight n point)=1 := by
  have one : genericRowMLE n (fun _ => (1:K)) point=1 := by
    induction n generalizing point with
    | zero => rfl
    | succ n ih => simp only [genericRowMLE,ih]; grind
  have h := row_equality_dot n point (fun _ => (1:K))
  have f : (fun i => rowEqualityWeight n point i*1)=rowEqualityWeight n point := by funext i; grind
  rw [f,one] at h
  exact h

/-- At zero PCS coordinates the current contribution is the sum of all
current slots. Next slots are required zero, not silently discarded. -/
theorem heterogeneous_beta_zero_current (m : Nat) (lane : GKRSourceLane)
    (rowpoint left right : Nat → K) (gamma : K)
    (noNext : ∀ c,c<2^lane.packingLog → heterogeneousColumnWeight m lane true left right gamma c=0) :
    heterogeneousLaneBeta m lane rowpoint left right (fun _ => 0) gamma=
      cubeSum lane.packingLog (heterogeneousColumnWeight m lane false left right gamma) := by
  rw [heterogeneousLaneBeta,row_mle_at_zero]
  simp only [heterogeneousLaneWeight,packedDualWeight,Nat.zero_div,Nat.zero_mod]
  rw [upper_zeta_at_zero,upper_zeta_at_zero,upper_zeta_at_zero,row_equality_mass]
  have zero : cubeSum lane.packingLog (heterogeneousColumnWeight m lane true left right gamma)=0 := by
    unfold cubeSum
    have eq : (List.range (2^lane.packingLog)).map (heterogeneousColumnWeight m lane true left right gamma)=
        (List.range (2^lane.packingLog)).map (fun _ => (0:K)) := by
      apply List.map_congr_left
      intro c hc
      exact noNext c (List.mem_range.mp hc)
    rw [eq]
    induction List.range (2^lane.packingLog) with
    | nil => rfl
    | cons c cs ih => simp only [List.map_cons,List.sum_cons,ih]; grind
  rw [zero]
  grind

theorem row_equality_boolean_selector (m : Nat) (bits : Nat → Bool) (slot : Nat)
    (bound : slot<2^m) :
    rowEqualityWeight m (genericRowBooleanPoint bits) slot=
      if slot=genericRowBitIndex m bits then (1:K) else 0 := by
  induction m generalizing bits slot with
  | zero =>
    have h : slot=0 := by simp only [Nat.pow_zero] at bound; omega
    subst slot
    simp [rowEqualityWeight,genericRowBitIndex]
  | succ m ih =>
    have half : slot/2<2^m := by rw [Nat.pow_succ] at bound; omega
    change (if slot%2=0 then 1-(if bits 0 then (1:K) else 0) else (if bits 0 then 1 else 0))*
      rowEqualityWeight m (genericRowBooleanPoint (fun i => bits (i+1))) (slot/2)=_
    rw [ih _ _ half]
    simp only [genericRowBitIndex]
    by_cases h : bits 0=true <;> simp only [h,ite_false,ite_true]
    all_goals split <;> split <;> split <;> grind

/-- Exact slot delta with no assumed private-weight vector. -/
theorem heterogeneous_column_boolean_selector (layout : GKRJointLayout) (lane : GKRSourceLane)
    (valid : lane.WellFormed layout) (bits : Nat → Bool) (next : Bool) (col : Nat)
    (right : Nat → K) :
    heterogeneousColumnWeight layout.inputLog lane next (genericRowBooleanPoint bits) right 0 col=
      if lane.group*2^lane.packingLog+col<lane.width ∧
        lane.inputStart+(if next then lane.nextOffset else 0)+lane.group*2^lane.packingLog+col=
          genericRowBitIndex layout.inputLog bits then 1 else 0 := by
  unfold heterogeneousColumnWeight
  by_cases live : lane.group*2^lane.packingLog+col<lane.width
  · have bound : lane.inputStart+(if next then lane.nextOffset else 0)+(lane.group*2^lane.packingLog+col)<2^layout.inputLog := by
      obtain ⟨_,_,a,b,c⟩ := valid
      cases next <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega
    rw [ite_eq_left live,row_equality_boolean_selector _ _ _ bound]
    simp only [live,true_and,Nat.add_assoc]
    grind
  · simp only [live,ite_false,false_and]

private theorem list_sum_append (a b : List K) : (a++b).sum=a.sum+b.sum := by
  induction a with
  | nil => simp; grind
  | cons x xs ih => simp only [List.cons_append,List.sum_cons,ih]; grind

private theorem sum_delta (N chosen : Nat) :
    ((List.range N).map (fun i => if i=chosen then (1:K) else 0)).sum=
      if chosen<N then 1 else 0 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ,List.map_append,list_sum_append,ih]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
    by_cases a : chosen<N <;> by_cases b : N=chosen <;> by_cases c : chosen<N+1 <;> simp_all <;> grind

def GKRSourceLane.LiveSlot (lane : GKRSourceLane) (next : Bool) (slot : Nat) : Prop :=
  ∃ c,c<2^lane.packingLog ∧ lane.group*2^lane.packingLog+c<lane.width ∧
    lane.inputStart+(if next then lane.nextOffset else 0)+lane.group*2^lane.packingLog+c=slot

/-- A selected live current slot contributes exactly one, even in a partial
packed lane. No next-slot collision is permitted. -/
theorem heterogeneous_beta_select_live (layout : GKRJointLayout) (lane : GKRSourceLane)
    (valid : lane.WellFormed layout) (bits : Nat → Bool) (rowpoint right : Nat → K)
    (live : lane.LiveSlot false (genericRowBitIndex layout.inputLog bits))
    (noNext : ¬lane.LiveSlot true (genericRowBitIndex layout.inputLog bits)) :
    heterogeneousLaneBeta layout.inputLog lane rowpoint (genericRowBooleanPoint bits) right (fun _ => 0) 0=1 := by
  have nextZero (c : Nat) (hc : c<2^lane.packingLog) :
      heterogeneousColumnWeight layout.inputLog lane true (genericRowBooleanPoint bits) right 0 c=0 := by
    rw [heterogeneous_column_boolean_selector layout lane valid]
    apply ite_eq_right
    intro h
    exact noNext ⟨c,hc,h.1,h.2⟩
  rw [heterogeneous_beta_zero_current _ _ _ _ _ _ nextZero]
  obtain ⟨chosen,hc,hl,hs⟩ := live
  have weights : (List.range (2^lane.packingLog)).map
      (heterogeneousColumnWeight layout.inputLog lane false (genericRowBooleanPoint bits) right 0)=
      (List.range (2^lane.packingLog)).map (fun c => if c=chosen then (1:K) else 0) := by
    apply List.map_congr_left
    intro c mem
    rw [heterogeneous_column_boolean_selector layout lane valid]
    congr 1
    apply propext
    simp only [Bool.false_eq_true,ite_false,Nat.add_zero] at hs ⊢
    constructor
    · intro h; omega
    · intro h; subst c; exact ⟨hl,hs⟩
  unfold cubeSum
  rw [weights,sum_delta,ite_eq_left hc]

/-- Any lane with no current or next occurrence of the selected slot has
zero beta at this Boolean separator. -/
theorem heterogeneous_beta_select_absent (layout : GKRJointLayout) (lane : GKRSourceLane)
    (valid : lane.WellFormed layout) (bits : Nat → Bool) (rowpoint right : Nat → K)
    (absent : ∀ next,¬lane.LiveSlot next (genericRowBitIndex layout.inputLog bits)) :
    heterogeneousLaneBeta layout.inputLog lane rowpoint (genericRowBooleanPoint bits) right (fun _ => 0) 0=0 := by
  have zeros (next : Bool) (c : Nat) (hc : c<2^lane.packingLog) :
      heterogeneousColumnWeight layout.inputLog lane next (genericRowBooleanPoint bits) right 0 c=0 := by
    rw [heterogeneous_column_boolean_selector layout lane valid]
    apply ite_eq_right
    intro h
    exact absent next ⟨c,hc,h.1,h.2⟩
  rw [heterogeneous_beta_zero_current _ _ _ _ _ _ (zeros true)]
  unfold cubeSum
  have eq : (List.range (2^lane.packingLog)).map
      (heterogeneousColumnWeight layout.inputLog lane false (genericRowBooleanPoint bits) right 0)=
      (List.range (2^lane.packingLog)).map (fun _ => (0:K)) := by
    apply List.map_congr_left
    intro c hc
    exact zeros false c (List.mem_range.mp hc)
  rw [eq]
  induction List.range (2^lane.packingLog) with
  | nil => rfl
  | cons c cs ih => simp only [List.map_cons,List.sum_cons,ih]; grind

def GKRSourceLane.slotStart (lane : GKRSourceLane) (next : Bool) : Nat :=
  lane.inputStart+(if next then lane.nextOffset else 0)+lane.group*2^lane.packingLog

def GKRSourceLane.slotEnd (lane : GKRSourceLane) (next : Bool) : Nat :=
  min (lane.inputStart+(if next then lane.nextOffset else 0)+lane.width)
    (lane.slotStart next+2^lane.packingLog)

/-- Exact half-open live-slot interval, including partial and empty groups. -/
theorem live_slot_interval (lane : GKRSourceLane) (next : Bool) (slot : Nat) :
    lane.LiveSlot next slot ↔ lane.slotStart next≤slot ∧ slot<lane.slotEnd next := by
  simp only [GKRSourceLane.LiveSlot,GKRSourceLane.slotStart,GKRSourceLane.slotEnd,Nat.lt_min]
  constructor
  · rintro ⟨c,a,b,h⟩; omega
  · intro h
    refine ⟨slot-(lane.inputStart+(if next then lane.nextOffset else 0)+lane.group*2^lane.packingLog),?_,?_,?_⟩ <;> omega

/-- Numerical nonoverlap certificates discharge slot exclusion directly. -/
theorem live_slot_disjoint (a b : GKRSourceLane) (na nb : Bool)
    (separate : a.slotEnd na≤b.slotStart nb ∨ b.slotEnd nb≤a.slotStart na)
    (slot : Nat) (live : a.LiveSlot na slot) : ¬b.LiveSlot nb slot := by
  rw [live_slot_interval] at live ⊢
  omega

/-- The ceil(width/packing) enumeration never creates an empty group. -/
theorem metadata_lane_nonempty (table : GKRTableMetadata) (lane : GKRSourceLane)
    (member : lane∈gkrMetadataLanes table) :
    lane.group*2^lane.packingLog<lane.width := by
  have ceil (w p g : Nat) (pos : 0<p) (hg : g<(w+p-1)/p) : g*p<w := by
    have h := (Nat.lt_div_iff_mul_lt pos).mp hg
    omega
  simp only [gkrMetadataLanes,List.mem_append,List.mem_map] at member
  rcases member with ⟨g,hg,rfl⟩ | ⟨g,hg,rfl⟩
  · exact ceil _ _ _ (Nat.two_pow_pos _) (List.mem_range.mp hg)
  · exact ceil _ _ _ (Nat.two_pow_pos _) (List.mem_range.mp hg)

theorem nonempty_lane_first_slot (lane : GKRSourceLane)
    (nonempty : lane.group*2^lane.packingLog<lane.width) :
    lane.LiveSlot false (lane.slotStart false) := by
  exact ⟨0,Nat.two_pow_pos _,by simpa using nonempty,by simp [GKRSourceLane.slotStart]⟩
end NearCompression
