import NearCompression.SHA384BatchedCore

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 NearSpecV3.SHA512
set_option maxRecDepth 65536

theorem sha384_batch_constraint (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384BatchedAir n) pub tr) (r : Nat) (hr : r<tr.height 0)
    (e : Expr) (he : e∈sha384BatchCoreConstraints (sha384PaddedLength n/128)) :
    e.eval tr 0 r pub=0 := h.constr 0 (by simp [sha384BatchedAir]) r hr e he

theorem sha384_batch_active_boolean (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384BatchedAir n) pub tr) (r : Nat) (hr : r<tr.height 0) :
    tr.cell 0 r 5232=0 ∨ tr.cell 0 r 5232=1 := by
  have hc := sha384_batch_constraint n pub tr h r hr (instructionBitConstraint 5232)
    (by simp [sha384BatchCoreConstraints])
  change tr.cell 0 r 5232 * (tr.cell 0 r 5232 + -(1:Fp))=0 at hc
  grind

theorem sha384_batch_first (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384BatchedAir n) pub tr) :
    tr.cell 0 0 5232=1 ∧ tr.cell 0 0 5233=0 ∧
    ∀ i,i<80 → tr.cell 0 0 (5152+i)=if i=0 then 1 else 0 := by
  have active := sha384_batch_constraint n pub tr h 0 (Nat.two_pow_pos _)
    (.mul .isFirst (.add sha384BatchActive (.neg (.const 1)))) (by simp [sha384BatchCoreConstraints])
  have tag := sha384_batch_constraint n pub tr h 0 (Nat.two_pow_pos _)
    (.mul .isFirst sha384BatchTag) (by simp [sha384BatchCoreConstraints])
  change (1:Fp)*(tr.cell 0 0 5232 + -1)=0 at active
  change (1:Fp)*tr.cell 0 0 5233=0 at tag
  refine ⟨by grind,by grind,?_⟩
  intro i hi
  have phase := sha384_batch_constraint n pub tr h 0 (Nat.two_pow_pos _)
    (.mul .isFirst (.add (sha384BatchPhase i) (.neg (.const (if i=0 then 1 else 0)))))
    (by simp only [sha384BatchCoreConstraints,List.mem_append]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (List.mem_map.mpr ⟨i,List.mem_range.mpr hi,rfl⟩))))))
  by_cases zero : i=0
  · subst i;change (1:Fp)*(tr.cell 0 0 (5152+0)+ -1)=0 at phase;simp only [ite_true];grind
  · change (1:Fp)*(tr.cell 0 0 (5152+i)+ -Fp.ofNat (if i=0 then 1 else 0))=0 at phase
    rw [ite_eq_right zero] at phase ⊢
    change (1:Fp)*(tr.cell 0 0 (5152+i)+ -0)=0 at phase
    grind

theorem sha384_batch_no_restart (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384BatchedAir n) pub tr) (r : Nat) (hr : r+1<tr.height 0)
    (active : tr.cell 0 (r+1) 5232=1) : tr.cell 0 r 5232=1 := by
  have hc := sha384_batch_constraint n pub tr h r (by omega)
    (.mul .isTransition (.mul (.col 5232 true) (.add (.const 1) (.neg sha384BatchActive))))
    (by simp [sha384BatchCoreConstraints])
  simp only [Expr.eval,Expr.evalWith,rowEnv,sha384BatchActive,Nat.mod_eq_of_lt hr,Nat.ne_of_lt hr,ite_false,ite_true] at hc
  rw [active] at hc
  grind

theorem sha384_batch_phase_step (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384BatchedAir n) pub tr) (r i : Nat) (hr : r+1<tr.height 0) (hi : i<80) :
    tr.cell 0 (r+1) (5152+i)=tr.cell 0 (r+1) 5232 * tr.cell 0 r (5152+(if i=0 then 79 else i-1)) := by
  have hc := sha384_batch_constraint n pub tr h r (by omega)
    (.mul .isTransition (.add (.col (5152+i) true) (.neg (.mul (.col 5232 true) (sha384BatchPhase (if i=0 then 79 else i-1))))))
    (by simp only [sha384BatchCoreConstraints,List.mem_append];exact Or.inl (Or.inl (Or.inl (Or.inr (List.mem_map.mpr ⟨i,List.mem_range.mpr hi,rfl⟩)))))
  simp only [Expr.eval,Expr.evalWith,rowEnv,sha384BatchPhase,Nat.mod_eq_of_lt hr,Nat.ne_of_lt hr,ite_false,ite_true] at hc
  grind

/-- Active rows have a canonical modulo80 phase, derived from reset equations. -/
theorem sha384_batch_active_phase (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384BatchedAir n) pub tr) (r : Nat) (hr : r<tr.height 0)
    (active : tr.cell 0 r 5232=1) (i : Nat) (hi : i<80) :
    tr.cell 0 r (5152+i)=if i=r%80 then 1 else 0 := by
  induction r generalizing i with
  | zero => simpa using (sha384_batch_first n pub tr h).2.2 i hi
  | succ r ih =>
    have prev := sha384_batch_no_restart n pub tr h r hr active
    have idx : (if i=0 then 79 else i-1)<80 := by split <;> omega
    have phase := ih (by omega) prev (if i=0 then 79 else i-1) idx
    have step := sha384_batch_phase_step n pub tr h r i hr hi
    rw [active,phase] at step
    have eq : (if i=0 then 79 else i-1)=r%80 ↔ i=(r+1)%80 := by
      by_cases zero : i=0 <;> simp only [zero,ite_true,ite_false] <;> omega
    simp only [eq] at step
    grind

theorem sha384_batch_active_prefix (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384BatchedAir n) pub tr) (r : Nat) (hr : r<tr.height 0)
    (active : tr.cell 0 r 5232=1) (s : Nat) (hs : s≤r) : tr.cell 0 s 5232=1 := by
  induction r with
  | zero =>
    have eq : s=0 := by omega
    subst s
    exact active
  | succ r ih =>
    by_cases eq : s=r+1
    · subst s;exact active
    · exact ih (by omega) (sha384_batch_no_restart n pub tr h r hr active) (by omega)

theorem sha384_batch_inactive_phase (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384BatchedAir n) pub tr) (r : Nat) (hr : r<tr.height 0)
    (inactive : tr.cell 0 r 5232=0) (i : Nat) (hi : i<80) : tr.cell 0 r (5152+i)=0 := by
  cases r with
  | zero => have first := (sha384_batch_first n pub tr h).1;rw [inactive] at first;exact False.elim ((by decide : (0:Fp)≠1) first)
  | succ r =>
    have step := sha384_batch_phase_step n pub tr h r i hr hi
    rw [inactive] at step
    grind

theorem sha384_batch_tag_step (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384BatchedAir n) pub tr) (r : Nat) (hr : r+1<tr.height 0)
    (active : tr.cell 0 (r+1) 5232=1) :
    tr.cell 0 (r+1) 5233=tr.cell 0 r 5233+tr.cell 0 r (5152+79) := by
  have hc := sha384_batch_constraint n pub tr h r (by omega)
    (.mul .isTransition (.mul (.col 5232 true)
     (.add (.col 5233 true) (.neg (.add sha384BatchTag (sha384BatchPhase 79))))))
    (by simp [sha384BatchCoreConstraints])
  simp only [Expr.eval,Expr.evalWith,rowEnv,sha384BatchPhase,sha384BatchTag,Nat.mod_eq_of_lt hr,Nat.ne_of_lt hr,ite_false,ite_true] at hc
  rw [active] at hc
  grind

theorem sha384_batch_active_tag (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384BatchedAir n) pub tr) (r : Nat) (hr : r<tr.height 0)
    (active : tr.cell 0 r 5232=1) : tr.cell 0 r 5233=Fp.ofNat (r/80) := by
  induction r with
  | zero => exact (sha384_batch_first n pub tr h).2.1
  | succ r ih =>
    have prev := sha384_batch_no_restart n pub tr h r hr active
    have tag := ih (by omega) prev
    have phase := sha384_batch_active_phase n pub tr h r (by omega) prev 79 (by decide)
    have step := sha384_batch_tag_step n pub tr h r hr active
    rw [tag,phase] at step
    by_cases last : 79=r%80
    · rw [ite_eq_left last] at step
      have quotient : (r+1)/80=r/80+1 := by omega
      rw [quotient]
      have cast : Fp.ofNat (r/80+1)=Fp.ofNat (r/80)+1 := Lean.Grind.Semiring.natCast_add _ _
      rw [cast]
      exact step
    · rw [ite_eq_right last] at step
      have quotient : (r+1)/80=r/80 := by omega
      rw [quotient]
      grind


theorem sha384_batch_height_small (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384BatchedAir n) pub tr) : tr.height 0<P := by
  have log := h.logBound 0 (by simp [sha384BatchedAir])
  have upper : tr.log 0≤22 := log.2
  have power := Nat.pow_le_pow_right (by decide : 1≤2) upper
  change 2^tr.log 0<P
  unfold P
  omega

/-- A stopping active row must be precisely the final phase of the final tag. -/
theorem sha384_batch_stop_index (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384BatchedAir n) pub tr) (bound : sha384PaddedLength n/128<P)
    (r : Nat) (hr : r<tr.height 0) (active : tr.cell 0 r 5232=1)
    (stop : sha384BatchStop.eval tr 0 r pub=1) : r+1=80*(sha384PaddedLength n/128) := by
  have phase := sha384_batch_constraint n pub tr h r hr
    (.mul sha384BatchStop (.add (sha384BatchPhase 79) (.neg (.const 1))))
    (by simp [sha384BatchCoreConstraints])
  have tag := sha384_batch_constraint n pub tr h r hr
    (.mul sha384BatchStop (.add sha384BatchTag (.neg (.const (sha384PaddedLength n/128-1)))))
    (by simp [sha384BatchCoreConstraints])
  change sha384BatchStop.eval tr 0 r pub*(tr.cell 0 r (5152+79)+ -(1:Fp))=0 at phase
  change sha384BatchStop.eval tr 0 r pub*(tr.cell 0 r 5233+ -Fp.ofNat (sha384PaddedLength n/128-1))=0 at tag
  rw [stop,sha384_batch_active_phase n pub tr h r hr active 79 (by decide)] at phase
  rw [stop,sha384_batch_active_tag n pub tr h r hr active] at tag
  have last : 79=r%80 := by
    by_cases eq : 79=r%80
    · exact eq
    · simp only [ite_eq_right eq] at phase
      have bad : (0:Fp)=1 := by grind
      exact False.elim ((by decide : (0:Fp)≠1) bad)
  have tags : Fp.ofNat (r/80)=Fp.ofNat (sha384PaddedLength n/128-1) := by grind
  have small := sha384_batch_height_small n pub tr h
  have same := congrArg Fp.toNat tags
  rw [Fp.toNat_ofNat,Fp.toNat_ofNat,Nat.mod_eq_of_lt (by omega : r/80<P),
    Nat.mod_eq_of_lt (by omega : sha384PaddedLength n/128-1<P)] at same
  have pos : 0<sha384PaddedLength n/128 := by unfold sha384PaddedLength;omega
  omega

theorem sha384_batch_stop_last (_n : Nat) (pub : List Fp) (tr : Trace Fp)
    (r : Nat) (last : r+1=tr.height 0) (active : tr.cell 0 r 5232=1) :
    sha384BatchStop.eval tr 0 r pub=1 := by
  simp only [sha384BatchStop,sha384BatchActive,Expr.eval,Expr.evalWith,rowEnv,last,Bool.false_eq_true,ite_true,ite_false]
  rw [active]
  grind

theorem sha384_batch_stop_next_inactive (_n : Nat) (pub : List Fp) (tr : Trace Fp)
    (r : Nat) (next : r+1<tr.height 0) (active : tr.cell 0 r 5232=1)
    (inactive : tr.cell 0 (r+1) 5232=0) : sha384BatchStop.eval tr 0 r pub=1 := by
  simp only [sha384BatchStop,sha384BatchActive,Expr.eval,Expr.evalWith,rowEnv,Nat.mod_eq_of_lt next,
    Nat.ne_of_lt next,Bool.false_eq_true,ite_true,ite_false]
  rw [active,inactive]
  grind

theorem sha384_batch_required_active (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384BatchedAir n) pub tr) (bound : sha384PaddedLength n/128<P)
    (r : Nat) (hr : r<tr.height 0) (required : r<80*(sha384PaddedLength n/128)) :
    tr.cell 0 r 5232=1 := by
  induction r with
  | zero => exact (sha384_batch_first n pub tr h).1
  | succ r ih =>
    have active := ih (by omega) (by omega)
    rcases sha384_batch_active_boolean n pub tr h (r+1) hr with inactive | result
    · have stop := sha384_batch_stop_next_inactive n pub tr r hr active inactive
      have index := sha384_batch_stop_index n pub tr h bound r (by omega) active stop
      omega
    · exact result

theorem sha384_batch_capacity (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384BatchedAir n) pub tr) (bound : sha384PaddedLength n/128<P) :
    80*(sha384PaddedLength n/128)≤tr.height 0 := by
  by_cases fits : 80*(sha384PaddedLength n/128)≤tr.height 0
  · exact fits
  · have pos : 0<tr.height 0 := Nat.two_pow_pos _
    have active := sha384_batch_required_active n pub tr h bound (tr.height 0-1) (by omega) (by omega)
    have stop := sha384_batch_stop_last n pub tr (tr.height 0-1) (by omega) active
    have index := sha384_batch_stop_index n pub tr h bound (tr.height 0-1) (by omega) active stop
    omega


theorem sha384_batch_active_bounded (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384BatchedAir n) pub tr) (bound : sha384PaddedLength n/128<P)
    (r : Nat) (hr : r<tr.height 0) (active : tr.cell 0 r 5232=1) :
    r<80*(sha384PaddedLength n/128) := by
  have descend (k : Nat) : ∀ r,r<tr.height 0 → tr.height 0-r≤k → tr.cell 0 r 5232=1 → r<80*(sha384PaddedLength n/128) := by
    induction k with
    | zero => intro r hr distance active;omega
    | succ k ih =>
      intro r hr distance active
      by_cases last : r+1=tr.height 0
      · have stop := sha384_batch_stop_last n pub tr r last active
        have index := sha384_batch_stop_index n pub tr h bound r hr active stop
        omega
      · have next : r+1<tr.height 0 := by omega
        rcases sha384_batch_active_boolean n pub tr h (r+1) next with inactive | nextActive
        · have stop := sha384_batch_stop_next_inactive n pub tr r next active inactive
          have index := sha384_batch_stop_index n pub tr h bound r hr active stop
          omega
        · have result := ih (r+1) next (by omega) nextActive
          omega
  exact descend (tr.height 0-r) r hr (by omega) active

/-- Exact active prefix, with its length derived from stop/tag constraints. -/
theorem sha384_batch_active_iff (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384BatchedAir n) pub tr) (bound : sha384PaddedLength n/128<P)
    (r : Nat) (hr : r<tr.height 0) :
    tr.cell 0 r 5232=1 ↔ r<80*(sha384PaddedLength n/128) :=
  ⟨sha384_batch_active_bounded n pub tr h bound r hr,
   sha384_batch_required_active n pub tr h bound r hr⟩

/-- Each requested block has exactly its canonical80active rows; this is the
stable interface for extracting local gadgets and within-segment transitions. -/
theorem sha384_batch_segment_metadata (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384BatchedAir n) pub tr) (bound : sha384PaddedLength n/128<P)
    (block phase : Nat) (hb : block<sha384PaddedLength n/128) (hp : phase<80) :
    80*block+phase<tr.height 0 ∧ tr.cell 0 (80*block+phase) 5232=1 ∧
    tr.cell 0 (80*block+phase) 5233=Fp.ofNat block ∧
    ∀ i,i<80 → tr.cell 0 (80*block+phase) (5152+i)=if i=phase then 1 else 0 := by
  have capacity := sha384_batch_capacity n pub tr h bound
  have hr : 80*block+phase<tr.height 0 := by omega
  have active := sha384_batch_required_active n pub tr h bound (80*block+phase) hr (by omega)
  have tag := sha384_batch_active_tag n pub tr h (80*block+phase) hr active
  have div : (80*block+phase)/80=block := by omega
  have mod : (80*block+phase)%80=phase := by omega
  rw [div] at tag
  refine ⟨hr,active,tag,?_⟩
  intro i hi
  simpa only [mod] using sha384_batch_active_phase n pub tr h (80*block+phase) hr active i hi


end NearCompression
