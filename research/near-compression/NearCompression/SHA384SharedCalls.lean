import NearCompression.SHA384SharedCore

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 NearSpecV3.SHA512
set_option maxRecDepth 65536

def sharedCallActive : Expr := .col 2 false
def sharedCallTag : Expr := .col 0 false
def sharedCallPhase (i : Nat) : Expr := .col (3+i) false
def sharedCallStop : Expr := sharedStop 2

theorem sha384_call_constraint (f0 f1 : List (Nat × Nat)) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384SharedAir f0 f1) pub tr) (r : Nat) (hr : r<tr.height 3)
    (e : Expr) (he : e∈sha384SharedCalls.constraints) :
    e.eval tr 3 r pub=0 := h.constr 3 (by simp [sha384SharedAir]) r hr e he

theorem sha384_call_active_boolean (f0 f1 : List (Nat × Nat)) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384SharedAir f0 f1) pub tr) (r : Nat) (hr : r<tr.height 3) :
    tr.cell 3 r 2=0 ∨ tr.cell 3 r 2=1 := by
  have hc := sha384_call_constraint f0 f1 pub tr h r hr (instructionBitConstraint 2)
    (by simp [sha384SharedCalls,sharedSub])
  change tr.cell 3 r 2 * (tr.cell 3 r 2 + -(1:Fp))=0 at hc
  grind

theorem sha384_call_first (f0 f1 : List (Nat × Nat)) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384SharedAir f0 f1) pub tr) :
    tr.cell 3 0 2=1 ∧ tr.cell 3 0 0=0 ∧
    ∀ i,i<3 → tr.cell 3 0 (3+i)=if i=0 then 1 else 0 := by
  have active := sha384_call_constraint f0 f1 pub tr h 0 (Nat.two_pow_pos _)
    (.mul .isFirst (.add sharedCallActive (.neg (.const 1)))) (by simp [sha384SharedCalls,sharedSub,sharedCallActive])
  have tag := sha384_call_constraint f0 f1 pub tr h 0 (Nat.two_pow_pos _)
    (.mul .isFirst sharedCallTag) (by simp [sha384SharedCalls,sharedSub,sharedCallTag])
  change (1:Fp)*(tr.cell 3 0 2 + -1)=0 at active
  change (1:Fp)*tr.cell 3 0 0=0 at tag
  refine ⟨by grind,by grind,?_⟩
  intro i hi
  have phase := sha384_call_constraint f0 f1 pub tr h 0 (Nat.two_pow_pos _)
    (.mul .isFirst (.add (sharedCallPhase i) (.neg (.const (if i=0 then 1 else 0)))))
    (by
      have cases : i=0 ∨ i=1 ∨ i=2 := by omega
      rcases cases with rfl | rfl | rfl <;> simp [sha384SharedCalls,sharedSub,sharedCallPhase,List.range_succ])
  by_cases zero : i=0
  · subst i;change (1:Fp)*(tr.cell 3 0 (3+0)+ -1)=0 at phase;simp only [ite_true];grind
  · change (1:Fp)*(tr.cell 3 0 (3+i)+ -Fp.ofNat (if i=0 then 1 else 0))=0 at phase
    rw [ite_eq_right zero] at phase ⊢
    change (1:Fp)*(tr.cell 3 0 (3+i)+ -0)=0 at phase
    grind

theorem sha384_call_no_restart (f0 f1 : List (Nat × Nat)) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384SharedAir f0 f1) pub tr) (r : Nat) (hr : r+1<tr.height 3)
    (active : tr.cell 3 (r+1) 2=1) : tr.cell 3 r 2=1 := by
  have hc := sha384_call_constraint f0 f1 pub tr h r (by omega)
    (.mul .isTransition (.mul (.col 2 true) (.add (.const 1) (.neg sharedCallActive))))
    (by simp [sha384SharedCalls,sharedSub,sharedCallActive])
  simp only [Expr.eval,Expr.evalWith,rowEnv,sharedCallActive,Nat.mod_eq_of_lt hr,Nat.ne_of_lt hr,ite_false,ite_true] at hc
  rw [active] at hc
  grind

theorem sha384_call_phase_step (f0 f1 : List (Nat × Nat)) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384SharedAir f0 f1) pub tr) (r i : Nat) (hr : r+1<tr.height 3) (hi : i<3) :
    tr.cell 3 (r+1) (3+i)=tr.cell 3 (r+1) 2 * tr.cell 3 r (3+(if i=0 then 2 else i-1)) := by
  have hc := sha384_call_constraint f0 f1 pub tr h r (by omega)
    (.mul .isTransition (.add (.col (3+i) true) (.neg (.mul (.col 2 true) (sharedCallPhase (if i=0 then 2 else i-1))))))
    (by
      have cases : i=0 ∨ i=1 ∨ i=2 := by omega
      rcases cases with rfl | rfl | rfl <;> simp [sha384SharedCalls,sharedSub,sharedCallPhase,List.range_succ])
  simp only [Expr.eval,Expr.evalWith,rowEnv,sharedCallPhase,Nat.mod_eq_of_lt hr,Nat.ne_of_lt hr,ite_false,ite_true] at hc
  grind

/-- Active rows have a canonical modulo3 phase, derived from reset equations. -/
theorem sha384_call_active_phase (f0 f1 : List (Nat × Nat)) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384SharedAir f0 f1) pub tr) (r : Nat) (hr : r<tr.height 3)
    (active : tr.cell 3 r 2=1) (i : Nat) (hi : i<3) :
    tr.cell 3 r (3+i)=if i=r%3 then 1 else 0 := by
  induction r generalizing i with
  | zero => simpa using (sha384_call_first f0 f1 pub tr h).2.2 i hi
  | succ r ih =>
    have prev := sha384_call_no_restart f0 f1 pub tr h r hr active
    have idx : (if i=0 then 2 else i-1)<3 := by split <;> omega
    have phase := ih (by omega) prev (if i=0 then 2 else i-1) idx
    have step := sha384_call_phase_step f0 f1 pub tr h r i hr hi
    rw [active,phase] at step
    have eq : (if i=0 then 2 else i-1)=r%3 ↔ i=(r+1)%3 := by
      by_cases zero : i=0 <;> simp only [zero,ite_true,ite_false] <;> omega
    simp only [eq] at step
    grind

theorem sha384_call_active_prefix (f0 f1 : List (Nat × Nat)) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384SharedAir f0 f1) pub tr) (r : Nat) (hr : r<tr.height 3)
    (active : tr.cell 3 r 2=1) (s : Nat) (hs : s≤r) : tr.cell 3 s 2=1 := by
  induction r with
  | zero =>
    have eq : s=0 := by omega
    subst s
    exact active
  | succ r ih =>
    by_cases eq : s=r+1
    · subst s;exact active
    · exact ih (by omega) (sha384_call_no_restart f0 f1 pub tr h r hr active) (by omega)

theorem sha384_call_inactive_phase (f0 f1 : List (Nat × Nat)) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384SharedAir f0 f1) pub tr) (r : Nat) (hr : r<tr.height 3)
    (inactive : tr.cell 3 r 2=0) (i : Nat) (hi : i<3) : tr.cell 3 r (3+i)=0 := by
  cases r with
  | zero => have first := (sha384_call_first f0 f1 pub tr h).1;rw [inactive] at first;exact False.elim ((by decide : (0:Fp)≠1) first)
  | succ r =>
    have step := sha384_call_phase_step f0 f1 pub tr h r i hr hi
    rw [inactive] at step
    grind

theorem sha384_call_tag_step (f0 f1 : List (Nat × Nat)) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384SharedAir f0 f1) pub tr) (r : Nat) (hr : r+1<tr.height 3)
    (active : tr.cell 3 (r+1) 2=1) :
    tr.cell 3 (r+1) 0=tr.cell 3 r 0+tr.cell 3 r (3+2) := by
  have hc := sha384_call_constraint f0 f1 pub tr h r (by omega)
    (.mul .isTransition (.mul (.col 2 true)
     (.add (.col 0 true) (.neg (.add sharedCallTag (sharedCallPhase 2))))))
    (by simp [sha384SharedCalls,sharedSub,sharedCallTag,sharedCallPhase])
  simp only [Expr.eval,Expr.evalWith,rowEnv,sharedCallPhase,sharedCallTag,Nat.mod_eq_of_lt hr,Nat.ne_of_lt hr,ite_false,ite_true] at hc
  rw [active] at hc
  grind

theorem sha384_call_active_tag (f0 f1 : List (Nat × Nat)) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384SharedAir f0 f1) pub tr) (r : Nat) (hr : r<tr.height 3)
    (active : tr.cell 3 r 2=1) : tr.cell 3 r 0=Fp.ofNat (r/3) := by
  induction r with
  | zero => exact (sha384_call_first f0 f1 pub tr h).2.1
  | succ r ih =>
    have prev := sha384_call_no_restart f0 f1 pub tr h r hr active
    have tag := ih (by omega) prev
    have phase := sha384_call_active_phase f0 f1 pub tr h r (by omega) prev 2 (by decide)
    have step := sha384_call_tag_step f0 f1 pub tr h r hr active
    rw [tag,phase] at step
    by_cases last : 2=r%3
    · rw [ite_eq_left last] at step
      have quotient : (r+1)/3=r/3+1 := by omega
      rw [quotient]
      have cast : Fp.ofNat (r/3+1)=Fp.ofNat (r/3)+1 := Lean.Grind.Semiring.natCast_add _ _
      rw [cast]
      exact step
    · rw [ite_eq_right last] at step
      have quotient : (r+1)/3=r/3 := by omega
      rw [quotient]
      grind


theorem sha384_call_height_small (f0 f1 : List (Nat × Nat)) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384SharedAir f0 f1) pub tr) : tr.height 3<P := by
  have log := h.logBound 3 (by simp [sha384SharedAir])
  have upper : tr.log 3≤3 := log.2
  have power := Nat.pow_le_pow_right (by decide : 1≤2) upper
  change 2^tr.log 3<P
  unfold P
  omega

/-- A stopping active row must be precisely the final phase of the final tag. -/
theorem sha384_call_stop_index (f0 f1 : List (Nat × Nat)) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384SharedAir f0 f1) pub tr) 
    (r : Nat) (hr : r<tr.height 3) (active : tr.cell 3 r 2=1)
    (stop : sharedCallStop.eval tr 3 r pub=1) : r+1=3*(2) := by
  have phase := sha384_call_constraint f0 f1 pub tr h r hr
    (.mul sharedCallStop (.add (sharedCallPhase 2) (.neg (.const 1))))
    (by simp [sha384SharedCalls,sharedSub,sharedCallPhase,sharedCallStop])
  have tag := sha384_call_constraint f0 f1 pub tr h r hr
    (.mul sharedCallStop (.add sharedCallTag (.neg (.const (2-1)))))
    (by simp [sha384SharedCalls,sharedSub,sharedCallTag,sharedCallStop])
  change sharedCallStop.eval tr 3 r pub*(tr.cell 3 r (3+2)+ -(1:Fp))=0 at phase
  change sharedCallStop.eval tr 3 r pub*(tr.cell 3 r 0+ -Fp.ofNat (2-1))=0 at tag
  rw [stop,sha384_call_active_phase f0 f1 pub tr h r hr active 2 (by decide)] at phase
  rw [stop,sha384_call_active_tag f0 f1 pub tr h r hr active] at tag
  have last : 2=r%3 := by
    by_cases eq : 2=r%3
    · exact eq
    · simp only [ite_eq_right eq] at phase
      have bad : (0:Fp)=1 := by grind
      exact False.elim ((by decide : (0:Fp)≠1) bad)
  have tags : Fp.ofNat (r/3)=Fp.ofNat (2-1) := by grind
  have small := sha384_call_height_small f0 f1 pub tr h
  have same := congrArg Fp.toNat tags
  rw [Fp.toNat_ofNat,Fp.toNat_ofNat,Nat.mod_eq_of_lt (by omega : r/3<P),
    Nat.mod_eq_of_lt (by omega : 2-1<P)] at same
  have pos : 0<2 := by decide
  omega

theorem sha384_call_stop_last (_f0 _f1 : List (Nat × Nat)) (pub : List Fp) (tr : Trace Fp)
    (r : Nat) (last : r+1=tr.height 3) (active : tr.cell 3 r 2=1) :
    sharedCallStop.eval tr 3 r pub=1 := by
  simp only [sharedCallStop,sharedStop,sharedSub,Expr.eval,Expr.evalWith,rowEnv,last,Bool.false_eq_true,ite_true,ite_false]
  rw [active]
  grind

theorem sha384_call_stop_next_inactive (_f0 _f1 : List (Nat × Nat)) (pub : List Fp) (tr : Trace Fp)
    (r : Nat) (next : r+1<tr.height 3) (active : tr.cell 3 r 2=1)
    (inactive : tr.cell 3 (r+1) 2=0) : sharedCallStop.eval tr 3 r pub=1 := by
  simp only [sharedCallStop,sharedStop,sharedSub,Expr.eval,Expr.evalWith,rowEnv,Nat.mod_eq_of_lt next,
    Nat.ne_of_lt next,Bool.false_eq_true,ite_true,ite_false]
  rw [active,inactive]
  grind

theorem sha384_call_required_active (f0 f1 : List (Nat × Nat)) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384SharedAir f0 f1) pub tr) 
    (r : Nat) (hr : r<tr.height 3) (required : r<3*(2)) :
    tr.cell 3 r 2=1 := by
  induction r with
  | zero => exact (sha384_call_first f0 f1 pub tr h).1
  | succ r ih =>
    have active := ih (by omega) (by omega)
    rcases sha384_call_active_boolean f0 f1 pub tr h (r+1) hr with inactive | result
    · have stop := sha384_call_stop_next_inactive f0 f1 pub tr r hr active inactive
      have index := sha384_call_stop_index f0 f1 pub tr h r (by omega) active stop
      omega
    · exact result

theorem sha384_call_capacity (f0 f1 : List (Nat × Nat)) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384SharedAir f0 f1) pub tr)  :
    3*(2)≤tr.height 3 := by
  by_cases fits : 3*(2)≤tr.height 3
  · exact fits
  · have pos : 0<tr.height 3 := Nat.two_pow_pos _
    have active := sha384_call_required_active f0 f1 pub tr h (tr.height 3-1) (by omega) (by omega)
    have stop := sha384_call_stop_last f0 f1 pub tr (tr.height 3-1) (by omega) active
    have index := sha384_call_stop_index f0 f1 pub tr h (tr.height 3-1) (by omega) active stop
    omega


theorem sha384_call_active_bounded (f0 f1 : List (Nat × Nat)) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384SharedAir f0 f1) pub tr) 
    (r : Nat) (hr : r<tr.height 3) (active : tr.cell 3 r 2=1) :
    r<3*(2) := by
  have descend (k : Nat) : ∀ r,r<tr.height 3 → tr.height 3-r≤k → tr.cell 3 r 2=1 → r<3*(2) := by
    induction k with
    | zero => intro r hr distance active;omega
    | succ k ih =>
      intro r hr distance active
      by_cases last : r+1=tr.height 3
      · have stop := sha384_call_stop_last f0 f1 pub tr r last active
        have index := sha384_call_stop_index f0 f1 pub tr h r hr active stop
        omega
      · have next : r+1<tr.height 3 := by omega
        rcases sha384_call_active_boolean f0 f1 pub tr h (r+1) next with inactive | nextActive
        · have stop := sha384_call_stop_next_inactive f0 f1 pub tr r next active inactive
          have index := sha384_call_stop_index f0 f1 pub tr h r hr active stop
          omega
        · have result := ih (r+1) next (by omega) nextActive
          omega
  exact descend (tr.height 3-r) r hr (by omega) active

/-- Exact active prefix, with its length derived from stop/tag constraints. -/
theorem sha384_call_active_iff (f0 f1 : List (Nat × Nat)) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384SharedAir f0 f1) pub tr) 
    (r : Nat) (hr : r<tr.height 3) :
    tr.cell 3 r 2=1 ↔ r<3*(2) :=
  ⟨sha384_call_active_bounded f0 f1 pub tr h r hr,
   sha384_call_required_active f0 f1 pub tr h r hr⟩

/-- Each requested block has exactly its canonical3active rows; this is the
stable interface for extracting local gadgets and within-segment transitions. -/
theorem sha384_call_segment_metadata (f0 f1 : List (Nat × Nat)) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384SharedAir f0 f1) pub tr) 
    (block phase : Nat) (hb : block<2) (hp : phase<3) :
    3*block+phase<tr.height 3 ∧ tr.cell 3 (3*block+phase) 2=1 ∧
    tr.cell 3 (3*block+phase) 0=Fp.ofNat block ∧
    ∀ i,i<3 → tr.cell 3 (3*block+phase) (3+i)=if i=phase then 1 else 0 := by
  have capacity := sha384_call_capacity f0 f1 pub tr h
  have hr : 3*block+phase<tr.height 3 := by omega
  have active := sha384_call_required_active f0 f1 pub tr h (3*block+phase) hr (by omega)
  have tag := sha384_call_active_tag f0 f1 pub tr h (3*block+phase) hr active
  have div : (3*block+phase)/3=block := by omega
  have mod : (3*block+phase)%3=phase := by omega
  rw [div] at tag
  refine ⟨hr,active,tag,?_⟩
  intro i hi
  simpa only [mod] using sha384_call_active_phase f0 f1 pub tr h (3*block+phase) hr active i hi


/-- Every call resets all32 limbs, including SHA384 hidden state words6/7. -/
theorem sha384_call_initial (f0 f1 : List (Nat × Nat)) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384SharedAir f0 f1) pub tr) (call limb : Nat) (hc : call<2) (hl : limb<32) :
    tr.cell 3 (3*call) (6+limb)=Fp.ofNat (sha384BatchIVPayload[limb]!) := by
  have metadata := sha384_call_segment_metadata f0 f1 pub tr h call 0 hc (by decide)
  simp only [Nat.add_zero] at metadata
  have phase := metadata.2.2.2 0 (by decide)
  simp only [ite_true] at phase
  have eq := sha384_call_constraint f0 f1 pub tr h _ metadata.1
    (.mul (.col 3 false) (sharedSub (.col (6+limb) false) (.const (sha384BatchIVPayload[limb]!))))
    (by simp only [sha384SharedCalls,List.mem_append];exact Or.inl (Or.inl (Or.inr (List.mem_map.mpr ⟨limb,List.mem_range.mpr hl,rfl⟩))))
  change tr.cell 3 (3*call) 3*(tr.cell 3 (3*call) (6+limb)+ -Fp.ofNat (sha384BatchIVPayload[limb]!))=0 at eq
  change tr.cell 3 (3*call) 3=1 at phase
  rw [phase] at eq
  grind

/-- Within a call, all32 output limbs feed the next block; no link crosses reset. -/
theorem sha384_call_state_link (f0 f1 : List (Nat × Nat)) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384SharedAir f0 f1) pub tr) (call block limb : Nat)
    (hc : call<2) (hb : block<2) (hl : limb<32) :
    tr.cell 3 (3*call+(block+1)) (6+limb)=tr.cell 3 (3*call+block) (102+limb) := by
  have metadata := sha384_call_segment_metadata f0 f1 pub tr h call block hc (by omega)
  have next := (sha384_call_segment_metadata f0 f1 pub tr h call (block+1) hc (by omega)).1
  have p0 := metadata.2.2.2 0 (by decide)
  have p1 := metadata.2.2.2 1 (by decide)
  have eq := sha384_call_constraint f0 f1 pub tr h _ metadata.1
    (.mul .isTransition (.mul (.add (.col 3 false) (.col 4 false))
      (sharedSub (.col (6+limb) true) (.col (102+limb) false))))
    (by simp only [sha384SharedCalls,List.mem_append];exact Or.inl (Or.inr (List.mem_map.mpr ⟨limb,List.mem_range.mpr hl,rfl⟩)))
  have next' : 3*call+block+1<tr.height 3 := by omega
  simp only [Expr.eval,Expr.evalWith,rowEnv,sharedSub,Nat.mod_eq_of_lt next',Nat.ne_of_lt next',Bool.false_eq_true,ite_false,ite_true] at eq
  change tr.cell 3 (3*call+block) 3=(if 0=block then 1 else 0) at p0
  change tr.cell 3 (3*call+block) 4=(if 1=block then 1 else 0) at p1
  have sum : tr.cell 3 (3*call+block) 3+tr.cell 3 (3*call+block) 4=1 := by
    rw [p0,p1]
    have cases : block=0 ∨ block=1 := by omega
    rcases cases with rfl | rfl <;> simp <;> grind
  rw [sum] at eq
  have result : tr.cell 3 (3*call+block+1) (6+limb)=tr.cell 3 (3*call+block) (102+limb) := by grind
  simpa only [Nat.add_assoc] using result

/-- Final public bytes are selected by the constrained callID, not a free selector. -/
theorem sha384_call_final_byte (f0 f1 : List (Nat × Nat)) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384SharedAir f0 f1) pub tr) (call byte : Nat) (hc : call<2) (hb : byte<48) :
    tr.cell 3 (3*call+2) (134+byte)=pub.getD (48*call+byte) 0 := by
  have metadata := sha384_call_segment_metadata f0 f1 pub tr h call 2 hc (by decide)
  have phase := metadata.2.2.2 2 (by decide)
  change tr.cell 3 (3*call+2) 5=1 at phase
  have tag := metadata.2.2.1
  have eq := sha384_call_constraint f0 f1 pub tr h _ metadata.1
    (.mul (.col 5 false) (sharedSub (.col (134+byte) false)
      (.add (.mul (sharedSub (.const 1) (.col 0 false)) (.pub byte))
        (.mul (.col 0 false) (.pub (48+byte))))))
    (by simp only [sha384SharedCalls,List.mem_append];exact Or.inr (List.mem_map.mpr ⟨byte,List.mem_range.mpr hb,rfl⟩))
  change tr.cell 3 (3*call+2) 5*(tr.cell 3 (3*call+2) (134+byte)+
    -(((1:Fp)+ -tr.cell 3 (3*call+2) 0)*pub.getD byte 0+tr.cell 3 (3*call+2) 0*pub.getD (48+byte) 0))=0 at eq
  rw [phase,tag] at eq
  have cases : call=0 ∨ call=1 := by omega
  rcases cases with rfl | rfl
  · change (1:Fp)*(tr.cell 3 (3*0+2) (134+byte)+ -((1+ -0)*pub.getD byte 0+0*pub.getD (48+byte) 0))=0 at eq
    simpa only [Nat.mul_zero,Nat.zero_add] using (show tr.cell 3 (3*0+2) (134+byte)=pub.getD byte 0 by grind)
  · change (1:Fp)*(tr.cell 3 (3*1+2) (134+byte)+ -((1+ -1)*pub.getD byte 0+1*pub.getD (48+byte) 0))=0 at eq
    simpa only [Nat.mul_one] using (show tr.cell 3 (3*1+2) (134+byte)=pub.getD (48+byte) 0 by grind)

end NearCompression
