import NearCompression.SHA384SharedCore
import NearCompression.SHA384BatchedCompression

/-! Independent-node local arithmetic. The prior phase/slice/round proofs are
specialized to an explicit constraint-only contract, never to the old bus
balance or inter-block state-chain assumptions. The contract is derived below
from actual shared AIR HoldsP. -/
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 NearSpecV3.SHA512
set_option maxRecDepth 65536

structure SHA384CoreLocal (blocks : Nat) (pub : List Fp) (tr : Trace Fp) : Prop where
  positive : 0<blocks
  logBound : 1≤tr.log 0 ∧ tr.log 0≤22
  constr : ∀ r,r<tr.height 0 → ∀ e,e∈sha384BatchCoreConstraints blocks → e.eval tr 0 r pub=0

theorem sha384_local_constraint (blocks : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : SHA384CoreLocal blocks pub tr) (r : Nat) (hr : r<tr.height 0)
    (e : Expr) (he : e∈sha384BatchCoreConstraints (blocks)) :
    e.eval tr 0 r pub=0 := h.constr r hr e he


theorem sha384_local_active_boolean (blocks : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : SHA384CoreLocal blocks pub tr) (r : Nat) (hr : r<tr.height 0) :
    tr.cell 0 r 5232=0 ∨ tr.cell 0 r 5232=1 := by
  have hc := sha384_local_constraint blocks pub tr h r hr (instructionBitConstraint 5232)
    (by simp [sha384BatchCoreConstraints])
  change tr.cell 0 r 5232 * (tr.cell 0 r 5232 + -(1:Fp))=0 at hc
  grind


theorem sha384_local_first (blocks : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : SHA384CoreLocal blocks pub tr) :
    tr.cell 0 0 5232=1 ∧ tr.cell 0 0 5233=0 ∧
    ∀ i,i<80 → tr.cell 0 0 (5152+i)=if i=0 then 1 else 0 := by
  have active := sha384_local_constraint blocks pub tr h 0 (Nat.two_pow_pos _)
    (.mul .isFirst (.add sha384BatchActive (.neg (.const 1)))) (by simp [sha384BatchCoreConstraints])
  have tag := sha384_local_constraint blocks pub tr h 0 (Nat.two_pow_pos _)
    (.mul .isFirst sha384BatchTag) (by simp [sha384BatchCoreConstraints])
  change (1:Fp)*(tr.cell 0 0 5232 + -1)=0 at active
  change (1:Fp)*tr.cell 0 0 5233=0 at tag
  refine ⟨by grind,by grind,?_⟩
  intro i hi
  have phase := sha384_local_constraint blocks pub tr h 0 (Nat.two_pow_pos _)
    (.mul .isFirst (.add (sha384BatchPhase i) (.neg (.const (if i=0 then 1 else 0)))))
    (by simp only [sha384BatchCoreConstraints,List.mem_append]; exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (List.mem_map.mpr ⟨i,List.mem_range.mpr hi,rfl⟩))))))
  by_cases zero : i=0
  · subst i;change (1:Fp)*(tr.cell 0 0 (5152+0)+ -1)=0 at phase;simp only [ite_true];grind
  · change (1:Fp)*(tr.cell 0 0 (5152+i)+ -Fp.ofNat (if i=0 then 1 else 0))=0 at phase
    rw [ite_eq_right zero] at phase ⊢
    change (1:Fp)*(tr.cell 0 0 (5152+i)+ -0)=0 at phase
    grind


theorem sha384_local_no_restart (blocks : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : SHA384CoreLocal blocks pub tr) (r : Nat) (hr : r+1<tr.height 0)
    (active : tr.cell 0 (r+1) 5232=1) : tr.cell 0 r 5232=1 := by
  have hc := sha384_local_constraint blocks pub tr h r (by omega)
    (.mul .isTransition (.mul (.col 5232 true) (.add (.const 1) (.neg sha384BatchActive))))
    (by simp [sha384BatchCoreConstraints])
  simp only [Expr.eval,Expr.evalWith,rowEnv,sha384BatchActive,Nat.mod_eq_of_lt hr,Nat.ne_of_lt hr,ite_false,ite_true] at hc
  rw [active] at hc
  grind


theorem sha384_local_phase_step (blocks : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : SHA384CoreLocal blocks pub tr) (r i : Nat) (hr : r+1<tr.height 0) (hi : i<80) :
    tr.cell 0 (r+1) (5152+i)=tr.cell 0 (r+1) 5232 * tr.cell 0 r (5152+(if i=0 then 79 else i-1)) := by
  have hc := sha384_local_constraint blocks pub tr h r (by omega)
    (.mul .isTransition (.add (.col (5152+i) true) (.neg (.mul (.col 5232 true) (sha384BatchPhase (if i=0 then 79 else i-1))))))
    (by simp only [sha384BatchCoreConstraints,List.mem_append];exact Or.inl (Or.inl (Or.inl (Or.inr (List.mem_map.mpr ⟨i,List.mem_range.mpr hi,rfl⟩)))))
  simp only [Expr.eval,Expr.evalWith,rowEnv,sha384BatchPhase,Nat.mod_eq_of_lt hr,Nat.ne_of_lt hr,ite_false,ite_true] at hc
  grind

/-- Active rows have a canonical modulo80 phase, derived from reset equations. -/

theorem sha384_local_active_phase (blocks : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : SHA384CoreLocal blocks pub tr) (r : Nat) (hr : r<tr.height 0)
    (active : tr.cell 0 r 5232=1) (i : Nat) (hi : i<80) :
    tr.cell 0 r (5152+i)=if i=r%80 then 1 else 0 := by
  induction r generalizing i with
  | zero => simpa using (sha384_local_first blocks pub tr h).2.2 i hi
  | succ r ih =>
    have prev := sha384_local_no_restart blocks pub tr h r hr active
    have idx : (if i=0 then 79 else i-1)<80 := by split <;> omega
    have phase := ih (by omega) prev (if i=0 then 79 else i-1) idx
    have step := sha384_local_phase_step blocks pub tr h r i hr hi
    rw [active,phase] at step
    have eq : (if i=0 then 79 else i-1)=r%80 ↔ i=(r+1)%80 := by
      by_cases zero : i=0 <;> simp only [zero,ite_true,ite_false] <;> omega
    simp only [eq] at step
    grind


theorem sha384_local_active_prefix (blocks : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : SHA384CoreLocal blocks pub tr) (r : Nat) (hr : r<tr.height 0)
    (active : tr.cell 0 r 5232=1) (s : Nat) (hs : s≤r) : tr.cell 0 s 5232=1 := by
  induction r with
  | zero =>
    have eq : s=0 := by omega
    subst s
    exact active
  | succ r ih =>
    by_cases eq : s=r+1
    · subst s;exact active
    · exact ih (by omega) (sha384_local_no_restart blocks pub tr h r hr active) (by omega)


theorem sha384_local_inactive_phase (blocks : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : SHA384CoreLocal blocks pub tr) (r : Nat) (hr : r<tr.height 0)
    (inactive : tr.cell 0 r 5232=0) (i : Nat) (hi : i<80) : tr.cell 0 r (5152+i)=0 := by
  cases r with
  | zero => have first := (sha384_local_first blocks pub tr h).1;rw [inactive] at first;exact False.elim ((by decide : (0:Fp)≠1) first)
  | succ r =>
    have step := sha384_local_phase_step blocks pub tr h r i hr hi
    rw [inactive] at step
    grind


theorem sha384_local_tag_step (blocks : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : SHA384CoreLocal blocks pub tr) (r : Nat) (hr : r+1<tr.height 0)
    (active : tr.cell 0 (r+1) 5232=1) :
    tr.cell 0 (r+1) 5233=tr.cell 0 r 5233+tr.cell 0 r (5152+79) := by
  have hc := sha384_local_constraint blocks pub tr h r (by omega)
    (.mul .isTransition (.mul (.col 5232 true)
     (.add (.col 5233 true) (.neg (.add sha384BatchTag (sha384BatchPhase 79))))))
    (by simp [sha384BatchCoreConstraints])
  simp only [Expr.eval,Expr.evalWith,rowEnv,sha384BatchPhase,sha384BatchTag,Nat.mod_eq_of_lt hr,Nat.ne_of_lt hr,ite_false,ite_true] at hc
  rw [active] at hc
  grind


theorem sha384_local_active_tag (blocks : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : SHA384CoreLocal blocks pub tr) (r : Nat) (hr : r<tr.height 0)
    (active : tr.cell 0 r 5232=1) : tr.cell 0 r 5233=Fp.ofNat (r/80) := by
  induction r with
  | zero => exact (sha384_local_first blocks pub tr h).2.1
  | succ r ih =>
    have prev := sha384_local_no_restart blocks pub tr h r hr active
    have tag := ih (by omega) prev
    have phase := sha384_local_active_phase blocks pub tr h r (by omega) prev 79 (by decide)
    have step := sha384_local_tag_step blocks pub tr h r hr active
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



theorem sha384_local_height_small (blocks : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : SHA384CoreLocal blocks pub tr) : tr.height 0<P := by
  have log := h.logBound
  have upper : tr.log 0≤22 := log.2
  have power := Nat.pow_le_pow_right (by decide : 1≤2) upper
  change 2^tr.log 0<P
  unfold P
  omega

/-- A stopping active row must be precisely the final phase of the final tag. -/

theorem sha384_local_stop_index (blocks : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : SHA384CoreLocal blocks pub tr) (bound : blocks<P)
    (r : Nat) (hr : r<tr.height 0) (active : tr.cell 0 r 5232=1)
    (stop : sha384BatchStop.eval tr 0 r pub=1) : r+1=80*(blocks) := by
  have phase := sha384_local_constraint blocks pub tr h r hr
    (.mul sha384BatchStop (.add (sha384BatchPhase 79) (.neg (.const 1))))
    (by simp [sha384BatchCoreConstraints])
  have tag := sha384_local_constraint blocks pub tr h r hr
    (.mul sha384BatchStop (.add sha384BatchTag (.neg (.const (blocks-1)))))
    (by simp [sha384BatchCoreConstraints])
  change sha384BatchStop.eval tr 0 r pub*(tr.cell 0 r (5152+79)+ -(1:Fp))=0 at phase
  change sha384BatchStop.eval tr 0 r pub*(tr.cell 0 r 5233+ -Fp.ofNat (blocks-1))=0 at tag
  rw [stop,sha384_local_active_phase blocks pub tr h r hr active 79 (by decide)] at phase
  rw [stop,sha384_local_active_tag blocks pub tr h r hr active] at tag
  have last : 79=r%80 := by
    by_cases eq : 79=r%80
    · exact eq
    · simp only [ite_eq_right eq] at phase
      have bad : (0:Fp)=1 := by grind
      exact False.elim ((by decide : (0:Fp)≠1) bad)
  have tags : Fp.ofNat (r/80)=Fp.ofNat (blocks-1) := by grind
  have small := sha384_local_height_small blocks pub tr h
  have same := congrArg Fp.toNat tags
  rw [Fp.toNat_ofNat,Fp.toNat_ofNat,Nat.mod_eq_of_lt (by omega : r/80<P),
    Nat.mod_eq_of_lt (by omega : blocks-1<P)] at same
  have pos : 0<blocks := h.positive
  omega


theorem sha384_local_required_active (blocks : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : SHA384CoreLocal blocks pub tr) (bound : blocks<P)
    (r : Nat) (hr : r<tr.height 0) (required : r<80*(blocks)) :
    tr.cell 0 r 5232=1 := by
  induction r with
  | zero => exact (sha384_local_first blocks pub tr h).1
  | succ r ih =>
    have active := ih (by omega) (by omega)
    rcases sha384_local_active_boolean blocks pub tr h (r+1) hr with inactive | result
    · have stop := sha384_batch_stop_next_inactive blocks pub tr r hr active inactive
      have index := sha384_local_stop_index blocks pub tr h bound r (by omega) active stop
      omega
    · exact result


theorem sha384_local_capacity (blocks : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : SHA384CoreLocal blocks pub tr) (bound : blocks<P) :
    80*(blocks)≤tr.height 0 := by
  by_cases fits : 80*(blocks)≤tr.height 0
  · exact fits
  · have pos : 0<tr.height 0 := Nat.two_pow_pos _
    have active := sha384_local_required_active blocks pub tr h bound (tr.height 0-1) (by omega) (by omega)
    have stop := sha384_batch_stop_last blocks pub tr (tr.height 0-1) (by omega) active
    have index := sha384_local_stop_index blocks pub tr h bound (tr.height 0-1) (by omega) active stop
    omega



theorem sha384_local_active_bounded (blocks : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : SHA384CoreLocal blocks pub tr) (bound : blocks<P)
    (r : Nat) (hr : r<tr.height 0) (active : tr.cell 0 r 5232=1) :
    r<80*(blocks) := by
  have descend (k : Nat) : ∀ r,r<tr.height 0 → tr.height 0-r≤k → tr.cell 0 r 5232=1 → r<80*(blocks) := by
    induction k with
    | zero => intro r hr distance active;omega
    | succ k ih =>
      intro r hr distance active
      by_cases last : r+1=tr.height 0
      · have stop := sha384_batch_stop_last blocks pub tr r last active
        have index := sha384_local_stop_index blocks pub tr h bound r hr active stop
        omega
      · have next : r+1<tr.height 0 := by omega
        rcases sha384_local_active_boolean blocks pub tr h (r+1) next with inactive | nextActive
        · have stop := sha384_batch_stop_next_inactive blocks pub tr r next active inactive
          have index := sha384_local_stop_index blocks pub tr h bound r hr active stop
          omega
        · have result := ih (r+1) next (by omega) nextActive
          omega
  exact descend (tr.height 0-r) r hr (by omega) active

/-- Exact active prefix, with its length derived from stop/tag constraints. -/

theorem sha384_local_active_iff (blocks : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : SHA384CoreLocal blocks pub tr) (bound : blocks<P)
    (r : Nat) (hr : r<tr.height 0) :
    tr.cell 0 r 5232=1 ↔ r<80*(blocks) :=
  ⟨sha384_local_active_bounded blocks pub tr h bound r hr,
   sha384_local_required_active blocks pub tr h bound r hr⟩

/-- Each requested block has exactly its canonical80active rows; this is the
stable interface for extracting local gadgets and within-segment transitions. -/

theorem sha384_local_segment_metadata (blocks : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : SHA384CoreLocal blocks pub tr) (bound : blocks<P)
    (block phase : Nat) (hb : block<blocks) (hp : phase<80) :
    80*block+phase<tr.height 0 ∧ tr.cell 0 (80*block+phase) 5232=1 ∧
    tr.cell 0 (80*block+phase) 5233=Fp.ofNat block ∧
    ∀ i,i<80 → tr.cell 0 (80*block+phase) (5152+i)=if i=phase then 1 else 0 := by
  have capacity := sha384_local_capacity blocks pub tr h bound
  have hr : 80*block+phase<tr.height 0 := by omega
  have active := sha384_local_required_active blocks pub tr h bound (80*block+phase) hr (by omega)
  have tag := sha384_local_active_tag blocks pub tr h (80*block+phase) hr active
  have div : (80*block+phase)/80=block := by omega
  have mod : (80*block+phase)%80=phase := by omega
  rw [div] at tag
  refine ⟨hr,active,tag,?_⟩
  intro i hi
  simpa only [mod] using sha384_local_active_phase blocks pub tr h (80*block+phase) hr active i hi


theorem sha384_local_gated_constraint (blocks : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : SHA384CoreLocal blocks pub tr) (r : Nat) (hr : r<tr.height 0)
    (active : tr.cell 0 r 5232=1) (e : Expr) (he : e∈sha512CombinedConstraints) :
    (sha384BatchGate e).eval tr 0 r pub=0 := by
  have hc := sha384_local_constraint blocks pub tr h r hr (.mul sha384BatchActive (sha384BatchGate e))
    (by simp only [sha384BatchCoreConstraints,List.mem_append];exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (List.mem_map.mpr ⟨e,he,rfl⟩))))))
  change tr.cell 0 r 5232*(sha384BatchGate e).eval tr 0 r pub=0 at hc
  rw [active] at hc
  grind

/-- This proof explicitly checks the canonical combined AST has only current
constraints and simple transition links. Thus no first/last selector is lost. -/

theorem sha384_local_pair_holds (blocks : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : SHA384CoreLocal blocks pub tr) (bound : blocks<P)
    (block phase : Nat) (hb : block<blocks) (hp : phase<79) :
    Holds ⟨[sha512CombinedTable],0,0⟩ pub (sha384BatchPairTrace tr (80*block+phase)) := by
  constructor
  · intro t ht
    have zero : t=0 := by simpa using ht
    subst t
    change 1≤1 ∧ 1≤22
    decide
  · intro t ht r hr e he
    have zero : t=0 := by simpa using ht
    subst t
    change e∈sha512CombinedConstraints at he
    have cases : r=0 ∨ r=1 := by change r<2 at hr;omega
    have shape := List.all_eq_true.mp sha384_batch_combined_shapes e he
    simp only [Bool.or_eq_true] at shape
    rcases shape with current | link
    · have locality := sha512_current_expr_local e current
      have rr : 80*block+phase+r=80*block+(phase+r) := by omega
      have metadata := sha384_local_segment_metadata blocks pub tr h bound block (phase+r) hb (by omega)
      have hc := sha384_local_gated_constraint blocks pub tr h _ metadata.1 metadata.2.1 e he
      rw [sha384_batch_gate_current e current,instruction_local_eval e tr 0 _ pub locality] at hc
      rw [instruction_local_eval e _ 0 r pub locality]
      simpa only [sha384BatchPairTrace,rr] using hc
    · obtain ⟨a,b,rfl⟩ := sha384_batch_link_shape e link
      rcases cases with rfl | rfl
      · have metadata := sha384_local_segment_metadata blocks pub tr h bound block phase hb (by omega)
        have hc := sha384_local_gated_constraint blocks pub tr h _ metadata.1 metadata.2.1 _ he
        have phaseZero := metadata.2.2.2 79 (by decide)
        rw [ite_eq_right (by omega : ¬79=phase)] at phaseZero
        have next : 80*block+phase+1<tr.height 0 := by
          have m := sha384_local_segment_metadata blocks pub tr h bound block (phase+1) hb (by omega)
          omega
        simp only [instructionSequenceConstraint,sha384BatchGate,sha384BatchContinue,sha384BatchPhase,
          Expr.eval,Expr.evalWith,rowEnv,Nat.mod_eq_of_lt next,Nat.ne_of_lt next,
          Bool.false_eq_true,ite_false,ite_true] at hc
        rw [phaseZero] at hc
        simp only [instructionSequenceConstraint,Expr.eval,Expr.evalWith,rowEnv,sha384BatchPairTrace,
          Trace.height,Nat.reducePow,Nat.reduceAdd,Nat.reduceMod,Bool.false_eq_true,ite_false,ite_true,Nat.add_zero]
        grind
      · simp only [instructionSequenceConstraint,Expr.eval,Expr.evalWith,rowEnv,sha384BatchPairTrace,Trace.height]
        grind
  · intro t ht r hr i hi
    have zero : t=0 := by simpa using ht
    subst t
    contradiction
  · intro b msg
    simp [busCount,busCount.go,tableBusCount,sha512CombinedTable]


theorem sha384_local_output (blocks : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : SHA384CoreLocal blocks pub tr) (bound : blocks<P)
    (block phase : Nat) (hb : block<blocks) (hp : phase<80) :
    sha512CombinedOutput (tr.cell 0 (80*block+phase))=
      round (sha512CombinedVars (tr.cell 0 (80*block+phase)))
        (sha512CombinedK (tr.cell 0 (80*block+phase)))
        ((sha512CombinedWindow (tr.cell 0 (80*block+phase))).headD 0) := by
  by_cases last : phase=79
  · subst phase
    have pair := sha384_local_pair_holds blocks pub tr h bound block 78 hb (by decide)
    have result := sha512_combined_output _ _ pub 0 (by decide) rfl pair 1 (by change 1<2;decide)
    simpa only [sha384BatchPairTrace,Nat.add_assoc,Nat.reduceAdd] using result
  · have pair := sha384_local_pair_holds blocks pub tr h bound block phase hb (by omega)
    have result := sha512_combined_output _ _ pub 0 (by decide) rfl pair 0 (by change 0<2;decide)
    simpa only [sha384BatchPairTrace,Nat.add_zero] using result


theorem sha384_local_recurrence (blocks : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : SHA384CoreLocal blocks pub tr) (bound : blocks<P)
    (block phase : Nat) (hb : block<blocks) (hp : phase<79) :
    sha512CombinedVars (tr.cell 0 (80*block+phase+1))=
      round (sha512CombinedVars (tr.cell 0 (80*block+phase)))
        (sha512CombinedK (tr.cell 0 (80*block+phase)))
        ((sha512CombinedWindow (tr.cell 0 (80*block+phase))).headD 0) ∧
    sha512CombinedWindow (tr.cell 0 (80*block+phase+1))=
      nextWindow (sha512CombinedWindow (tr.cell 0 (80*block+phase))) := by
  have pair := sha384_local_pair_holds blocks pub tr h bound block phase hb hp
  have result := sha512_combined_recurrence _ _ pub 0 (by decide) rfl pair 0 (by change 1<2;decide)
  simpa only [sha384BatchPairTrace,Nat.add_zero,Nat.zero_add] using result


theorem sha384_local_round_holds (blocks : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : SHA384CoreLocal blocks pub tr) (bound : blocks<P)
    (block phase : Nat) (hb : block<blocks) (hp : phase<80) :
    sha512RoundHolds (sha512CombinedRoundRow (tr.cell 0 (80*block+phase))) := by
  by_cases last : phase=79
  · subst phase
    have pair := sha384_local_pair_holds blocks pub tr h bound block 78 hb (by decide)
    have rounds := sha512_combined_round_holds _ _ pub 0 (by decide) rfl pair
    have row := sha512_sequence_row_holds _ _ pub 0 (by decide) rfl rounds 1 (by change 1<2;decide)
    change sha512RoundHolds (fun col => tr.cell 0 (80*block+79) (2544+col))
    simpa only [sha384BatchPairTrace,sha512CombinedProjection,Nat.zero_add,Nat.add_assoc,Nat.reduceAdd] using row
  · have pair := sha384_local_pair_holds blocks pub tr h bound block phase hb (by omega)
    have rounds := sha512_combined_round_holds _ _ pub 0 (by decide) rfl pair
    have row := sha512_sequence_row_holds _ _ pub 0 (by decide) rfl rounds 0 (by change 0<2;decide)
    change sha512RoundHolds (fun col => tr.cell 0 (80*block+phase) (2544+col))
    simpa only [sha384BatchPairTrace,sha512CombinedProjection,Nat.zero_add,Nat.add_zero] using row


theorem sha384_local_key_limb (blocks : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : SHA384CoreLocal blocks pub tr) (bound : blocks<P)
    (block phase limb : Nat) (hb : block<blocks) (hp : phase<80) (hl : limb<4) :
    (tr.cell 0 (80*block+phase) (4116+limb)).toNat=sha512ConstantDigit phase limb := by
  have metadata := sha384_local_segment_metadata blocks pub tr h bound block phase hb hp
  have hc := sha384_local_constraint blocks pub tr h _ metadata.1
    (.mul sha384BatchActive (.add (.col (4116+limb) false) (.neg (sha512ConstantSum limb 80))))
    (by simp only [sha384BatchCoreConstraints,List.mem_append];exact Or.inl (Or.inr (List.mem_map.mpr ⟨limb,List.mem_range.mpr hl,rfl⟩)))
  change tr.cell 0 (80*block+phase) 5232*(tr.cell 0 (80*block+phase) (4116+limb)+
    -(sha512ConstantSum limb 80).eval tr 0 (80*block+phase) pub)=0 at hc
  rw [metadata.2.1,sha384_batch_constant_sum tr pub _ phase limb 80 (by decide) metadata.2.2.2,ite_eq_left hp] at hc
  have eq : tr.cell 0 (80*block+phase) (4116+limb)=Fp.ofNat (sha512ConstantDigit phase limb) := by grind
  rw [eq,Fp.toNat_ofNat]
  have small : sha512ConstantDigit phase limb<65536 := Nat.mod_lt _ (by decide)
  apply Nat.mod_eq_of_lt
  unfold P
  omega


theorem sha384_local_key (blocks : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : SHA384CoreLocal blocks pub tr) (bound : blocks<P)
    (block phase : Nat) (hb : block<blocks) (hp : phase<80) :
    sha512CombinedK (tr.cell 0 (80*block+phase))=K.getD phase 0 := by
  have l0 := sha384_local_key_limb blocks pub tr h bound block phase 0 hb hp (by decide)
  have l1 := sha384_local_key_limb blocks pub tr h bound block phase 1 hb hp (by decide)
  have l2 := sha384_local_key_limb blocks pub tr h bound block phase 2 hb hp (by decide)
  have l3 := sha384_local_key_limb blocks pub tr h bound block phase 3 hb hp (by decide)
  change (tr.cell 0 (80*block+phase) (4116+0)).toNat+65536*(tr.cell 0 (80*block+phase) (4116+1)).toNat+
    4294967296*(tr.cell 0 (80*block+phase) (4116+2)).toNat+281474976710656*(tr.cell 0 (80*block+phase) (4116+3)).toNat=_
  rw [l0,l1,l2,l3]
  exact sha512_constants_digits phase (by omega)


theorem sha384_local_round_segment (blocks : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : SHA384CoreLocal blocks pub tr) (bound : blocks<P)
    (block count phase : Nat) (hb : block<blocks) (hp : phase+count<80) :
    rounds (sha512CombinedVars (tr.cell 0 (80*block+phase)))
      ((List.range' phase (count+1)).map (fun i => K.getD i 0))
      (sha512CombinedWindow (tr.cell 0 (80*block+phase)))=
      sha512CombinedOutput (tr.cell 0 (80*block+(phase+count))) := by
  induction count generalizing phase with
  | zero =>
    have out := sha384_local_output blocks pub tr h bound block phase hb (by omega)
    rw [sha384_local_key blocks pub tr h bound block phase hb (by omega)] at out
    simpa only [List.range'_succ,List.range'_zero,List.map_cons,List.map_nil,rounds,Nat.add_zero] using out.symm
  | succ count ih =>
    have link := sha384_local_recurrence blocks pub tr h bound block phase hb (by omega)
    rw [sha384_local_key blocks pub tr h bound block phase hb (by omega)] at link
    rw [List.range'_succ,List.map_cons,rounds]
    rw [←link.1,←link.2]
    have result := ih (phase+1) (by omega)
    simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using result

/-- All eighty actual SHA512 rounds follow from batched AIR constraints. -/

theorem sha384_local_rounds (blocks : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : SHA384CoreLocal blocks pub tr) (bound : blocks<P)
    (block : Nat) (hb : block<blocks) :
    rounds (sha512CombinedVars (tr.cell 0 (80*block))) K
      (sha512CombinedWindow (tr.cell 0 (80*block)))=
      sha512CombinedOutput (tr.cell 0 (80*block+79)) := by
  have result := sha384_local_round_segment blocks pub tr h bound block 79 0 hb (by decide)
  have keys : (List.range' 0 80).map (fun i => K.getD i 0)=K := by decide
  simpa only [Nat.zero_add,Nat.add_zero,keys] using result


theorem sha384_local_compression (blocks : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : SHA384CoreLocal blocks pub tr) (bound : blocks<P)
    (block : Nat) (hb : block<blocks) :
    sha384BatchCompression tr block=(List.range 8).map (fun i =>
      add64 (sha512FeedForwardVarsWord (sha512CombinedVars (tr.cell 0 (80*block))) i)
        (sha512FeedForwardVarsWord (sha512CombinedOutput (tr.cell 0 (80*block+79))) i)) := by
  unfold sha384BatchCompression sha512DecodedState
  rw [sha512_compress_vars,sha512_decoded_block_words]
  have result := sha384_local_rounds blocks pub tr h bound block hb
  dsimp only [sha512CombinedWindow] at result
  rw [result]


/-- No old-chain or old-bus premise is required for the independent-node core. -/
theorem sha384_shared_core_local (f0 f1 : List (Nat × Nat)) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384SharedAir f0 f1) pub tr) : SHA384CoreLocal 5 pub tr := by
  constructor
  · decide
  · have log := h.logBound 0 (by simp [sha384SharedAir])
    change 1≤tr.log 0 ∧ tr.log 0≤9 at log
    omega
  · exact sha384_shared_constraint f0 f1 pub tr h

theorem sha384_shared_compression (f0 f1 : List (Nat × Nat)) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384SharedAir f0 f1) pub tr) (node : Nat) (hn : node<5) :
    sha384BatchCompression tr node=(List.range 8).map (fun i =>
      add64 (sha512FeedForwardVarsWord (sha512CombinedVars (tr.cell 0 (80*node))) i)
        (sha512FeedForwardVarsWord (sha512CombinedOutput (tr.cell 0 (80*node+79))) i)) :=
  sha384_local_compression 5 pub tr (sha384_shared_core_local f0 f1 pub tr h) (by decide) node hn

end NearCompression
