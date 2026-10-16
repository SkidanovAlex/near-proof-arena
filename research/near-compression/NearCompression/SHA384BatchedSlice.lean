import NearCompression.SHA384BatchedPhase

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 NearSpecV3.SHA512
set_option maxRecDepth 65536

def sha384BatchLinkExpr : Expr → Bool
  | .mul .isTransition (.add (.col _ false) (.neg (.col _ true))) => true
  | _ => false

set_option maxHeartbeats 8000000 in
theorem sha384_batch_combined_shapes :
    sha512CombinedConstraints.all (fun e => sha512CurrentExpr e || sha384BatchLinkExpr e)=true := by decide

theorem sha384_batch_link_shape (e : Expr) (he : sha384BatchLinkExpr e=true) :
    ∃ a b,e=instructionSequenceConstraint (a,b) := by
  unfold sha384BatchLinkExpr at he
  split at he
  · rename_i a b
    exact ⟨a,b,rfl⟩
  · contradiction

theorem sha384_batch_gate_current (e : Expr) (he : sha512CurrentExpr e=true) : sha384BatchGate e=e := by
  induction e <;> simp_all [sha512CurrentExpr,sha384BatchGate]

def sha384BatchPairTrace (tr : Trace Fp) (start : Nat) : Trace Fp :=
  ⟨fun _ => 1,fun _ r c => tr.cell 0 (start+r) c⟩

theorem sha384_batch_gated_constraint (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384BatchedAir n) pub tr) (r : Nat) (hr : r<tr.height 0)
    (active : tr.cell 0 r 5232=1) (e : Expr) (he : e∈sha512CombinedConstraints) :
    (sha384BatchGate e).eval tr 0 r pub=0 := by
  have hc := sha384_batch_constraint n pub tr h r hr (.mul sha384BatchActive (sha384BatchGate e))
    (by simp only [sha384BatchCoreConstraints,List.mem_append];exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (List.mem_map.mpr ⟨e,he,rfl⟩))))))
  change tr.cell 0 r 5232*(sha384BatchGate e).eval tr 0 r pub=0 at hc
  rw [active] at hc
  grind

/-- This proof explicitly checks the canonical combined AST has only current
constraints and simple transition links. Thus no first/last selector is lost. -/
theorem sha384_batch_pair_holds (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384BatchedAir n) pub tr) (bound : sha384PaddedLength n/128<P)
    (block phase : Nat) (hb : block<sha384PaddedLength n/128) (hp : phase<79) :
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
      have metadata := sha384_batch_segment_metadata n pub tr h bound block (phase+r) hb (by omega)
      have hc := sha384_batch_gated_constraint n pub tr h _ metadata.1 metadata.2.1 e he
      rw [sha384_batch_gate_current e current,instruction_local_eval e tr 0 _ pub locality] at hc
      rw [instruction_local_eval e _ 0 r pub locality]
      simpa only [sha384BatchPairTrace,rr] using hc
    · obtain ⟨a,b,rfl⟩ := sha384_batch_link_shape e link
      rcases cases with rfl | rfl
      · have metadata := sha384_batch_segment_metadata n pub tr h bound block phase hb (by omega)
        have hc := sha384_batch_gated_constraint n pub tr h _ metadata.1 metadata.2.1 _ he
        have phaseZero := metadata.2.2.2 79 (by decide)
        rw [ite_eq_right (by omega : ¬79=phase)] at phaseZero
        have next : 80*block+phase+1<tr.height 0 := by
          have m := sha384_batch_segment_metadata n pub tr h bound block (phase+1) hb (by omega)
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

theorem sha384_batch_output (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384BatchedAir n) pub tr) (bound : sha384PaddedLength n/128<P)
    (block phase : Nat) (hb : block<sha384PaddedLength n/128) (hp : phase<80) :
    sha512CombinedOutput (tr.cell 0 (80*block+phase))=
      round (sha512CombinedVars (tr.cell 0 (80*block+phase)))
        (sha512CombinedK (tr.cell 0 (80*block+phase)))
        ((sha512CombinedWindow (tr.cell 0 (80*block+phase))).headD 0) := by
  by_cases last : phase=79
  · subst phase
    have pair := sha384_batch_pair_holds n pub tr h bound block 78 hb (by decide)
    have result := sha512_combined_output _ _ pub 0 (by decide) rfl pair 1 (by change 1<2;decide)
    simpa only [sha384BatchPairTrace,Nat.add_assoc,Nat.reduceAdd] using result
  · have pair := sha384_batch_pair_holds n pub tr h bound block phase hb (by omega)
    have result := sha512_combined_output _ _ pub 0 (by decide) rfl pair 0 (by change 0<2;decide)
    simpa only [sha384BatchPairTrace,Nat.add_zero] using result

theorem sha384_batch_recurrence (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384BatchedAir n) pub tr) (bound : sha384PaddedLength n/128<P)
    (block phase : Nat) (hb : block<sha384PaddedLength n/128) (hp : phase<79) :
    sha512CombinedVars (tr.cell 0 (80*block+phase+1))=
      round (sha512CombinedVars (tr.cell 0 (80*block+phase)))
        (sha512CombinedK (tr.cell 0 (80*block+phase)))
        ((sha512CombinedWindow (tr.cell 0 (80*block+phase))).headD 0) ∧
    sha512CombinedWindow (tr.cell 0 (80*block+phase+1))=
      nextWindow (sha512CombinedWindow (tr.cell 0 (80*block+phase))) := by
  have pair := sha384_batch_pair_holds n pub tr h bound block phase hb hp
  have result := sha512_combined_recurrence _ _ pub 0 (by decide) rfl pair 0 (by change 1<2;decide)
  simpa only [sha384BatchPairTrace,Nat.add_zero,Nat.zero_add] using result

theorem sha384_batch_round_holds (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384BatchedAir n) pub tr) (bound : sha384PaddedLength n/128<P)
    (block phase : Nat) (hb : block<sha384PaddedLength n/128) (hp : phase<80) :
    sha512RoundHolds (sha512CombinedRoundRow (tr.cell 0 (80*block+phase))) := by
  by_cases last : phase=79
  · subst phase
    have pair := sha384_batch_pair_holds n pub tr h bound block 78 hb (by decide)
    have rounds := sha512_combined_round_holds _ _ pub 0 (by decide) rfl pair
    have row := sha512_sequence_row_holds _ _ pub 0 (by decide) rfl rounds 1 (by change 1<2;decide)
    change sha512RoundHolds (fun col => tr.cell 0 (80*block+79) (2544+col))
    simpa only [sha384BatchPairTrace,sha512CombinedProjection,Nat.zero_add,Nat.add_assoc,Nat.reduceAdd] using row
  · have pair := sha384_batch_pair_holds n pub tr h bound block phase hb (by omega)
    have rounds := sha512_combined_round_holds _ _ pub 0 (by decide) rfl pair
    have row := sha512_sequence_row_holds _ _ pub 0 (by decide) rfl rounds 0 (by change 0<2;decide)
    change sha512RoundHolds (fun col => tr.cell 0 (80*block+phase) (2544+col))
    simpa only [sha384BatchPairTrace,sha512CombinedProjection,Nat.zero_add,Nat.add_zero] using row


end NearCompression
