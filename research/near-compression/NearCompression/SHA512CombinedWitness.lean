import NearCompression.SHA512ScheduleWindowWitness
import NearCompression.SHA512RoundInvariant
import NearCompression.SHA512Combined

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.View ZkFormal.Sha.Sound NearSpecV3.SHA512

def sha512CombinedWitnessRow (v : Vars) (window : List Nat) (key col : Nat) : Fp :=
  if col<2544 then sha512ScheduleWindowWitness window col else
    sha512RoundWitness v key (window.getD 0 0) (col-2544)

def sha512CombinedWitnessTrace (initial : Vars) (window : List Nat) (keys : Nat → Nat)
    (logSize : Nat) : Trace Fp :=
  ⟨fun _ => logSize,fun _ r col => sha512CombinedWitnessRow
    (sha512CombinedStateRun initial window keys r) (sha512ScheduleWindowRun window r) (keys r) col⟩

def sha512CombinedWitnessAir : Air := ⟨[sha512CombinedTable],0,0⟩

/-- The state-link columns belong to constrained Boolean word encodings. -/
theorem sha512_round_state_boolean (row : Nat → Fp) (h : sha512RoundHolds row)
    (base : Nat) (member : base ∈ [0,64,128,576,640,704,1168,2416,2336,2544])
    (bit : Nat) (hb : bit<64) : (row (base+bit)).toNat≤1 := by
  have input (i col : Nat) (hi : i<2) (hc : col<192) :=
    sha512_bits_input_boolean _ (sha512_round_bits_holds row h i hi) col hc
  have add (i base : Nat) (hi : i<7) (hc : base+4≤12) :=
    sha512_add_word_bit _ (sha512_round_add_holds row h i hi) base bit hc hb
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with eq | eq | eq | eq | eq | eq | eq | eq | eq | eq <;> subst base
  · exact input 0 bit (by decide) (by omega)
  · simpa only [sha512RoundBitsRow,Nat.mul_zero,Nat.zero_add] using input 0 (64+bit) (by decide) (by omega)
  · simpa only [sha512RoundBitsRow,Nat.mul_zero,Nat.zero_add] using input 0 (128+bit) (by decide) (by omega)
  · exact input 1 bit (by decide) (by omega)
  · have bound := input 1 (64+bit) (by decide) (by omega)
    simpa only [sha512RoundBitsRow,←Nat.add_assoc,Nat.reduceMul,Nat.reduceAdd] using bound
  · have bound := input 1 (128+bit) (by decide) (by omega)
    simpa only [sha512RoundBitsRow,←Nat.add_assoc,Nat.reduceMul,Nat.reduceAdd] using bound
  · have bound := add 0 0 (by decide) (by decide)
    simpa only [sha512RoundAddRow,sha512RoundAddBase,←Nat.add_assoc,Nat.reduceMul,Nat.reduceAdd] using bound
  · have bound := add 6 0 (by decide) (by decide)
    simpa only [sha512RoundAddRow,sha512RoundAddBase,←Nat.add_assoc,Nat.reduceMul,Nat.reduceAdd] using bound
  · have bound := add 5 8 (by decide) (by decide)
    simpa only [sha512RoundAddRow,sha512RoundAddBase,←Nat.add_assoc,Nat.reduceMul,Nat.reduceAdd] using bound
  · have bound := add 6 8 (by decide) (by decide)
    simpa only [sha512RoundAddRow,sha512RoundAddBase,←Nat.add_assoc,Nat.reduceMul,Nat.reduceAdd] using bound

theorem sha512_round_link_bits (row nextRow : Nat → Fp) (h : sha512RoundHolds row)
    (nextH : sha512RoundHolds nextRow) (states : sha512RoundVars nextRow=sha512RoundOutput row)
    (post pre bit : Nat) (member : (post,pre) ∈ sha512RoundSequenceWordPairs) (hb : bit<64) :
    row (post+bit)=nextRow (pre+bit) := by
  have a := congrArg Vars.a states; have b := congrArg Vars.b states
  have c := congrArg Vars.c states; have d := congrArg Vars.d states
  have e := congrArg Vars.e states; have f := congrArg Vars.f states
  have g := congrArg Vars.g states; have hh := congrArg Vars.h states
  simp only [sha512RoundVars,sha512RoundOutput] at a b c d e f g hh
  rw [sha512_round_add_bits row h 5 8 (by decide) (by decide)] at a
  rw [sha512_round_add_bits row h 6 8 (by decide) (by decide)] at e
  rw [sha512_round_add_bits nextRow nextH 6 0 (by decide) (by decide)] at d
  rw [sha512_round_add_bits nextRow nextH 0 0 (by decide) (by decide)] at hh
  simp only [sha512BitsWord,sha512RoundBitsRow,sha512RoundAddBase,←Nat.add_assoc,
    Nat.reduceMul,Nat.reduceAdd,Nat.zero_add] at a b c d e f g hh
  have link (p q : Nat) (hp : p ∈ [0,64,128,576,640,704,1168,2416,2336,2544])
      (hq : q ∈ [0,64,128,576,640,704,1168,2416,2336,2544])
      (eq : sha512BitsWord nextRow q=sha512BitsWord row p) : row (p+bit)=nextRow (q+bit) := by
    rw [sha512_word_bit_decode row p _ (sha512_round_state_boolean row h p hp) rfl bit hb,
      sha512_word_bit_decode nextRow q _ (sha512_round_state_boolean nextRow nextH q hq) rfl bit hb,eq]
  simp only [sha512RoundSequenceWordPairs,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with eq | eq | eq | eq | eq | eq | eq | eq <;> cases eq
  · exact link 2336 0 (by decide) (by decide) a
  · exact link 0 64 (by decide) (by decide) b
  · exact link 64 128 (by decide) (by decide) c
  · exact link 128 2416 (by decide) (by decide) d
  · exact link 2544 576 (by decide) (by decide) e
  · exact link 576 640 (by decide) (by decide) f
  · exact link 640 704 (by decide) (by decide) g
  · exact link 704 1168 (by decide) (by decide) hh

theorem sha512_combined_witness_schedule_prefix (v : Vars) (window : List Nat) (key col : Nat)
    (hc : col<2544) :
    sha512CombinedWitnessRow v window key col=sha512ScheduleWindowWitness window col := by
  simp only [sha512CombinedWitnessRow,if_pos hc]

theorem sha512_combined_witness_round_prefix (v : Vars) (window : List Nat) (key col : Nat) :
    sha512CombinedWitnessRow v window key (2544+col)=sha512RoundWitness v key (window.getD 0 0) col := by
  simp only [sha512CombinedWitnessRow,if_neg (by omega : ¬2544+col<2544),Nat.add_sub_cancel_left]

/-- The constructor encodes exactly the requested state, window, and key. -/
theorem sha512_combined_witness_inputs (v : Vars) (window : List Nat) (key : Nat)
    (valid : sha512WindowValid window)
    (bounds : sha512RoundInputBounds v key (window.getD 0 0)) :
    sha512CombinedVars (sha512CombinedWitnessRow v window key)=v ∧
    sha512CombinedWindow (sha512CombinedWitnessRow v window key)=window ∧
    sha512CombinedK (sha512CombinedWitnessRow v window key)=key := by
  have roundEq : sha512CombinedRoundRow (sha512CombinedWitnessRow v window key)=
      sha512RoundWitness v key (window.getD 0 0) := by
    funext col
    exact sha512_combined_witness_round_prefix v window key col
  have inputs := sha512_round_witness_inputs v key (window.getD 0 0) bounds
  refine ⟨?_,?_,?_⟩
  · simpa only [sha512CombinedVars,roundEq] using inputs.1
  · change sha512ScheduleWindow (sha512CombinedWitnessRow v window key)=window
    apply Eq.trans (b := sha512ScheduleWindow (sha512ScheduleWindowWitness window)) _ (sha512_window_witness_decode window valid)
    apply List.map_congr_left
    intro i hi
    apply ofBits_congr
    intro bit hb
    rw [sha512_combined_witness_schedule_prefix v window key (sha512ScheduleWindowBase i+bit) (by
      have bound : sha512ScheduleWindowBase i≤2480 := by
        unfold sha512ScheduleWindowBase
        split <;> omega
      omega)]
  · simpa only [sha512CombinedK,roundEq] using inputs.2.1

/-- Evaluation transport preserves selectors and next-row access for a shared
height, not merely current-row arithmetic. -/
theorem sha512_trace_prefix_eval (e : Expr) (tr other : Trace Fp) (t r : Nat) (pub : List Fp)
    (width : Nat) (bound : e.colBound≤width) (height : tr.height t=other.height t)
    (cells : ∀ r col,col<width → tr.cell t r col=other.cell t r col) :
    e.eval tr t r pub=e.eval other t r pub := by
  induction e with
  | const n => rfl
  | pub i => rfl
  | isFirst => rfl
  | isLast => simp only [Expr.eval,Expr.evalWith,rowEnv,height]
  | isTransition => simp only [Expr.eval,Expr.evalWith,rowEnv,height]
  | col col next =>
    simp only [Expr.eval,Expr.evalWith,rowEnv,height]
    exact cells _ col (by change col+1≤width at bound; omega)
  | add a b ia ib | mul a b ia ib =>
    have ha : a.colBound≤width := Nat.le_trans (Nat.le_max_left ..) bound
    have hb : b.colBound≤width := Nat.le_trans (Nat.le_max_right ..) bound
    first
    | change a.eval tr t r pub+b.eval tr t r pub=a.eval other t r pub+b.eval other t r pub
    | change a.eval tr t r pub*b.eval tr t r pub=a.eval other t r pub*b.eval other t r pub
    rw [ia ha,ib hb]
  | neg a ia =>
    change -a.eval tr t r pub= -a.eval other t r pub
    rw [ia bound]

def sha512CombinedRoundWitnessTrace (initial : Vars) (window : List Nat) (keys : Nat → Nat)
    (logSize : Nat) : Trace Fp :=
  ⟨fun _ => logSize,fun _ r col => sha512RoundWitness (sha512CombinedStateRun initial window keys r)
    (keys r) ((sha512ScheduleWindowRun window r).getD 0 0) col⟩

theorem sha512_combined_round_witness_holds (initial : Vars) (initialValid : sha512VarsValid initial)
    (window : List Nat) (windowValid : sha512WindowValid window) (keys : Nat → Nat)
    (keysBound : ∀ r,keys r<2^64) (logSize : Nat) (height : 1≤logSize ∧ logSize≤22) :
    Holds ⟨[sha512RoundSequenceTable],0,0⟩ [] (sha512CombinedRoundWitnessTrace initial window keys logSize) := by
  have bounds (r : Nat) := sha512_combined_run_input_bounds initial initialValid window windowValid keys keysBound r
  have rowH (r : Nat) := sha512_round_witness_holds _ _ _ (bounds r)
  have nextState (r : Nat) :
      sha512RoundVars ((sha512CombinedRoundWitnessTrace initial window keys logSize).cell 0 (r+1))=
      sha512RoundOutput ((sha512CombinedRoundWitnessTrace initial window keys logSize).cell 0 r) := by
    simp only [sha512CombinedRoundWitnessTrace]
    rw [(sha512_round_witness_inputs _ _ _ (bounds (r+1))).1]
    rw [←sha512_round_full_output _ (rowH r)]
    have input := sha512_round_witness_inputs _ _ _ (bounds r)
    rw [input.1,input.2.1,input.2.2]
    rfl
  constructor
  · intro t ht
    have eq : t=0 := by simpa using ht
    subst t
    exact height
  · intro t ht r hr e he
    have eq : t=0 := by simpa using ht
    subst t
    rcases List.mem_append.mp he with he | he
    · rw [instruction_local_eval e _ 0 r [] (sha512_round_constraints_local e he)]
      exact rowH r e he
    · obtain ⟨pair,hp,rfl⟩ := List.mem_map.mp he
      obtain ⟨wordPair,hw,hp⟩ := List.mem_flatMap.mp hp
      obtain ⟨bit,hb,rfl⟩ := List.mem_map.mp hp
      apply instruction_sequence_eval_complete _ [] 0 r _ _ hr
      intro next
      exact sha512_round_link_bits _ _ (rowH r) (rowH (r+1)) (nextState r)
        wordPair.1 wordPair.2 bit hw (List.mem_range.mp hb)
  · intro t ht r hr i hi
    have eq : t=0 := by simpa using ht
    subst t
    simp [sha512RoundSequenceTable,instructionSequenceTable,sha512RoundTable] at hi
  · intro b m
    simp [busCount,busCount.go,tableBusCount,sha512RoundSequenceTable,instructionSequenceTable,sha512RoundTable]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
theorem sha512_combined_witness_component_bounds :
    sha512ScheduleWindowSequenceTable.constraints.all (fun e => decide (e.colBound≤2544))=true ∧
    sha512RoundSequenceTable.constraints.all (fun e => decide (e.colBound≤2608))=true := by decide

theorem sha512_round_witness_message_bit (v : Vars) (key word : Nat)
    (bounds : sha512RoundInputBounds v key word) (bit : Nat) (hb : bit<64) :
    sha512RoundWitness v key word (1856+bit)=Fp.ofNat (bt word bit) := by
  have rowH := sha512_round_witness_holds v key word bounds
  have input := (sha512_round_witness_inputs v key word bounds).2.2
  have bits := sha512_round_add_bits _ rowH 3 4 (by decide) (by decide)
  have eq : sha512BitsWord (sha512RoundWitness v key word) 1856=word := bits.symm.trans input
  apply sha512_word_bit_decode _ _ _ _ eq bit hb
  intro b hb
  have bound := sha512_add_word_bit _ (sha512_round_add_holds _ rowH 3 (by decide)) 4 b (by decide) hb
  simpa only [sha512RoundAddRow,sha512RoundAddBase,←Nat.add_assoc,Nat.reduceMul,Nat.reduceAdd] using bound

/-- The schedule head and the round message input agree at every individual bit. -/
theorem sha512_combined_witness_message_bit (v : Vars) (window : List Nat) (key : Nat)
    (valid : sha512WindowValid window) (bounds : sha512RoundInputBounds v key (window.getD 0 0))
    (bit : Nat) (hb : bit<64) :
    sha512CombinedWitnessRow v window key (1440+bit)=sha512CombinedWitnessRow v window key (4400+bit) := by
  rw [show 4400+bit=2544+(1856+bit) by omega,sha512_combined_witness_round_prefix,
    sha512_combined_witness_schedule_prefix v window key _ (by omega)]
  exact (sha512_window_witness_bit window valid 0 bit (by decide) hb).trans
    (sha512_round_witness_message_bit v key _ bounds bit hb).symm

/-- Universal construction of the actual combined trace, including all
schedule transitions, all round-state transitions, and message-consumption wires. -/
theorem sha512_combined_witness_trace_holds (initial : Vars) (initialValid : sha512VarsValid initial)
    (window : List Nat) (windowValid : sha512WindowValid window) (keys : Nat → Nat)
    (keysBound : ∀ r,keys r<2^64) (logSize : Nat) (height : 1≤logSize ∧ logSize≤22) :
    Holds sha512CombinedWitnessAir [] (sha512CombinedWitnessTrace initial window keys logSize) := by
  have schedule := sha512_window_witness_trace_holds window windowValid logSize height
  have rounds := sha512_combined_round_witness_holds initial initialValid window windowValid keys keysBound logSize height
  constructor
  · intro t ht
    have eq : t=0 := by simpa [sha512CombinedWitnessAir] using ht
    subst t
    exact height
  · intro t ht r hr e he
    have eq : t=0 := by simpa [sha512CombinedWitnessAir] using ht
    subst t
    rcases List.mem_append.mp he with he | he
    · rcases List.mem_append.mp he with he | he
      · have bound := of_decide_eq_true (List.all_eq_true.mp sha512_combined_witness_component_bounds.1 e he)
        rw [sha512_trace_prefix_eval e (sha512CombinedWitnessTrace initial window keys logSize) (sha512ScheduleWindowWitnessTrace window logSize) 0 r [] 2544 bound rfl
          (fun r col hc => sha512_combined_witness_schedule_prefix _ _ _ col hc)]
        exact schedule.constr 0 (by decide) r hr e he
      · obtain ⟨inner,hi,rfl⟩ := List.mem_map.mp he
        rw [sha512_combined_relocate_eval]
        have bound := of_decide_eq_true (List.all_eq_true.mp sha512_combined_witness_component_bounds.2 inner hi)
        rw [sha512_trace_prefix_eval inner (sha512CombinedProjection (sha512CombinedWitnessTrace initial window keys logSize) 0 2544) (sha512CombinedRoundWitnessTrace initial window keys logSize) 0 r [] 2608 bound rfl
          (fun r col hc => sha512_combined_witness_round_prefix _ _ _ col)]
        exact rounds.constr 0 (by decide) r hr inner hi
    · obtain ⟨bit,hb,rfl⟩ := List.mem_map.mp he
      have eq := sha512_combined_witness_message_bit _ _ _
        (sha512_window_run_valid window windowValid r)
        (sha512_combined_run_input_bounds initial initialValid window windowValid keys keysBound r)
        bit (List.mem_range.mp hb)
      change sha512CombinedWitnessRow _ _ _ (1440+bit) + -sha512CombinedWitnessRow _ _ _ (4400+bit)=0
      simp only [Bool.false_eq_true,ite_false]
      rw [eq]
      grind
  · intro t ht r hr i hi
    have eq : t=0 := by simpa [sha512CombinedWitnessAir] using ht
    subst t
    simp [sha512CombinedWitnessAir,sha512CombinedTable] at hi
  · intro b m
    simp [busCount,busCount.go,tableBusCount,sha512CombinedWitnessAir,sha512CombinedTable]

/-- The actual SHA-512 initial state and constants instantiate the same construction. -/
theorem sha512_combined_standard_witness_holds (window : List Nat) (valid : sha512WindowValid window)
    (logSize : Nat) (height : 1≤logSize ∧ logSize≤22) :
    Holds sha512CombinedWitnessAir []
      (sha512CombinedWitnessTrace (ofList H0) window (fun r => K.getD r 0) logSize) :=
  sha512_combined_witness_trace_holds (ofList H0) sha512_initial_state_valid window valid
    (fun r => K.getD r 0) sha512_standard_keys_bound logSize height

end NearCompression
