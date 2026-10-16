import NearCompression.SHA512WindowInvariant
import NearCompression.SHA512WindowBounds

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.View ZkFormal.Sha.Sound NearSpecV3.SHA512

def sha512WindowExtraIndex (slot : Nat) : Nat :=
  if slot<7 then slot+2 else if slot<11 then slot+3 else 15

def sha512ScheduleWindowWitnessCore (window : List Nat) : Nat → Fp :=
  sha512ScheduleWitness (window.getD 0 0) (window.getD 1 0) (window.getD 9 0) (window.getD 14 0)

def sha512ScheduleWindowWitness (window : List Nat) (col : Nat) : Fp :=
  if col<1776 then sha512ScheduleWindowWitnessCore window col else
    Fp.ofNat (bt (window.getD (sha512WindowExtraIndex ((col-1776)/64)) 0) ((col-1776)%64))

def sha512ScheduleWindowHolds (row : Nat → Fp) : Prop :=
  ∀ e ∈ sha512ScheduleWindowConstraints,e.evalWith (instructionAddEnv row)=0

def sha512ScheduleWindowWitnessTrace (initial : List Nat) (logSize : Nat) : Trace Fp :=
  ⟨fun _ => logSize,fun _ r col => sha512ScheduleWindowWitness (sha512ScheduleWindowRun initial r) col⟩

def sha512ScheduleWindowSequenceAir : Air := ⟨[sha512ScheduleWindowSequenceTable],0,0⟩

theorem sha512_window_witness_prefix (window : List Nat) (col : Nat) (hc : col<1776) :
    sha512ScheduleWindowWitness window col=sha512ScheduleWindowWitnessCore window col := by
  simp only [sha512ScheduleWindowWitness,if_pos hc]

theorem sha512_window_witness_extra (window : List Nat) (slot bit : Nat) (hb : bit<64) :
    sha512ScheduleWindowWitness window (1776+64*slot+bit)=
      Fp.ofNat (bt (window.getD (sha512WindowExtraIndex slot) 0) bit) := by
  have hn : ¬1776+64*slot+bit<1776 := by omega
  have hd : (1776+64*slot+bit-1776)/64=slot := by omega
  have hm : (1776+64*slot+bit-1776)%64=bit := by omega
  simp only [sha512ScheduleWindowWitness,if_neg hn,hd,hm]

theorem sha512_window_witness_core_bounds (window : List Nat) (valid : sha512WindowValid window) :
    sha512ScheduleInputBounds (window.getD 0 0) (window.getD 1 0) (window.getD 9 0) (window.getD 14 0) :=
  ⟨sha512_window_getD_bound window valid 0,sha512_window_getD_bound window valid 1,
    sha512_window_getD_bound window valid 9,sha512_window_getD_bound window valid 14⟩

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
theorem sha512_window_core_column_bound :
    sha512ScheduleConstraints.all (fun e => decide (e.colBound≤1776))=true := by decide

theorem sha512_window_witness_core_holds (window : List Nat) (valid : sha512WindowValid window) :
    sha512ScheduleHolds (sha512ScheduleWindowWitness window) := by
  intro e he
  have bound := of_decide_eq_true (List.all_eq_true.mp sha512_window_core_column_bound e he)
  rw [instruction_control_prefix_eval e _ (sha512ScheduleWindowWitnessCore window) 1776 bound
    (fun col hc => sha512_window_witness_prefix window col hc)]
  exact sha512_schedule_witness_holds _ _ _ _ (sha512_window_witness_core_bounds window valid) e he

theorem sha512_window_witness_extra_boolean (window : List Nat) (col : Nat) (hc : 1776≤col) :
    (sha512ScheduleWindowWitness window col).toNat≤1 := by
  rw [sha512ScheduleWindowWitness,if_neg (by omega),Fp.toNat_ofNat]
  have bit := bt_le (window.getD (sha512WindowExtraIndex ((col-1776)/64)) 0) ((col-1776)%64)
  have bound : bt (window.getD (sha512WindowExtraIndex ((col-1776)/64)) 0) ((col-1776)%64)<P := by
    unfold P; omega
  rw [Nat.mod_eq_of_lt bound]
  exact bit

/-- Universal satisfaction of all core and 768 added Boolean constraints. -/
theorem sha512_window_witness_holds (window : List Nat) (valid : sha512WindowValid window) :
    sha512ScheduleWindowHolds (sha512ScheduleWindowWitness window) := by
  intro e he
  rcases List.mem_append.mp he with he | he
  · exact sha512_window_witness_core_holds window valid e he
  · obtain ⟨bit,hb,rfl⟩ := List.mem_map.mp he
    have bound := sha512_window_witness_extra_boolean window (1776+bit) (by omega)
    change sha512ScheduleWindowWitness window (1776+bit) *
      (sha512ScheduleWindowWitness window (1776+bit) + -(1 : Fp))=0
    have cases : (sha512ScheduleWindowWitness window (1776+bit)).toNat=0 ∨
        (sha512ScheduleWindowWitness window (1776+bit)).toNat=1 := by omega
    rcases cases with h | h
    · have eq : sha512ScheduleWindowWitness window (1776+bit)=(0 : Fp) := Fp.ext h
      rw [eq]; grind
    · have eq : sha512ScheduleWindowWitness window (1776+bit)=(1 : Fp) := Fp.ext h
      rw [eq]; grind

theorem sha512_window_witness_core_bits (window : List Nat) (base : Nat) (hb : base+64≤1776) :
    sha512BitsWord (sha512ScheduleWindowWitness window) base=
      sha512BitsWord (sha512ScheduleWindowWitnessCore window) base := by
  apply ofBits_congr
  intro bit hbit
  rw [sha512_window_witness_prefix window _ (by omega)]

theorem sha512_window_witness_core_word (window : List Nat) (base : Nat) (hb : base+4≤1776) :
    instructionAdd64Word (sha512ScheduleWindowWitness window) base=
      instructionAdd64Word (sha512ScheduleWindowWitnessCore window) base := by
  unfold instructionAdd64Word
  rw [sha512_window_witness_prefix window base (by omega),
    sha512_window_witness_prefix window (base+1) (by omega),
    sha512_window_witness_prefix window (base+2) (by omega),
    sha512_window_witness_prefix window (base+3) (by omega)]

theorem sha512_window_witness_core_inputs (window : List Nat) (valid : sha512WindowValid window) :
    sha512ScheduleW0 (sha512ScheduleWindowWitness window)=window.getD 0 0 ∧
    sha512ScheduleW1 (sha512ScheduleWindowWitness window)=window.getD 1 0 ∧
    sha512ScheduleW9 (sha512ScheduleWindowWitness window)=window.getD 9 0 ∧
    sha512ScheduleW14 (sha512ScheduleWindowWitness window)=window.getD 14 0 := by
  have input := sha512_schedule_witness_inputs _ _ _ _ (sha512_window_witness_core_bounds window valid)
  have a0 := sha512_window_witness_core_word window 1156 (by decide)
  have a1 := sha512_window_witness_core_word window 1364 (by decide)
  have b0 := sha512_window_witness_core_bits window 0 (by decide)
  have b1 := sha512_window_witness_core_bits window 576 (by decide)
  simp only [sha512ScheduleW0,sha512ScheduleW1,sha512ScheduleW9,sha512ScheduleW14,
    instructionAdd64Word,sha512BitsWord,sha512RoundAddRow,sha512RoundAddBase,
    sha512RoundBitsRow,sha512ScheduleWindowWitnessCore,Nat.reduceMul,Nat.reduceAdd,Nat.zero_add,Nat.add_assoc]
    at input a0 a1 b0 b1 ⊢
  rw [a0,a1,b0,b1]
  exact input

theorem sha512_window_extra_layout (slot : Nat) (hs : slot<12) :
    sha512ScheduleWindowBase (sha512WindowExtraIndex slot)=1776+64*slot := by
  have checked : ∀ slot : Fin 12,sha512ScheduleWindowBase (sha512WindowExtraIndex slot.val)=1776+64*slot.val := by decide
  exact checked ⟨slot,hs⟩

theorem sha512_window_extra_coverage (i : Nat) (hi : i<16)
    (h0 : i≠0) (h1 : i≠1) (h9 : i≠9) (h14 : i≠14) :
    ∃ slot,slot<12 ∧ sha512WindowExtraIndex slot=i := by
  have checked : ∀ i : Fin 16,i.val≠0 → i.val≠1 → i.val≠9 → i.val≠14 →
      ∃ slot : Fin 12,sha512WindowExtraIndex slot.val=i.val := by decide
  obtain ⟨slot,eq⟩ := checked ⟨i,hi⟩ h0 h1 h9 h14
  exact ⟨slot.val,slot.isLt,eq⟩

theorem sha512_window_witness_extra_word (window : List Nat) (valid : sha512WindowValid window)
    (slot : Nat) (hs : slot<12) :
    sha512ScheduleWindowWord (sha512ScheduleWindowWitness window) (sha512WindowExtraIndex slot)=
      window.getD (sha512WindowExtraIndex slot) 0 := by
  unfold sha512ScheduleWindowWord
  rw [sha512_window_extra_layout slot hs]
  have eq : sha512BitsWord (sha512ScheduleWindowWitness window) (1776+64*slot)=
      ofBits (bt (window.getD (sha512WindowExtraIndex slot) 0)) 64 := by
    apply ofBits_congr
    intro bit hb
    rw [sha512_window_witness_extra window slot bit hb,Fp.toNat_ofNat]
    apply Nat.mod_eq_of_lt
    have bound := bt_le (window.getD (sha512WindowExtraIndex slot) 0) bit
    unfold P
    omega
  rw [eq,ofBits_bt,Nat.mod_eq_of_lt (sha512_window_getD_bound window valid _)]

theorem sha512_window_witness_word (window : List Nat) (valid : sha512WindowValid window)
    (i : Nat) (hi : i<16) :
    sha512ScheduleWindowWord (sha512ScheduleWindowWitness window) i=window.getD i 0 := by
  have core := sha512_window_core_words _ (sha512_window_witness_core_holds window valid)
  have inputs := sha512_window_witness_core_inputs window valid
  by_cases h0 : i=0
  · subst i; exact core.1.trans inputs.1
  by_cases h1 : i=1
  · subst i; exact core.2.1.trans inputs.2.1
  by_cases h9 : i=9
  · subst i; exact core.2.2.1.trans inputs.2.2.1
  by_cases h14 : i=14
  · subst i; exact core.2.2.2.1.trans inputs.2.2.2
  obtain ⟨slot,hs,eq⟩ := sha512_window_extra_coverage i hi h0 h1 h9 h14
  rw [←eq]
  exact sha512_window_witness_extra_word window valid slot hs

theorem sha512_window_witness_decode (window : List Nat) (valid : sha512WindowValid window) :
    sha512ScheduleWindow (sha512ScheduleWindowWitness window)=window := by
  apply List.ext_getElem
  · simpa only [sha512ScheduleWindow,List.length_map,List.length_range] using valid.1.symm
  · intro i hi hi'
    simp only [sha512ScheduleWindow,List.getElem_map,List.getElem_range]
    rw [sha512_window_witness_word window valid i (by simpa [sha512ScheduleWindow] using hi)]
    exact (List.getElem_eq_getD (h := hi') 0).symm

theorem sha512_window_witness_boolean (window : List Nat) (valid : sha512WindowValid window)
    (i bit : Nat) (hi : i<16) (hb : bit<64) :
    (sha512ScheduleWindowWitness window (sha512ScheduleWindowBase i+bit)).toNat≤1 := by
  have core := sha512_window_witness_core_holds window valid
  by_cases h0 : i=0
  · subst i
    have bound := sha512_add_word_bit _ (sha512_schedule_add_holds _ core 1 (by decide)) 4 bit (by decide) hb
    simpa only [sha512ScheduleWindowBase,sha512RoundAddRow,sha512RoundAddBase,
      ←Nat.add_assoc,Nat.reduceMul,Nat.reduceAdd] using bound
  by_cases h1 : i=1
  · subst i
    exact sha512_bits_input_boolean _ (sha512_schedule_bits_holds _ core 1 (by decide)) bit (by omega)
  by_cases h9 : i=9
  · subst i
    have bound := sha512_add_word_bit _ (sha512_schedule_add_holds _ core 0 (by decide)) 4 bit (by decide) hb
    simpa only [sha512ScheduleWindowBase,sha512RoundAddRow,sha512RoundAddBase,
      ←Nat.add_assoc,Nat.reduceMul,Nat.reduceAdd] using bound
  by_cases h14 : i=14
  · subst i
    have bound := sha512_bits_input_boolean _ (sha512_schedule_bits_holds _ core 0 (by decide)) bit (by omega)
    simpa only [sha512ScheduleWindowBase,sha512RoundBitsRow,Nat.mul_zero,Nat.zero_add] using bound
  obtain ⟨slot,hs,eq⟩ := sha512_window_extra_coverage i hi h0 h1 h9 h14
  rw [←eq,sha512_window_extra_layout slot hs]
  exact sha512_window_witness_extra_boolean window _ (by omega)

/-- Any constrained Boolean encoding equals the canonical bits of its word. -/
theorem sha512_word_bit_decode (row : Nat → Fp) (base word : Nat)
    (boolean : ∀ bit,bit<64 → (row (base+bit)).toNat≤1)
    (eq : sha512BitsWord row base=word) (bit : Nat) (hb : bit<64) :
    row (base+bit)=Fp.ofNat (bt word bit) := by
  have bits := bt_ofBits boolean hb
  change bt (sha512BitsWord row base) bit=(row (base+bit)).toNat at bits
  rw [eq] at bits
  rw [bits,Fp.ofNat_toNat]

theorem sha512_window_witness_bit (window : List Nat) (valid : sha512WindowValid window)
    (i bit : Nat) (hi : i<16) (hb : bit<64) :
    sha512ScheduleWindowWitness window (sha512ScheduleWindowBase i+bit)=Fp.ofNat (bt (window.getD i 0) bit) :=
  sha512_word_bit_decode _ _ _ (fun bit hb => sha512_window_witness_boolean window valid i bit hi hb)
    (sha512_window_witness_word window valid i hi) bit hb

theorem sha512_window_witness_output (window : List Nat) (valid : sha512WindowValid window) :
    sha512BitsWord (sha512ScheduleWindowWitness window) 1712=(nextWindow window).getD 15 0 := by
  have core := sha512_window_witness_core_holds window valid
  have output := (sha512_window_core_words _ core).2.2.2.2
  rw [output,sha512_schedule_sound _ core]
  have inputs := sha512_window_witness_core_inputs window valid
  rw [inputs.1,inputs.2.1,inputs.2.2.1,inputs.2.2.2,sha512_window_next_last window valid.1]

theorem sha512_window_witness_output_bit (window : List Nat) (valid : sha512WindowValid window)
    (bit : Nat) (hb : bit<64) :
    sha512ScheduleWindowWitness window (1712+bit)=Fp.ofNat (bt ((nextWindow window).getD 15 0) bit) := by
  apply sha512_word_bit_decode _ _ _ _ (sha512_window_witness_output window valid) bit hb
  intro b hb
  have bound := sha512_add_word_bit _ (sha512_schedule_add_holds _ (sha512_window_witness_core_holds window valid) 2 (by decide)) 8 b (by decide) hb
  simpa only [sha512RoundAddRow,sha512RoundAddBase,←Nat.add_assoc,Nat.reduceMul,Nat.reduceAdd] using bound

/-- All 1024 next-row bit wires hold between a window and its actual update. -/
theorem sha512_window_witness_next_bit (window : List Nat) (valid : sha512WindowValid window)
    (i bit : Nat) (hi : i<16) (hb : bit<64) :
    sha512ScheduleWindowWitness window
      ((if i<15 then sha512ScheduleWindowBase (i+1) else 1712)+bit)=
    sha512ScheduleWindowWitness (nextWindow window) (sha512ScheduleWindowBase i+bit) := by
  rw [sha512_window_witness_bit _ (sha512_window_next_valid window valid) i bit hi hb]
  by_cases before : i<15
  · rw [if_pos before,sha512_window_witness_bit window valid (i+1) bit (by omega) hb,
      sha512_window_next_shift window valid.1 i before]
  · have eq : i=15 := by omega
    subst i
    rw [if_neg (by decide)]
    exact sha512_window_witness_output_bit window valid bit hb

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
theorem sha512_window_constraints_current :
    sha512ScheduleWindowConstraints.all sha512CurrentExpr=true := by decide

/-- Universal actual AIR completeness. The constructed trace uses specification
iteration, with no assumed local-Holds or cross-row equality hypotheses. -/
theorem sha512_window_witness_trace_holds (initial : List Nat) (valid : sha512WindowValid initial)
    (logSize : Nat) (height : 1≤logSize ∧ logSize≤22) :
    Holds sha512ScheduleWindowSequenceAir [] (sha512ScheduleWindowWitnessTrace initial logSize) := by
  constructor
  · intro t ht
    have eq : t=0 := by simpa [sha512ScheduleWindowSequenceAir] using ht
    subst t
    exact height
  · intro t ht r hr e he
    have eq : t=0 := by simpa [sha512ScheduleWindowSequenceAir] using ht
    subst t
    rcases List.mem_append.mp he with he | he
    · rw [instruction_local_eval e _ 0 r [] (sha512_current_expr_local e
        (List.all_eq_true.mp sha512_window_constraints_current e he))]
      exact sha512_window_witness_holds _ (sha512_window_run_valid initial valid r) e he
    · obtain ⟨pair,hp,rfl⟩ := List.mem_map.mp he
      obtain ⟨i,hi,hp⟩ := List.mem_flatMap.mp hp
      obtain ⟨bit,hb,rfl⟩ := List.mem_map.mp hp
      apply instruction_sequence_eval_complete _ [] 0 r _ _ hr
      intro next
      exact sha512_window_witness_next_bit _ (sha512_window_run_valid initial valid r)
        i bit (List.mem_range.mp hi) (List.mem_range.mp hb)
  · intro t ht r hr i hi
    have eq : t=0 := by simpa [sha512ScheduleWindowSequenceAir] using ht
    subst t
    simp [sha512ScheduleWindowSequenceAir,sha512ScheduleWindowSequenceTable,
      instructionSequenceTable,sha512ScheduleWindowTable] at hi
  · intro b m
    simp [busCount,busCount.go,tableBusCount,sha512ScheduleWindowSequenceAir,
      sha512ScheduleWindowSequenceTable,instructionSequenceTable,sha512ScheduleWindowTable]

theorem sha512_window_witness_trace_decode (initial : List Nat) (valid : sha512WindowValid initial)
    (logSize r : Nat) :
    sha512ScheduleWindow ((sha512ScheduleWindowWitnessTrace initial logSize).cell 0 r)=
      sha512ScheduleWindowRun initial r :=
  sha512_window_witness_decode _ (sha512_window_run_valid initial valid r)

end NearCompression
