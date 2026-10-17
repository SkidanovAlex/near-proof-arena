import NearCompression.SHA512RoundWitness

/-! Arithmetic core of one SHA-512 message-schedule expansion. The other
window words and their temporal authentication are not constrained here. -/
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.View ZkFormal.Sha.Sound
open NearSpecV3.SHA512

def sha512ScheduleWires : List SHA512RoundWire :=
  [⟨1152,384,true⟩,⟨1360,896,true⟩,⟨1568,1160,false⟩,⟨1572,1368,false⟩]

def sha512ScheduleComponents : List (Nat × List Expr) :=
  [(0,sha512BitsConstraints),(576,sha512BitsConstraints)] ++
    (List.range 3).map (fun i => (sha512RoundAddBase i,instructionAdd64Constraints))

def sha512ScheduleConstraints : List Expr :=
  sha512ScheduleComponents.flatMap (fun component => component.2.map (sha512RelocateExpr component.1)) ++
    sha512ScheduleWires.flatMap sha512RoundWireConstraints

def sha512ScheduleTable : Table := ⟨1776,sha512ScheduleConstraints,[],22⟩
def sha512ScheduleHolds (row : Nat → Fp) : Prop :=
  ∀ e ∈ sha512ScheduleConstraints, e.evalWith (instructionAddEnv row) = 0

def sha512ScheduleW14 (row : Nat → Fp) : Nat := sha512BitsWord (sha512RoundBitsRow row 0) 0
def sha512ScheduleW1 (row : Nat → Fp) : Nat := sha512BitsWord (sha512RoundBitsRow row 1) 0
def sha512ScheduleW9 (row : Nat → Fp) : Nat := instructionAdd64Word (sha512RoundAddRow row 0) 4
def sha512ScheduleW0 (row : Nat → Fp) : Nat := instructionAdd64Word (sha512RoundAddRow row 1) 4
def sha512ScheduleOutput (row : Nat → Fp) : Nat := instructionAdd64Word (sha512RoundAddRow row 2) 8

theorem sha512_schedule_component_holds (row : Nat → Fp) (h : sha512ScheduleHolds row)
    (offset : Nat) (constraints : List Expr)
    (component : (offset, constraints) ∈ sha512ScheduleComponents) :
    ∀ e ∈ constraints, e.evalWith (instructionAddEnv (fun c => row (offset + c))) = 0 := by
  intro e he
  have hv := h (sha512RelocateExpr offset e) (List.mem_append_left _
    (List.mem_flatMap.mpr ⟨(offset, constraints), component, List.mem_map.mpr ⟨e, he, rfl⟩⟩))
  rwa [sha512_relocate_eval] at hv

theorem sha512_schedule_bits_holds (row : Nat → Fp) (h : sha512ScheduleHolds row)
    (i : Nat) (hi : i < 2) : sha512BitsHolds (sha512RoundBitsRow row i) := by
  apply sha512_schedule_component_holds row h (576 * i) sha512BitsConstraints
  have cases : i = 0 ∨ i = 1 := by omega
  rcases cases with hi | hi <;> subst i <;> simp [sha512ScheduleComponents]

theorem sha512_schedule_add_holds (row : Nat → Fp) (h : sha512ScheduleHolds row)
    (i : Nat) (hi : i < 3) : instructionAdd64Holds (sha512RoundAddRow row i) := by
  apply sha512_schedule_component_holds row h (sha512RoundAddBase i) instructionAdd64Constraints
  exact List.mem_append_right _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)

theorem sha512_schedule_wire_limb (row : Nat → Fp) (h : sha512ScheduleHolds row)
    (wire : SHA512RoundWire) (hw : wire ∈ sha512ScheduleWires) (limb : Nat) (hl : limb < 4) :
    row (wire.target + limb) = (sha512RoundWireExpr wire limb).evalWith (instructionAddEnv row) := by
  have hv := h (.add (.col (wire.target + limb) false) (.neg (sha512RoundWireExpr wire limb)))
    (List.mem_append_right _ (List.mem_flatMap.mpr ⟨wire, hw,
      List.mem_map.mpr ⟨limb, List.mem_range.mpr hl, rfl⟩⟩))
  change row (wire.target + limb) + -(sha512RoundWireExpr wire limb).evalWith (instructionAddEnv row) = 0 at hv
  grind

theorem sha512_schedule_limb_word_wire (row : Nat → Fp) (h : sha512ScheduleHolds row)
    (target source : Nat) (hw : ⟨target, source, false⟩ ∈ sha512ScheduleWires) :
    instructionAdd64Word row target = instructionAdd64Word row source := by
  have eqs (i : Nat) (hi : i < 4) : row (target + i) = row (source + i) :=
    sha512_schedule_wire_limb row h _ hw i hi
  have h0 := eqs 0 (by decide)
  have h1 := eqs 1 (by decide)
  have h2 := eqs 2 (by decide)
  have h3 := eqs 3 (by decide)
  simp only [Nat.add_zero] at h0
  simp only [instructionAdd64Word, h0, h1, h2, h3]

theorem sha512_schedule_bit_word_wire (row : Nat → Fp) (h : sha512ScheduleHolds row)
    (target bitRow slot : Nat) (hi : bitRow < 2) (hs : slot < 6)
    (hw : ⟨target, 576 * bitRow + (192 + 64 * slot), true⟩ ∈ sha512ScheduleWires) :
    instructionAdd64Word row target = sha512BitsWord (sha512RoundBitsRow row bitRow) (192 + 64 * slot) := by
  have boolean (bit : Nat) (hb : bit < 64) :
      (row (576 * bitRow + (192 + 64 * slot) + bit)).toNat ≤ 1 := by
    have hb' := sha512_bits_output_boolean (sha512RoundBitsRow row bitRow)
      (sha512_schedule_bits_holds row h bitRow hi) slot bit hs hb
    simpa only [sha512RoundBitsRow, Nat.add_assoc] using hb'
  have eq := sha512_bit_word_binding row target (576 * bitRow + (192 + 64 * slot)) boolean
    (fun limb hl => sha512_schedule_wire_limb row h _ hw limb hl)
  simpa only [sha512BitsWord, sha512RoundBitsRow, Nat.add_assoc] using eq


/-- The constrained result is the exact new-word formula used by nextWindow. -/
theorem sha512_schedule_sound (row : Nat → Fp) (h : sha512ScheduleHolds row) :
    sha512ScheduleOutput row = add64 (add64 (ssig1 (sha512ScheduleW14 row)) (sha512ScheduleW9 row))
      (add64 (ssig0 (sha512ScheduleW1 row)) (sha512ScheduleW0 row)) := by
  have w0 := sha512_schedule_bit_word_wire row h 1152 0 3 (by decide) (by decide) (by decide)
  have w1 := sha512_schedule_bit_word_wire row h 1360 1 2 (by decide) (by decide) (by decide)
  have w2 := sha512_schedule_limb_word_wire row h 1568 1160 (by decide)
  have w3 := sha512_schedule_limb_word_wire row h 1572 1368 (by decide)
  rw [sha512_bits_output _ (sha512_schedule_bits_holds row h 0 (by decide)) 3 (by decide)] at w0
  rw [sha512_bits_output _ (sha512_schedule_bits_holds row h 1 (by decide)) 2 (by decide)] at w1
  have a0 := sha512_add_air_sound _ (sha512_schedule_add_holds row h 0 (by decide))
  have a1 := sha512_add_air_sound _ (sha512_schedule_add_holds row h 1 (by decide))
  have a2 := sha512_add_air_sound _ (sha512_schedule_add_holds row h 2 (by decide))
  simp only [sha512BitsFunction] at w0 w1
  simp only [sha512ScheduleOutput,sha512ScheduleW14,sha512ScheduleW1,sha512ScheduleW9,sha512ScheduleW0,
    instructionAdd64Word,sha512RoundAddRow,sha512RoundAddBase,Nat.add_assoc,Nat.reduceMul,Nat.reduceAdd]
    at a0 a1 a2 w0 w1 w2 w3 ⊢
  rw [w0] at a0
  rw [w1] at a1
  rw [w2,w3,←a0,←a1] at a2
  exact a2.symm

/-- Exact actual nextWindow behavior with the twelve unused words explicit. -/
theorem sha512_schedule_next_window (row : Nat → Fp) (h : sha512ScheduleHolds row)
    (w2 w3 w4 w5 w6 w7 w8 w10 w11 w12 w13 w15 : Nat) :
    nextWindow [sha512ScheduleW0 row,sha512ScheduleW1 row,w2,w3,w4,w5,w6,w7,w8,
      sha512ScheduleW9 row,w10,w11,w12,w13,sha512ScheduleW14 row,w15] =
    [sha512ScheduleW1 row,w2,w3,w4,w5,w6,w7,w8,sha512ScheduleW9 row,
      w10,w11,w12,w13,sha512ScheduleW14 row,w15,sha512ScheduleOutput row] := by
  rw [sha512_schedule_sound row h]
  rfl

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
theorem sha512_schedule_table_wf :
    sha512ScheduleTable.wf ⟨[sha512ScheduleTable],0,0⟩ 3 = true := by decide

set_option maxRecDepth 65536 in
theorem sha512_schedule_table_size :
    sha512ScheduleTable.width = 1776 ∧ sha512ScheduleTable.constraints.length = 1804 := by decide

def sha512ScheduleInputBounds (w0 w1 w9 w14 : Nat) : Prop :=
  w0 < 2^64 ∧ w1 < 2^64 ∧ w9 < 2^64 ∧ w14 < 2^64

def sha512ScheduleWitnessInputs (w0 w1 w9 w14 : Nat) : Nat → Nat × Nat
  | 0 => (ssig1 w14,w9)
  | 1 => (ssig0 w1,w0)
  | _ => (add64 (ssig1 w14) w9,add64 (ssig0 w1) w0)

def sha512ScheduleWitnessBits (_w0 w1 _w9 w14 i : Nat) : Nat → Fp :=
  sha512BitsWitness (UInt64.ofNat (if i=0 then w14 else w1)) 0 0

def sha512ScheduleWitnessAdd (w0 w1 w9 w14 i : Nat) : Nat → Fp :=
  instructionAdd64Witness (UInt64.ofNat (sha512ScheduleWitnessInputs w0 w1 w9 w14 i).1)
    (UInt64.ofNat (sha512ScheduleWitnessInputs w0 w1 w9 w14 i).2)

def sha512ScheduleWitness (w0 w1 w9 w14 col : Nat) : Fp :=
  if col < 576 then sha512ScheduleWitnessBits w0 w1 w9 w14 0 col else
  if col < 1152 then sha512ScheduleWitnessBits w0 w1 w9 w14 1 (col-576) else
    sha512ScheduleWitnessAdd w0 w1 w9 w14 ((col-1152)/208) ((col-1152)%208)

theorem sha512_schedule_witness_bits_prefix (w0 w1 w9 w14 i col : Nat)
    (hi : i < 2) (hc : col < 576) :
    sha512RoundBitsRow (sha512ScheduleWitness w0 w1 w9 w14) i col = sha512ScheduleWitnessBits w0 w1 w9 w14 i col := by
  have cases : i = 0 ∨ i = 1 := by omega
  rcases cases with hi | hi <;> subst i
  · simpa only [sha512RoundBitsRow, Nat.mul_zero, Nat.zero_add, sha512ScheduleWitness,
      if_pos hc]
  · have hn : ¬576 + col < 576 := by omega
    have hlt : 576 + col < 1152 := by omega
    simp only [sha512RoundBitsRow, Nat.mul_one, sha512ScheduleWitness, if_neg hn,
      if_pos hlt, Nat.add_sub_cancel_left]

theorem sha512_schedule_witness_add_prefix (w0 w1 w9 w14 i col : Nat) (hc : col < 208) :
    sha512RoundAddRow (sha512ScheduleWitness w0 w1 w9 w14) i col = sha512ScheduleWitnessAdd w0 w1 w9 w14 i col := by
  have h0 : ¬1152 + 208 * i + col < 576 := by omega
  have h1 : ¬1152 + 208 * i + col < 1152 := by omega
  have hd : (1152 + 208 * i + col - 1152) / 208 = i := by omega
  have hm : (1152 + 208 * i + col - 1152) % 208 = col := by omega
  simp only [sha512RoundAddRow, sha512RoundAddBase, sha512ScheduleWitness, if_neg h0, if_neg h1, hd, hm]

theorem sha512_schedule_witness_bits_holds (w0 w1 w9 w14 i : Nat) (hi : i < 2) :
    sha512BitsHolds (sha512RoundBitsRow (sha512ScheduleWitness w0 w1 w9 w14) i) := by
  have honest : sha512BitsHolds (sha512ScheduleWitnessBits w0 w1 w9 w14 i) := by
    unfold sha512ScheduleWitnessBits
    apply sha512_bits_witness_holds
  intro e he
  have bound := of_decide_eq_true (List.all_eq_true.mp sha512_round_component_bounds.1 e he)
  rw [instruction_control_prefix_eval e _ (sha512ScheduleWitnessBits w0 w1 w9 w14 i) 576 bound
    (fun col hc => sha512_schedule_witness_bits_prefix w0 w1 w9 w14 i col hi hc)]
  exact honest e he

theorem sha512_schedule_witness_add_holds (w0 w1 w9 w14 i : Nat) :
    instructionAdd64Holds (sha512RoundAddRow (sha512ScheduleWitness w0 w1 w9 w14) i) := by
  have honest : instructionAdd64Holds (sha512ScheduleWitnessAdd w0 w1 w9 w14 i) :=
    instruction_add64_witness_holds _ _
  intro e he
  have bound := of_decide_eq_true (List.all_eq_true.mp sha512_round_component_bounds.2 e he)
  rw [instruction_control_prefix_eval e _ (sha512ScheduleWitnessAdd w0 w1 w9 w14 i) 208 bound
    (fun col hc => sha512_schedule_witness_add_prefix w0 w1 w9 w14 i col hc)]
  exact honest e he


theorem sha512_schedule_witness_inputs_bound (w0 w1 w9 w14 : Nat)
    (bounds : sha512ScheduleInputBounds w0 w1 w9 w14) (i : Nat) :
    (sha512ScheduleWitnessInputs w0 w1 w9 w14 i).1 < 2^64 ∧
    (sha512ScheduleWitnessInputs w0 w1 w9 w14 i).2 < 2^64 := by
  obtain ⟨h0,h1,h9,h14⟩ := bounds
  cases i with
  | zero => exact ⟨sha512_sigS_lt h14 19 61 6,h9⟩
  | succ i => cases i with
    | zero => exact ⟨sha512_sigS_lt h1 1 8 7,h0⟩
    | succ i => exact ⟨Nat.mod_lt _ (by decide),Nat.mod_lt _ (by decide)⟩

theorem sha512_schedule_witness_add_words (w0 w1 w9 w14 : Nat)
    (bounds : sha512ScheduleInputBounds w0 w1 w9 w14) (i : Nat) :
    instructionAdd64Word (sha512RoundAddRow (sha512ScheduleWitness w0 w1 w9 w14) i) 0 =
      (sha512ScheduleWitnessInputs w0 w1 w9 w14 i).1 ∧
    instructionAdd64Word (sha512RoundAddRow (sha512ScheduleWitness w0 w1 w9 w14) i) 4 =
      (sha512ScheduleWitnessInputs w0 w1 w9 w14 i).2 := by
  have eq := instruction_add64_witness_inputs
    (UInt64.ofNat (sha512ScheduleWitnessInputs w0 w1 w9 w14 i).1)
    (UInt64.ofNat (sha512ScheduleWitnessInputs w0 w1 w9 w14 i).2)
  have hb := sha512_schedule_witness_inputs_bound w0 w1 w9 w14 bounds i
  have p (col : Nat) (hc : col < 208) := sha512_schedule_witness_add_prefix w0 w1 w9 w14 i col hc
  simp only [instructionAdd64Word, Nat.zero_add] at eq ⊢
  rw [p 0 (by decide), p 1 (by decide), p 2 (by decide), p 3 (by decide),
    p 4 (by decide), p 5 (by decide), p 6 (by decide), p 7 (by decide)]
  change (_ = (sha512ScheduleWitnessInputs w0 w1 w9 w14 i).1 ∧ _ = (sha512ScheduleWitnessInputs w0 w1 w9 w14 i).2)
  simpa [sha512ScheduleWitnessAdd, Nat.mod_eq_of_lt hb.1, Nat.mod_eq_of_lt hb.2] using eq

theorem sha512_schedule_witness_add_output (w0 w1 w9 w14 : Nat)
    (bounds : sha512ScheduleInputBounds w0 w1 w9 w14) (i : Nat) :
    instructionAdd64Word (sha512RoundAddRow (sha512ScheduleWitness w0 w1 w9 w14) i) 8 =
      add64 (sha512ScheduleWitnessInputs w0 w1 w9 w14 i).1 (sha512ScheduleWitnessInputs w0 w1 w9 w14 i).2 := by
  have eq := sha512_add_air_sound _ (sha512_schedule_witness_add_holds w0 w1 w9 w14 i)
  have inputs := sha512_schedule_witness_add_words w0 w1 w9 w14 bounds i
  rw [inputs.1, inputs.2] at eq
  exact eq.symm


theorem sha512_schedule_witness_bits_input (w0 w1 w9 w14 : Nat)
    (bounds : sha512ScheduleInputBounds w0 w1 w9 w14) (i slot : Nat) (hi : i<2) (hs : slot<3) :
    sha512BitsWord (sha512RoundBitsRow (sha512ScheduleWitness w0 w1 w9 w14) i) (64*slot) =
      if slot=0 then (if i=0 then w14 else w1) else 0 := by
  have eq : sha512BitsWord (sha512RoundBitsRow (sha512ScheduleWitness w0 w1 w9 w14) i) (64*slot) =
      sha512BitsWord (sha512ScheduleWitnessBits w0 w1 w9 w14 i) (64*slot) := by
    apply ofBits_congr
    intro bit hb
    rw [sha512_schedule_witness_bits_prefix w0 w1 w9 w14 i _ hi (by omega)]
  rw [eq]
  unfold sha512ScheduleWitnessBits
  rw [sha512_bits_witness_input _ _ _ slot hs]
  have hb : (if i=0 then w14 else w1) < 2^64 := by split <;> first | exact bounds.2.2.2 | exact bounds.2.1
  have cases : slot=0 ∨ slot=1 ∨ slot=2 := by omega
  rcases cases with h | h | h <;> subst slot <;>
    simp [sha512BitsInput,Nat.mod_eq_of_lt hb]

theorem sha512_schedule_witness_bits_output (w0 w1 w9 w14 : Nat)
    (bounds : sha512ScheduleInputBounds w0 w1 w9 w14) (i slot : Nat) (hi : i<2) (hs : slot<6) :
    sha512BitsWord (sha512RoundBitsRow (sha512ScheduleWitness w0 w1 w9 w14) i) (192+64*slot) =
      sha512BitsFunction slot (if i=0 then w14 else w1) 0 0 := by
  rw [sha512_bits_output _ (sha512_schedule_witness_bits_holds w0 w1 w9 w14 i hi) slot hs]
  have h0 := sha512_schedule_witness_bits_input w0 w1 w9 w14 bounds i 0 hi (by decide)
  have h1 := sha512_schedule_witness_bits_input w0 w1 w9 w14 bounds i 1 hi (by decide)
  have h2 := sha512_schedule_witness_bits_input w0 w1 w9 w14 bounds i 2 hi (by decide)
  simp only [Nat.reduceMul,show (1=0) = False from propext (by decide),
    show (2=0) = False from propext (by decide),ite_true,ite_false] at h0 h1 h2
  rw [h0,h1,h2]

theorem sha512_schedule_witness_limb_link (w0 w1 w9 w14 : Nat)
    (target source targetBase sourceBase : Nat)
    (ht : targetBase + 4 ≤ 12) (hs : sourceBase + 4 ≤ 12)
    (eq : instructionAdd64Word (sha512RoundAddRow (sha512ScheduleWitness w0 w1 w9 w14) target) targetBase =
      instructionAdd64Word (sha512RoundAddRow (sha512ScheduleWitness w0 w1 w9 w14) source) sourceBase)
    (i : Nat) (hi : i < 4) :
    sha512ScheduleWitness w0 w1 w9 w14 (sha512RoundAddBase target + targetBase + i) =
      sha512ScheduleWitness w0 w1 w9 w14 (sha512RoundAddBase source + sourceBase + i) := by
  simp only [Nat.add_assoc]
  apply sha512_four_limb_unique
    (fun j => sha512RoundAddRow (sha512ScheduleWitness w0 w1 w9 w14) target (targetBase+j))
    (fun j => sha512RoundAddRow (sha512ScheduleWitness w0 w1 w9 w14) source (sourceBase+j))
  · intro j hj
    exact instruction_add64_ranges _ (sha512_schedule_witness_add_holds w0 w1 w9 w14 target) _ (by omega)
  · intro j hj
    exact instruction_add64_ranges _ (sha512_schedule_witness_add_holds w0 w1 w9 w14 source) _ (by omega)
  · simpa only [instructionAdd64Word,Nat.add_zero,Nat.add_assoc] using eq
  · exact hi

theorem sha512_schedule_witness_bit_link (w0 w1 w9 w14 : Nat)
    (target targetBase source slot : Nat)
    (ht : targetBase + 4 ≤ 12) (hs : source < 2) (hslot : slot < 6)
    (eq : instructionAdd64Word (sha512RoundAddRow (sha512ScheduleWitness w0 w1 w9 w14) target) targetBase =
      sha512BitsWord (sha512RoundBitsRow (sha512ScheduleWitness w0 w1 w9 w14) source) (192+64*slot))
    (i : Nat) (hi : i < 4) :
    sha512ScheduleWitness w0 w1 w9 w14 (sha512RoundAddBase target + targetBase + i) =
      (instructionBitExpr (576*source+(192+64*slot)+16*i) 16).evalWith
        (instructionAddEnv (sha512ScheduleWitness w0 w1 w9 w14)) := by
  apply sha512_bit_word_binding_reverse
  · intro bit hb
    have h := sha512_bits_output_boolean _ (sha512_schedule_witness_bits_holds w0 w1 w9 w14 source hs) slot bit hslot hb
    simpa only [sha512RoundBitsRow,Nat.add_assoc] using h
  · intro limb hl
    have h := instruction_add64_ranges _ (sha512_schedule_witness_add_holds w0 w1 w9 w14 target) (targetBase+limb) (by omega)
    simpa only [sha512RoundAddRow,Nat.add_assoc] using h
  · simpa only [instructionAdd64Word,sha512BitsWord,sha512RoundAddRow,sha512RoundBitsRow,
      Nat.add_assoc] using eq
  · exact hi


theorem sha512_schedule_witness_wires (w0 w1 w9 w14 : Nat)
    (bounds : sha512ScheduleInputBounds w0 w1 w9 w14) (wire : SHA512RoundWire)
    (hw : wire ∈ sha512ScheduleWires) (i : Nat) (hi : i<4) :
    sha512ScheduleWitness w0 w1 w9 w14 (wire.target+i) =
      (sha512RoundWireExpr wire i).evalWith (instructionAddEnv (sha512ScheduleWitness w0 w1 w9 w14)) := by
  have a (j : Nat) := sha512_schedule_witness_add_words w0 w1 w9 w14 bounds j
  have o (j : Nat) := sha512_schedule_witness_add_output w0 w1 w9 w14 bounds j
  have b (j slot : Nat) (hj : j<2) (hs : slot<6) :=
    sha512_schedule_witness_bits_output w0 w1 w9 w14 bounds j slot hj hs
  simp only [sha512ScheduleWires,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with hw | hw | hw | hw <;> subst wire
  · apply sha512_schedule_witness_bit_link w0 w1 w9 w14 0 0 0 3 (by decide) (by decide) (by decide) _ i hi
    rw [(a 0).1,b 0 3 (by decide) (by decide)]
    rfl
  · apply sha512_schedule_witness_bit_link w0 w1 w9 w14 1 0 1 2 (by decide) (by decide) (by decide) _ i hi
    rw [(a 1).1,b 1 2 (by decide) (by decide)]
    rfl
  · apply sha512_schedule_witness_limb_link w0 w1 w9 w14 2 0 0 8 (by decide) (by decide) _ i hi
    rw [(a 2).1,o 0]
    rfl
  · apply sha512_schedule_witness_limb_link w0 w1 w9 w14 2 1 4 8 (by decide) (by decide) _ i hi
    rw [(a 2).2,o 1]
    rfl

theorem sha512_schedule_witness_inputs (w0 w1 w9 w14 : Nat)
    (bounds : sha512ScheduleInputBounds w0 w1 w9 w14) :
    sha512ScheduleW0 (sha512ScheduleWitness w0 w1 w9 w14) = w0 ∧
    sha512ScheduleW1 (sha512ScheduleWitness w0 w1 w9 w14) = w1 ∧
    sha512ScheduleW9 (sha512ScheduleWitness w0 w1 w9 w14) = w9 ∧
    sha512ScheduleW14 (sha512ScheduleWitness w0 w1 w9 w14) = w14 := by
  have b0 := sha512_schedule_witness_bits_input w0 w1 w9 w14 bounds 0 0 (by decide) (by decide)
  have b1 := sha512_schedule_witness_bits_input w0 w1 w9 w14 bounds 1 0 (by decide) (by decide)
  have a0 := sha512_schedule_witness_add_words w0 w1 w9 w14 bounds 0
  have a1 := sha512_schedule_witness_add_words w0 w1 w9 w14 bounds 1
  exact ⟨a1.2,by simpa [sha512ScheduleW1] using b1,a0.2,by simpa [sha512ScheduleW14] using b0⟩

/-- Universal completeness for bounded SHA-512 schedule inputs. Every component
polynomial and every sixteen-bit connecting wire vanishes. -/
theorem sha512_schedule_witness_holds (w0 w1 w9 w14 : Nat)
    (bounds : sha512ScheduleInputBounds w0 w1 w9 w14) :
    sha512ScheduleHolds (sha512ScheduleWitness w0 w1 w9 w14) := by
  intro e he
  rcases List.mem_append.mp he with he | he
  · obtain ⟨⟨offset, constraints⟩,hc,he⟩ := List.mem_flatMap.mp he
    obtain ⟨inner,hi,rfl⟩ := List.mem_map.mp he
    rw [sha512_relocate_eval]
    simp only [sha512ScheduleComponents,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with (hc | hc) | hc
    · cases hc
      exact sha512_schedule_witness_bits_holds w0 w1 w9 w14 0 (by decide) inner hi
    · cases hc
      exact sha512_schedule_witness_bits_holds w0 w1 w9 w14 1 (by decide) inner hi
    · obtain ⟨j,hj,hc⟩ := List.mem_map.mp hc
      cases hc
      exact sha512_schedule_witness_add_holds w0 w1 w9 w14 j inner hi
  · obtain ⟨wire,hw,he⟩ := List.mem_flatMap.mp he
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp he
    have eq := sha512_schedule_witness_wires w0 w1 w9 w14 bounds wire hw i (List.mem_range.mp hi)
    change sha512ScheduleWitness w0 w1 w9 w14 (wire.target+i) +
      -(sha512RoundWireExpr wire i).evalWith (instructionAddEnv (sha512ScheduleWitness w0 w1 w9 w14)) = 0
    rw [eq]
    grind

end NearCompression
