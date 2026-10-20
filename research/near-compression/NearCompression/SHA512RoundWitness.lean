import NearCompression.SHA512Round
import NearCompression.SHA512BitBinding
import NearCompression.InstructionAddControl

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound ZkFormal.Sha.View
open NearSpecV3.SHA512

/-- The SHA-512 word domain, including the two supplied round inputs. -/
def sha512RoundInputBounds (v : Vars) (k w : Nat) : Prop :=
  v.a < 2^64 ∧ v.b < 2^64 ∧ v.c < 2^64 ∧ v.d < 2^64 ∧
  v.e < 2^64 ∧ v.f < 2^64 ∧ v.g < 2^64 ∧ v.h < 2^64 ∧ k < 2^64 ∧ w < 2^64

def sha512RoundWitnessT1 (v : Vars) (k w : Nat) : Nat :=
  add64 (add64 (add64 (add64 v.h (bsig1 v.e)) (ch v.e v.f v.g)) k) w

def sha512RoundWitnessT2 (v : Vars) : Nat := add64 (bsig0 v.a) (maj v.a v.b v.c)

def sha512RoundWitnessInputs (v : Vars) (k w : Nat) : Nat → Nat × Nat
  | 0 => (v.h, bsig1 v.e)
  | 1 => (add64 v.h (bsig1 v.e), ch v.e v.f v.g)
  | 2 => (add64 (add64 v.h (bsig1 v.e)) (ch v.e v.f v.g), k)
  | 3 => (add64 (add64 (add64 v.h (bsig1 v.e)) (ch v.e v.f v.g)) k, w)
  | 4 => (bsig0 v.a, maj v.a v.b v.c)
  | 5 => (sha512RoundWitnessT1 v k w, sha512RoundWitnessT2 v)
  | _ => (v.d, sha512RoundWitnessT1 v k w)

def sha512RoundWitnessBits (v : Vars) (i : Nat) : Nat → Fp :=
  if i = 0 then sha512BitsWitness (UInt64.ofNat v.a) (UInt64.ofNat v.b) (UInt64.ofNat v.c)
  else sha512BitsWitness (UInt64.ofNat v.e) (UInt64.ofNat v.f) (UInt64.ofNat v.g)

def sha512RoundWitnessAdd (v : Vars) (k w i : Nat) : Nat → Fp :=
  instructionAdd64Witness (UInt64.ofNat (sha512RoundWitnessInputs v k w i).1)
    (UInt64.ofNat (sha512RoundWitnessInputs v k w i).2)

def sha512RoundWitness (v : Vars) (k w col : Nat) : Fp :=
  if col < 576 then sha512RoundWitnessBits v 0 col else
  if col < 1152 then sha512RoundWitnessBits v 1 (col - 576) else
    sha512RoundWitnessAdd v k w ((col - 1152) / 208) ((col - 1152) % 208)

theorem sha512_round_witness_bits_prefix (v : Vars) (k w i col : Nat)
    (hi : i < 2) (hc : col < 576) :
    sha512RoundBitsRow (sha512RoundWitness v k w) i col = sha512RoundWitnessBits v i col := by
  have cases : i = 0 ∨ i = 1 := by omega
  rcases cases with hi | hi <;> subst i
  · simpa only [sha512RoundBitsRow, Nat.mul_zero, Nat.zero_add, sha512RoundWitness,
      if_pos hc]
  · have hn : ¬576 + col < 576 := by omega
    have hlt : 576 + col < 1152 := by omega
    simp only [sha512RoundBitsRow, Nat.mul_one, sha512RoundWitness, if_neg hn,
      if_pos hlt, Nat.add_sub_cancel_left]

theorem sha512_round_witness_add_prefix (v : Vars) (k w i col : Nat) (hc : col < 208) :
    sha512RoundAddRow (sha512RoundWitness v k w) i col = sha512RoundWitnessAdd v k w i col := by
  have h0 : ¬1152 + 208 * i + col < 576 := by omega
  have h1 : ¬1152 + 208 * i + col < 1152 := by omega
  have hd : (1152 + 208 * i + col - 1152) / 208 = i := by omega
  have hm : (1152 + 208 * i + col - 1152) % 208 = col := by omega
  simp only [sha512RoundAddRow, sha512RoundAddBase, sha512RoundWitness, if_neg h0, if_neg h1, hd, hm]

set_option maxRecDepth 32768 in
theorem sha512_round_component_bounds :
    sha512BitsConstraints.all (fun e => decide (e.colBound ≤ 576)) = true ∧
    instructionAdd64Constraints.all (fun e => decide (e.colBound ≤ 208)) = true := by decide

theorem sha512_round_witness_bits_holds (v : Vars) (k w i : Nat) (hi : i < 2) :
    sha512BitsHolds (sha512RoundBitsRow (sha512RoundWitness v k w) i) := by
  have honest : sha512BitsHolds (sha512RoundWitnessBits v i) := by
    unfold sha512RoundWitnessBits
    split <;> apply sha512_bits_witness_holds
  intro e he
  have bound := of_decide_eq_true (List.all_eq_true.mp sha512_round_component_bounds.1 e he)
  rw [instruction_control_prefix_eval e _ (sha512RoundWitnessBits v i) 576 bound
    (fun col hc => sha512_round_witness_bits_prefix v k w i col hi hc)]
  exact honest e he

theorem sha512_round_witness_add_holds (v : Vars) (k w i : Nat) :
    instructionAdd64Holds (sha512RoundAddRow (sha512RoundWitness v k w) i) := by
  have honest : instructionAdd64Holds (sha512RoundWitnessAdd v k w i) :=
    instruction_add64_witness_holds _ _
  intro e he
  have bound := of_decide_eq_true (List.all_eq_true.mp sha512_round_component_bounds.2 e he)
  rw [instruction_control_prefix_eval e _ (sha512RoundWitnessAdd v k w i) 208 bound
    (fun col hc => sha512_round_witness_add_prefix v k w i col hc)]
  exact honest e he

theorem sha512_round_witness_inputs_bound (v : Vars) (k w : Nat)
    (bounds : sha512RoundInputBounds v k w) (i : Nat) :
    (sha512RoundWitnessInputs v k w i).1 < 2^64 ∧ (sha512RoundWitnessInputs v k w i).2 < 2^64 := by
  obtain ⟨ha,hb,hc,hd,he,hf,hg,hh,hk,hw⟩ := bounds
  have addBound (a b : Nat) : add64 a b < 2^64 := Nat.mod_lt _ (by decide)
  cases i with
  | zero => exact ⟨hh, sha512_sig3_lt _ _ _ _⟩
  | succ i => cases i with
    | zero => exact ⟨addBound _ _, sha512_ch_lt _ hf hg⟩
    | succ i => cases i with
      | zero => exact ⟨addBound _ _, hk⟩
      | succ i => cases i with
        | zero => exact ⟨addBound _ _, hw⟩
        | succ i => cases i with
          | zero => exact ⟨sha512_sig3_lt _ _ _ _, sha512_maj_lt _ hb hc⟩
          | succ i => cases i with
            | zero => exact ⟨addBound _ _, addBound _ _⟩
            | succ i => exact ⟨hd, addBound _ _⟩

/-- Bounded four-limb encodings are unique over the integers. -/
theorem sha512_four_limb_unique (a b : Nat → Fp)
    (ha : ∀ i, i < 4 → (a i).toNat < 65536)
    (hb : ∀ i, i < 4 → (b i).toNat < 65536)
    (eq : instructionAdd64Word a 0 = instructionAdd64Word b 0)
    (i : Nat) (hi : i < 4) : a i = b i := by
  have a0 := ha 0 (by decide); have a1 := ha 1 (by decide)
  have a2 := ha 2 (by decide); have a3 := ha 3 (by decide)
  have b0 := hb 0 (by decide); have b1 := hb 1 (by decide)
  have b2 := hb 2 (by decide); have b3 := hb 3 (by decide)
  simp only [instructionAdd64Word, Nat.zero_add] at eq
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases cases with hi | hi | hi | hi <;> subst i <;> apply Fp.ext <;> omega

theorem sha512_round_witness_add_words (v : Vars) (k w : Nat)
    (bounds : sha512RoundInputBounds v k w) (i : Nat) :
    instructionAdd64Word (sha512RoundAddRow (sha512RoundWitness v k w) i) 0 =
      (sha512RoundWitnessInputs v k w i).1 ∧
    instructionAdd64Word (sha512RoundAddRow (sha512RoundWitness v k w) i) 4 =
      (sha512RoundWitnessInputs v k w i).2 := by
  have eq := instruction_add64_witness_inputs
    (UInt64.ofNat (sha512RoundWitnessInputs v k w i).1)
    (UInt64.ofNat (sha512RoundWitnessInputs v k w i).2)
  have hb := sha512_round_witness_inputs_bound v k w bounds i
  have p (col : Nat) (hc : col < 208) := sha512_round_witness_add_prefix v k w i col hc
  simp only [instructionAdd64Word, Nat.zero_add] at eq ⊢
  rw [p 0 (by decide), p 1 (by decide), p 2 (by decide), p 3 (by decide),
    p 4 (by decide), p 5 (by decide), p 6 (by decide), p 7 (by decide)]
  change (_ = (sha512RoundWitnessInputs v k w i).1 ∧ _ = (sha512RoundWitnessInputs v k w i).2)
  simpa [sha512RoundWitnessAdd, Nat.mod_eq_of_lt hb.1, Nat.mod_eq_of_lt hb.2] using eq

theorem sha512_round_witness_add_output (v : Vars) (k w : Nat)
    (bounds : sha512RoundInputBounds v k w) (i : Nat) :
    instructionAdd64Word (sha512RoundAddRow (sha512RoundWitness v k w) i) 8 =
      add64 (sha512RoundWitnessInputs v k w i).1 (sha512RoundWitnessInputs v k w i).2 := by
  have eq := sha512_add_air_sound _ (sha512_round_witness_add_holds v k w i)
  have inputs := sha512_round_witness_add_words v k w bounds i
  rw [inputs.1, inputs.2] at eq
  exact eq.symm

def sha512RoundWitnessBitInput (v : Vars) (i slot : Nat) : Nat :=
  if i = 0 then (match slot with | 0 => v.a | 1 => v.b | _ => v.c)
  else (match slot with | 0 => v.e | 1 => v.f | _ => v.g)

theorem sha512_round_witness_bits_input (v : Vars) (k w : Nat)
    (bounds : sha512RoundInputBounds v k w) (i slot : Nat) (hi : i < 2) (hs : slot < 3) :
    sha512BitsWord (sha512RoundBitsRow (sha512RoundWitness v k w) i) (64 * slot) =
      sha512RoundWitnessBitInput v i slot := by
  have eq : sha512BitsWord (sha512RoundBitsRow (sha512RoundWitness v k w) i) (64 * slot) =
      sha512BitsWord (sha512RoundWitnessBits v i) (64 * slot) := by
    apply ofBits_congr
    intro bit hb
    rw [sha512_round_witness_bits_prefix v k w i _ hi (by omega)]
  rw [eq]
  obtain ⟨ha,hb,hc,hd,he,hf,hg,hh,hk,hw⟩ := bounds
  have cases : i = 0 ∨ i = 1 := by omega
  rcases cases with hi | hi <;> subst i
  · change sha512BitsWord (sha512BitsWitness (UInt64.ofNat v.a) (UInt64.ofNat v.b) (UInt64.ofNat v.c))
      (64 * slot) = _
    rw [sha512_bits_witness_input _ _ _ slot hs]
    have cases : slot = 0 ∨ slot = 1 ∨ slot = 2 := by omega
    rcases cases with hs | hs | hs <;> subst slot <;>
      simp [sha512BitsInput, sha512RoundWitnessBitInput, UInt64.toNat_ofNat,
        Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hc]
  · change sha512BitsWord (sha512BitsWitness (UInt64.ofNat v.e) (UInt64.ofNat v.f) (UInt64.ofNat v.g))
      (64 * slot) = _
    rw [sha512_bits_witness_input _ _ _ slot hs]
    have cases : slot = 0 ∨ slot = 1 ∨ slot = 2 := by omega
    rcases cases with hs | hs | hs <;> subst slot <;>
      simp [sha512BitsInput, sha512RoundWitnessBitInput, UInt64.toNat_ofNat,
        Nat.mod_eq_of_lt he, Nat.mod_eq_of_lt hf, Nat.mod_eq_of_lt hg]

theorem sha512_round_witness_bits_output (v : Vars) (k w : Nat)
    (bounds : sha512RoundInputBounds v k w) (i slot : Nat) (hi : i < 2) (hs : slot < 6) :
    sha512BitsWord (sha512RoundBitsRow (sha512RoundWitness v k w) i) (192 + 64 * slot) =
      sha512BitsFunction slot (sha512RoundWitnessBitInput v i 0)
        (sha512RoundWitnessBitInput v i 1) (sha512RoundWitnessBitInput v i 2) := by
  rw [sha512_bits_output _ (sha512_round_witness_bits_holds v k w i hi) slot hs]
  have h0 := sha512_round_witness_bits_input v k w bounds i 0 hi (by decide)
  have h1 := sha512_round_witness_bits_input v k w bounds i 1 hi (by decide)
  have h2 := sha512_round_witness_bits_input v k w bounds i 2 hi (by decide)
  rw [h0, h1, h2]

/-- The constructor exposes exactly the supplied bounded round inputs. -/
theorem sha512_round_witness_inputs (v : Vars) (k w : Nat)
    (bounds : sha512RoundInputBounds v k w) :
    sha512RoundVars (sha512RoundWitness v k w) = v ∧
    sha512RoundK (sha512RoundWitness v k w) = k ∧
    sha512RoundW (sha512RoundWitness v k w) = w := by
  have b00 := sha512_round_witness_bits_input v k w bounds 0 0 (by decide) (by decide)
  have b01 := sha512_round_witness_bits_input v k w bounds 0 1 (by decide) (by decide)
  have b02 := sha512_round_witness_bits_input v k w bounds 0 2 (by decide) (by decide)
  have b10 := sha512_round_witness_bits_input v k w bounds 1 0 (by decide) (by decide)
  have b11 := sha512_round_witness_bits_input v k w bounds 1 1 (by decide) (by decide)
  have b12 := sha512_round_witness_bits_input v k w bounds 1 2 (by decide) (by decide)
  have a0 := sha512_round_witness_add_words v k w bounds 0
  have a2 := sha512_round_witness_add_words v k w bounds 2
  have a3 := sha512_round_witness_add_words v k w bounds 3
  have a6 := sha512_round_witness_add_words v k w bounds 6
  simp only [sha512RoundWitnessBitInput, sha512RoundWitnessInputs,
    Nat.reduceMul, if_pos, if_neg, Nat.one_ne_zero] at b00 b01 b02 b10 b11 b12 a0 a2 a3 a6
  constructor
  · unfold sha512RoundVars
    rw [b00,b01,b02,b10,b11,b12,a0.1,a6.1]
    simp
  · exact ⟨a2.2,a3.2⟩

theorem sha512_round_witness_limb_link (v : Vars) (k w : Nat)
    (target source targetBase sourceBase : Nat)
    (ht : targetBase + 4 ≤ 12) (hs : sourceBase + 4 ≤ 12)
    (eq : instructionAdd64Word (sha512RoundAddRow (sha512RoundWitness v k w) target) targetBase =
      instructionAdd64Word (sha512RoundAddRow (sha512RoundWitness v k w) source) sourceBase)
    (i : Nat) (hi : i < 4) :
    sha512RoundWitness v k w (sha512RoundAddBase target + targetBase + i) =
      sha512RoundWitness v k w (sha512RoundAddBase source + sourceBase + i) := by
  simp only [Nat.add_assoc]
  apply sha512_four_limb_unique
    (fun j => sha512RoundAddRow (sha512RoundWitness v k w) target (targetBase+j))
    (fun j => sha512RoundAddRow (sha512RoundWitness v k w) source (sourceBase+j))
  · intro j hj
    exact instruction_add64_ranges _ (sha512_round_witness_add_holds v k w target) _ (by omega)
  · intro j hj
    exact instruction_add64_ranges _ (sha512_round_witness_add_holds v k w source) _ (by omega)
  · simpa only [instructionAdd64Word,Nat.add_zero,Nat.add_assoc] using eq
  · exact hi

theorem sha512_round_witness_bit_link (v : Vars) (k w : Nat)
    (target targetBase source slot : Nat)
    (ht : targetBase + 4 ≤ 12) (hs : source < 2) (hslot : slot < 6)
    (eq : instructionAdd64Word (sha512RoundAddRow (sha512RoundWitness v k w) target) targetBase =
      sha512BitsWord (sha512RoundBitsRow (sha512RoundWitness v k w) source) (192+64*slot))
    (i : Nat) (hi : i < 4) :
    sha512RoundWitness v k w (sha512RoundAddBase target + targetBase + i) =
      (instructionBitExpr (576*source+(192+64*slot)+16*i) 16).evalWith
        (instructionAddEnv (sha512RoundWitness v k w)) := by
  apply sha512_bit_word_binding_reverse
  · intro bit hb
    have h := sha512_bits_output_boolean _ (sha512_round_witness_bits_holds v k w source hs) slot bit hslot hb
    simpa only [sha512RoundBitsRow,Nat.add_assoc] using h
  · intro limb hl
    have h := instruction_add64_ranges _ (sha512_round_witness_add_holds v k w target) (targetBase+limb) (by omega)
    simpa only [sha512RoundAddRow,Nat.add_assoc] using h
  · simpa only [instructionAdd64Word,sha512BitsWord,sha512RoundAddRow,sha512RoundBitsRow,
      Nat.add_assoc] using eq
  · exact hi

theorem sha512_round_witness_wires (v : Vars) (k w : Nat)
    (bounds : sha512RoundInputBounds v k w) (wire : SHA512RoundWire)
    (hw : wire ∈ sha512RoundWires) (i : Nat) (hi : i < 4) :
    sha512RoundWitness v k w (wire.target+i) =
      (sha512RoundWireExpr wire i).evalWith (instructionAddEnv (sha512RoundWitness v k w)) := by
  have a (j : Nat) := sha512_round_witness_add_words v k w bounds j
  have o (j : Nat) := sha512_round_witness_add_output v k w bounds j
  have b (j slot : Nat) (hj : j < 2) (hs : slot < 6) :=
    sha512_round_witness_bits_output v k w bounds j slot hj hs
  simp only [sha512RoundWires,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with hw | hw | hw | hw | hw | hw | hw | hw | hw | hw <;> subst wire
  · apply sha512_round_witness_bit_link v k w 0 4 1 1 (by decide) (by decide) (by decide) _ i hi
    rw [(a 0).2, b 1 1 (by decide) (by decide)]
    rfl
  · apply sha512_round_witness_limb_link v k w 1 0 0 8 (by decide) (by decide) _ i hi
    rw [(a 1).1, o 0]
    rfl
  · apply sha512_round_witness_bit_link v k w 1 4 1 4 (by decide) (by decide) (by decide) _ i hi
    rw [(a 1).2, b 1 4 (by decide) (by decide)]
    rfl
  · apply sha512_round_witness_limb_link v k w 2 1 0 8 (by decide) (by decide) _ i hi
    rw [(a 2).1, o 1]
    rfl
  · apply sha512_round_witness_limb_link v k w 3 2 0 8 (by decide) (by decide) _ i hi
    rw [(a 3).1, o 2]
    rfl
  · apply sha512_round_witness_bit_link v k w 4 0 0 0 (by decide) (by decide) (by decide) _ i hi
    rw [(a 4).1, b 0 0 (by decide) (by decide)]
    rfl
  · apply sha512_round_witness_bit_link v k w 4 4 0 5 (by decide) (by decide) (by decide) _ i hi
    rw [(a 4).2, b 0 5 (by decide) (by decide)]
    rfl
  · apply sha512_round_witness_limb_link v k w 5 3 0 8 (by decide) (by decide) _ i hi
    rw [(a 5).1, o 3]
    rfl
  · apply sha512_round_witness_limb_link v k w 5 4 4 8 (by decide) (by decide) _ i hi
    rw [(a 5).2, o 4]
    rfl
  · apply sha512_round_witness_limb_link v k w 6 3 4 8 (by decide) (by decide) _ i hi
    rw [(a 6).2, o 3]
    rfl

/-- Universal completeness for bounded SHA-512 round inputs. Every component
polynomial and every sixteen-bit connecting wire vanishes. -/
theorem sha512_round_witness_holds (v : Vars) (k w : Nat)
    (bounds : sha512RoundInputBounds v k w) :
    sha512RoundHolds (sha512RoundWitness v k w) := by
  intro e he
  rcases List.mem_append.mp he with he | he
  · obtain ⟨⟨offset, constraints⟩,hc,he⟩ := List.mem_flatMap.mp he
    obtain ⟨inner,hi,rfl⟩ := List.mem_map.mp he
    rw [sha512_relocate_eval]
    simp only [sha512RoundComponents,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with (hc | hc) | hc
    · cases hc
      exact sha512_round_witness_bits_holds v k w 0 (by decide) inner hi
    · cases hc
      exact sha512_round_witness_bits_holds v k w 1 (by decide) inner hi
    · obtain ⟨j,hj,hc⟩ := List.mem_map.mp hc
      cases hc
      exact sha512_round_witness_add_holds v k w j inner hi
  · obtain ⟨wire,hw,he⟩ := List.mem_flatMap.mp he
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp he
    have eq := sha512_round_witness_wires v k w bounds wire hw i (List.mem_range.mp hi)
    change sha512RoundWitness v k w (wire.target+i) +
      -(sha512RoundWireExpr wire i).evalWith (instructionAddEnv (sha512RoundWitness v k w)) = 0
    rw [eq]
    grind

end NearCompression
