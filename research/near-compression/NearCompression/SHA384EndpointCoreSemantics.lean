import NearCompression.SHA384EndpointSplit
import NearCompression.SHA384Padding
import NearCompression.SHA384MultiBlockSemantics

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 NearSpecV3.SHA512
set_option maxRecDepth 65536

theorem sha384_endpoint_core_table (n t : Nat) (ht : t<sha384PaddedLength n/128) :
    (sha384EndpointAir n).tables[t]'(by simp [sha384EndpointAir] <;> omega)=sha384EndpointCoreTable n t := by
  simp [sha384EndpointAir,List.getElem_append_left,ht]

theorem sha384_endpoint_core_constants (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384EndpointAir n) pub tr) (t : Nat) (ht : t<sha384PaddedLength n/128) :
    Holds ⟨[sha512ConstantsTable],0,0⟩ pub (sha512CombinedProjection tr t 0) :=
  sha384_endpoint_core_holds _ tr pub t (by simp [sha384EndpointAir] <;> omega) n t
    (sha384_endpoint_core_table n t ht) h

theorem sha384_endpoint_core_height_phase (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384EndpointAir n) pub tr) (t : Nat) (ht : t<sha384PaddedLength n/128) :
    tr.height t=128 ∧ ∀ r,r<tr.height t → tr.cell t r 5231=if r=79 then 1 else 0 := by
  have core := sha384_endpoint_core_constants n pub tr h t ht
  refine ⟨sha512_constants_height _ _ pub 0 (by decide) rfl core,?_⟩
  intro r hr
  have phase := sha512_constants_phase _ _ pub 0 (by decide) rfl core r hr 79 (by decide)
  simpa only [sha512CombinedProjection,Nat.zero_add,eq_comm] using phase

theorem sha384_endpoint_core_round_holds (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384EndpointAir n) pub tr) (t : Nat) (ht : t<sha384PaddedLength n/128)
    (r : Nat) (hr : r<tr.height t) : sha512RoundHolds (sha512CombinedRoundRow (tr.cell t r)) := by
  have core := sha384_endpoint_core_constants n pub tr h t ht
  have combined := sha512_constants_combined_holds _ _ pub 0 (by decide) rfl core
  have rounds := sha512_combined_round_holds _ _ pub 0 (by decide) rfl combined
  have row := sha512_sequence_row_holds _ _ pub 0 (by decide) rfl rounds r hr
  change sha512RoundHolds (fun col => tr.cell t r (2544+col))
  simpa only [sha512CombinedProjection,Nat.zero_add] using row

/-- Both input/output state bit ranges come directly from existing round gadgets. -/
theorem sha384_endpoint_state_bits (row : Nat → Fp) (h : sha512RoundHolds (sha512CombinedRoundRow row))
    (output : Bool) (i bit : Nat) (hi : i<8) (hb : bit<64) :
    (row ((if output then sha512FeedForwardResultBase i else sha512FeedForwardInputBase i)+bit)).toNat≤1 := by
  have g0 := sha512_round_bits_holds _ h 0 (by decide)
  have g1 := sha512_round_bits_holds _ h 1 (by decide)
  have a := sha512_bits_input_boolean _ g0 bit (by omega)
  have b := sha512_bits_input_boolean _ g0 (64+bit) (by omega)
  have c := sha512_bits_input_boolean _ g0 (128+bit) (by omega)
  have e := sha512_bits_input_boolean _ g1 bit (by omega)
  have f := sha512_bits_input_boolean _ g1 (64+bit) (by omega)
  have g := sha512_bits_input_boolean _ g1 (128+bit) (by omega)
  have d := sha512_add_word_bit _ (sha512_round_add_holds _ h 6 (by decide)) 0 bit (by decide) hb
  have hh := sha512_add_word_bit _ (sha512_round_add_holds _ h 0 (by decide)) 0 bit (by decide) hb
  have oa := sha512_add_word_bit _ (sha512_round_add_holds _ h 5 (by decide)) 8 bit (by decide) hb
  have oe := sha512_add_word_bit _ (sha512_round_add_holds _ h 6 (by decide)) 8 bit (by decide) hb
  have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 := by omega
  cases output <;> rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [Bool.false_eq_true,ite_false,ite_true,sha512FeedForwardResultBase,sha512FeedForwardInputBase,
    sha512RoundBitsRow,sha512RoundAddRow,sha512RoundAddBase,sha512CombinedRoundRow,
    ←Nat.add_assoc,Nat.reduceMul,Nat.reduceAdd,Nat.zero_add] at a b c d e f g hh oa oe ⊢
  all_goals first | exact a | exact b | exact c | exact d | exact e | exact f | exact g | exact hh | exact oa | exact oe

theorem sha384_split_byte_field (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384EndpointAir n) pub tr) (t : Nat)
    (ht : t<sha384PaddedLength n/128) (j : Nat) (hj : j<128) :
    (instructionBitExpr (sha512ScheduleWindowBase (j/8)+8*(7-j%8)) 8).eval tr t 0 pub=
      (sha384PaddedByte n (t*128+j)).eval tr t 0 pub := by
  have hc := h.constr t (by simp [sha384EndpointAir] <;> omega) 0 (Nat.two_pow_pos _) (sha384BlockByteConstraint n t j)
  rw [sha384_endpoint_core_table n t ht] at hc
  have hv := hc (List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨j,List.mem_range.mpr hj,rfl⟩)))
  change (1:Fp)*((instructionBitExpr (sha512ScheduleWindowBase (j/8)+8*(7-j%8)) 8).eval tr t 0 pub+
    -(sha384PaddedByte n (t*128+j)).eval tr t 0 pub)=0 at hv
  grind

theorem sha384_split_iv_field (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384EndpointAir n) pub tr) (i limb : Nat) (hi : i<8) (hl : limb<4) :
    (instructionBitExpr (sha512FeedForwardInputBase i+16*limb) 16).eval tr 0 0 pub=
      Fp.ofNat ((sha384ChainIV.getD i 0)/65536^limb%65536) := by
  have ht : 0<sha384PaddedLength n/128 := by unfold sha384PaddedLength;omega
  have hc := h.constr 0 (by simp [sha384EndpointAir] <;> omega) 0 (Nat.two_pow_pos _) (sha384IVConstraint i limb)
  rw [sha384_endpoint_core_table n 0 ht] at hc
  have hv := hc (List.mem_append_right _ (by
    simp only [sha384EndpointCoreTable,ite_true]
    exact List.mem_flatMap.mpr ⟨i,List.mem_range.mpr hi,List.mem_map.mpr ⟨limb,List.mem_range.mpr hl,rfl⟩⟩))
  change (1:Fp)*((instructionBitExpr (sha512FeedForwardInputBase i+16*limb) 16).eval tr 0 0 pub+
    -Fp.ofNat ((sha384ChainIV.getD i 0)/65536^limb%65536))=0 at hv
  grind

theorem sha384_split_message_bits (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384EndpointAir n) pub tr) (t : Nat)
    (ht : t<sha384PaddedLength n/128) (i bit : Nat) (hi : i<16) (hb : bit<64) :
    (tr.cell t 0 (sha512ScheduleWindowBase i+bit)).toNat≤1 := by
  have core := sha384_endpoint_core_constants n pub tr h t ht
  have combined := sha512_constants_combined_holds _ _ pub 0 (by decide) rfl core
  have schedule := sha512_combined_schedule_holds _ _ pub 0 (by decide) rfl combined
  have bits := sha512_window_bit_boolean _ _ pub 0 (by decide) rfl schedule 0 (Nat.two_pow_pos _) i hi bit hb
  simpa only [sha512CombinedProjection,Nat.zero_add] using bits

theorem sha384_split_state_bits (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384EndpointAir n) pub tr) (t : Nat)
    (ht : t<sha384PaddedLength n/128) (i bit : Nat) (hi : i<8) (hb : bit<64) :
    (tr.cell t 0 (sha512FeedForwardInputBase i+bit)).toNat≤1 :=
  sha384_endpoint_state_bits _ (sha384_endpoint_core_round_holds n pub tr h t ht 0 (Nat.two_pow_pos _)) false i bit hi hb

theorem sha384_split_byte_nat (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384EndpointAir n) pub tr) (t : Nat)
    (ht : t<sha384PaddedLength n/128) (j : Nat) (hj : j<128) :
    sha512WindowByte (tr.cell t 0) (sha512ScheduleWindowBase (j/8)) (7-j%8)=
      ((sha384PaddedByte n (t*128+j)).eval tr t 0 pub).toNat := by
  have field := sha384_split_byte_field n pub tr h t ht j hj
  rw [sha512_public_bitexpr_eval,sha512_bit_expr_field] at field
  have bound := sha512_window_byte_bound (tr.cell t 0) (sha512ScheduleWindowBase (j/8)) (7-j%8)
    (by omega) (fun bit hb => sha384_split_message_bits n pub tr h t ht (j/8) bit (by omega) hb)
  have small : sha512WindowByte (tr.cell t 0) (sha512ScheduleWindowBase (j/8)) (7-j%8)<P := by
    unfold P
    omega
  have value := congrArg Fp.toNat field
  rw [Fp.toNat_ofNat] at value
  change sha512WindowByte (tr.cell t 0) (sha512ScheduleWindowBase (j/8)) (7-j%8)%P=_ at value
  rwa [Nat.mod_eq_of_lt small] at value

private def sha384IVLimbs (i : Nat) : List Fp :=
  (List.range 4).map (fun limb => Fp.ofNat ((sha384ChainIV.getD i 0)/65536^limb%65536))

theorem sha384_split_initial (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384EndpointAir n) pub tr) :
    sha512DecodedState (tr.cell 0 0)=sha384ChainIV := by
  have ht : 0<sha384PaddedLength n/128 := by unfold sha384PaddedLength; omega
  have word (i : Nat) (hi : i<8) :
      sha512FeedForwardVarsWord (sha512CombinedVars (tr.cell 0 0)) i=sha384ChainIV.getD i 0 := by
    have field (limb : Nat) (hl : limb<4) : (sha384IVLimbs i).getD limb 0=
        (instructionBitExpr (sha512FeedForwardInputBase i+16*limb) 16).evalWith (instructionAddEnv (tr.cell 0 0)) := by
      have eq := sha384_split_iv_field n pub tr h i limb hi hl
      rw [sha512_public_bitexpr_eval] at eq
      rw [eq]
      simp [sha384IVLimbs,List.getD_eq_getElem?_getD,hl]
    have decoded := (sha512_public_word_decode (tr.cell 0 0) (sha384IVLimbs i) 0
      (sha512FeedForwardInputBase i)
      (fun bit hb => sha384_split_state_bits n pub tr h 0 ht i bit hi hb)
      (by simpa only [Nat.zero_add] using field)).1
    have round' := sha384_endpoint_core_round_holds n pub tr h 0 ht 0 (Nat.two_pow_pos _)
    rw [sha512_ff_input_words _ round' i hi] at decoded
    rw [←decoded]
    have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  calc
    sha512DecodedState (tr.cell 0 0)=(List.range 8).map (fun i => sha384ChainIV.getD i 0) := by
      apply List.map_congr_left
      intro i hi
      exact word i (List.mem_range.mp hi)
    _ = sha384ChainIV := rfl

private theorem padded_byte_bound (message : List UInt8) (i : Nat)
    (hi : i<(pad (message.map UInt8.toNat)).length) :
    (pad (message.map UInt8.toNat)).getD i 0<256 := by
  have member (v : Nat) (hv : v ∈ pad (message.map UInt8.toNat)) : v<256 := by
    simp only [pad,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,List.mem_replicate] at hv
    rcases hv with ((hv | hv) | hv) | hv
    · obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hv
      exact x.toNat_lt
    · subst v; decide
    · rcases hv with ⟨_,rfl⟩; decide
    · obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hv
      exact x.toNat_lt
  have value := member _ (List.getElem_mem hi)
  simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem,hi] using value

theorem sha384_split_padded_block (message : List UInt8) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384EndpointAir message.length) pub tr)
    (pubBound : ∀ i,i<message.length → pub.getD i 0=Fp.ofNat ((message.map UInt8.toNat).getD i 0))
    (t : Nat) (ht : t<sha384PaddedLength message.length/128) :
    sha512DecodedBlock (tr.cell t 0)=((pad (message.map UInt8.toNat)).drop (128*t)).take 128 := by
  have size := sha384_padding_length (message.map UInt8.toNat)
  simp only [List.length_map] at size
  rw [sha384_multiblock_decoded_block_shape]
  apply List.ext_getElem
  · simp only [List.length_map,List.length_range,List.length_take,List.length_drop,size]
    unfold sha384PaddedLength at ht ⊢
    omega
  · intro j hj hj'
    have jbound : j<128 := by simpa using hj
    have pos : 128*t+j<sha384PaddedLength message.length := by
      unfold sha384PaddedLength at ht ⊢
      omega
    have actual := sha384_split_byte_nat message.length pub tr h t ht j jbound
    have padded := sha384_padding_expr (message.map UInt8.toNat) tr t 0 pub
      (by simpa using pubBound) (128*t+j) (by simpa using pos)
    simp only [List.length_map] at padded
    rw [Nat.mul_comm t 128,padded,Fp.toNat_ofNat] at actual
    have bounded := padded_byte_bound message (128*t+j) (by omega)
    have small : (pad (message.map UInt8.toNat)).getD (128*t+j) 0<P := by unfold P;omega
    rw [Nat.mod_eq_of_lt small] at actual
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (by omega),Option.getD_some] at actual
    simpa [Nat.add_comm] using actual

def sha384CoreCompression (tr : Trace Fp) (t : Nat) : List Nat :=
  compress (sha512DecodedState (tr.cell t 0)) (sha512DecodedBlock (tr.cell t 0))

theorem sha384_split_compression (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384EndpointAir n) pub tr) (t : Nat) (ht : t<sha384PaddedLength n/128) :
    sha384CoreCompression tr t=(List.range 8).map (fun i =>
      add64 (sha512FeedForwardVarsWord (sha512CombinedVars (tr.cell t 0)) i)
        (sha512FeedForwardVarsWord (sha512CombinedOutput (tr.cell t 79)) i)) := by
  unfold sha384CoreCompression sha512DecodedState
  rw [sha512_compress_vars,sha512_decoded_block_words]
  have rounds := sha384_endpoint_core_rounds _ tr pub t (by simp [sha384EndpointAir] <;> omega)
    n t (sha384_endpoint_core_table n t ht) h
  dsimp only [sha512CombinedWindow] at rounds
  rw [rounds]

end NearCompression
