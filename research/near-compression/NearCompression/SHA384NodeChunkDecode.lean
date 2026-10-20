import NearCompression.SHA384NodeChunkNodes
import NearCompression.SHA384SharedDecode
import NearCompression.SHA384BatchedPayloadIndex
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 NearSpecV3.SHA512
set_option maxRecDepth 65536

/-- The record's 32 output limbs are exactly the endpoint's eight words. -/
theorem sha384_chunk_record_C_limbs (base count bits uses : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384NodeChunkAir base count bits uses) pub tr) (positive : 0<count) (small : count<P) (node : Nat) (hn : node<count) :
    (List.range 32).map (fun j=>tr.cell 2 node (2+bits+96+j))=sha384EndpointLimbs (tr.cell 1 node) 8 := by
  have eq:=sha384_chunk_record_CD base count bits uses pub tr h positive small node hn
  have take:=congrArg (List.take 32) eq
  exact take

/-- Exact complete output-state decoding; no digest truncation is used. -/
theorem sha384_chunk_record_C_words (base count bits uses : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384NodeChunkAir base count bits uses) pub tr) (positive : 0<count) (small : count<P) (node : Nat) (hn : node<count) :
    sharedFlatWords (tr.cell 2 node) (2+bits+96) 8=sha384BatchCompression tr node := by
  have eq:=sha384_chunk_record_C_limbs base count bits uses pub tr h positive small node hn
  have grouped : (List.range 8).flatMap (fun i=>(List.range 4).map (fun j=>tr.cell 2 node (2+bits+96+4*i+j)))=
      sha384EndpointLimbs (tr.cell 1 node) 8 := eq
  have limbs:=sha384_endpoint_limb_ext _ _ grouped
  rw [←sha384_chunk_endpoint_compression base count bits uses pub tr h positive small node hn]
  unfold sharedFlatWords sha384EndpointOutput
  apply List.map_congr_left
  intro i hi
  have bound:=List.mem_range.mp hi
  simp only [instructionAdd64Word]
  have l0:=limbs i 0 bound (by decide)
  simp only [Nat.add_zero] at l0
  rw [l0,limbs i 1 bound (by decide),limbs i 2 bound (by decide),limbs i 3 bound (by decide)]

/-- The digest representation is exactly the last 48 fields of the record. -/
theorem sha384_chunk_record_D_fields (base count bits uses : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384NodeChunkAir base count bits uses) pub tr) (positive : 0<count) (small : count<P) (node : Nat) (hn : node<count) :
    (List.range 48).map (fun j=>tr.cell 2 node (2+bits+128+j))=
      sha384EndpointDigestMessage.map (fun e=>e.eval tr 1 node pub) := by
  have eq:=sha384_chunk_record_CD base count bits uses pub tr h positive small node hn
  exact congrArg (List.drop 32) eq

/-- Generic endpoint digest decoding from the actual shared Add64 constraints. -/
theorem sha384_chunk_digest_decode (base count bits uses : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384NodeChunkAir base count bits uses) pub tr) (r : Nat) (hr : r<tr.height 1)
    (target : List Fp)
    (msg : sha384EndpointDigestMessage.map (fun e=>e.eval tr 1 r pub)=target) :
    ((digestBytes (sha384EndpointOutput (tr.cell 1 r))).take 48).map UInt8.toNat=
      (List.range 48).map (fun j=>(target.getD j 0).toNat) := by
  have add (i : Nat) (hi : i<8) := sha384_chunk_add_holds base count bits uses pub tr h r i hr hi
  have full : (digestBytes (sha384EndpointOutput (tr.cell 1 r))).map UInt8.toNat=
      (List.range 8).flatMap (fun i => sha512WindowWordBytes (fun c => tr.cell 1 r (208*i+c)) 144) := by
    simp only [digestBytes,sha384EndpointOutput,List.flatMap_map,List.map_flatMap]
    apply congrArg List.flatten
    apply List.map_congr_left
    intro i hi
    have ai := add i (List.mem_range.mp hi)
    rw [sha384_word_bytes,sha512_add_word_bits _ ai 8 (by decide)]
    exact sha512_nat_word_bytes_bits _ 144 (fun bit hb => sha512_add_word_bit _ ai 8 bit (by decide) hb)
  rw [List.map_take,full]
  change (List.range 48).map (fun j => sha512WindowByte (fun c => tr.cell 1 r (208*(j/8)+c)) 144 (7-j%8))=_
  apply List.map_congr_left
  intro j hj
  have jb := List.mem_range.mp hj
  have ai := add (j/8) (by omega)
  have bits (bit : Nat) (hb : bit<64) := sha512_add_word_bit _ ai 8 bit (by decide) hb
  have bounded := sha512_window_byte_bound (fun c => tr.cell 1 r (208*(j/8)+c)) 144 (7-j%8) (by omega) bits
  have field := congrArg (fun xs : List Fp => xs.getD j 0) msg
  simp only [sha384EndpointDigestMessage,List.map_map] at field
  simp [List.getD_eq_getElem?_getD,jb] at field
  rw [sha512_public_bitexpr_eval,sha512_bit_expr_field] at field
  have value := congrArg Fp.toNat field
  rw [Fp.toNat_ofNat] at value
  have small : sha512WindowByte (fun c => tr.cell 1 r (208*(j/8)+c)) 144 (7-j%8)<P := by unfold P;omega
  have value' : sha512WindowByte (fun c => tr.cell 1 r (208*(j/8)+c)) 144 (7-j%8)%P=(target.getD j 0).toNat := by
    simpa only [sha512WindowByte,Nat.add_assoc,List.getD_eq_getElem?_getD] using value
  rwa [Nat.mod_eq_of_lt small] at value'



/-- All record digest fields decode to the SHA-384 truncation of the full C state. -/
theorem sha384_chunk_record_D_bytes (base count bits uses : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384NodeChunkAir base count bits uses) pub tr) (positive : 0<count) (small : count<P) (node : Nat) (hn : node<count) :
    ((digestBytes (sharedFlatWords (tr.cell 2 node) (2+bits+96) 8)).take 48).map UInt8.toNat=
      (List.range 48).map (fun j=>(tr.cell 2 node (2+bits+128+j)).toNat) := by
  have cap:=shared_prefix_capacity (sha384_chunk_endpoint_prefix base count bits uses pub tr h positive small)
  have bytes:=sha384_chunk_digest_decode base count bits uses pub tr h node (by omega)
    ((List.range 48).map (fun j=>tr.cell 2 node (2+bits+128+j)))
    (sha384_chunk_record_D_fields base count bits uses pub tr h positive small node hn).symm
  rw [sha384_chunk_record_C_words base count bits uses pub tr h positive small node hn,
    ←sha384_chunk_endpoint_compression base count bits uses pub tr h positive small node hn]
  rw [bytes]
  apply List.map_congr_left
  intro j hj
  simp [List.getD,List.mem_range.mp hj]
/-- The record's complete input state decodes to the same core node. -/
theorem sha384_chunk_record_A_words (base count bits uses : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384NodeChunkAir base count bits uses) pub tr) (positive : 0<count) (small : count<P) (node : Nat) (hn : node<count) :
    sharedFlatWords (tr.cell 2 node) (2+bits) 8=sha512DecodedState (tr.cell 0 (80*node)) := by
  have core := sha384_chunk_core_A base count bits uses pub tr h positive small node hn
  have endpoint := sha384_chunk_endpoint_A base count bits uses pub tr h positive small node hn
  have eq := endpoint.trans core
  have grouped : sha384EndpointLimbs (tr.cell 1 node) 0=
      (List.range 8).flatMap (fun i=>(List.range 4).map (fun j=>tr.cell 2 node (2+bits+4*i+j))) := eq
  have limbs := sha384_endpoint_limb_ext _ _ grouped.symm
  have first := sha384_local_round_holds count pub tr (sha384_chunk_core_local base count bits uses pub tr h positive)
    small node 0 hn (by decide)
  simp only [Nat.add_zero] at first
  unfold sharedFlatWords sha512DecodedState
  apply List.map_congr_left
  intro i hi
  have bound := List.mem_range.mp hi
  have decoded := sha384_endpoint_word_decode _ _ 0 false first endpoint i bound
  simp only [Bool.false_eq_true,ite_false] at decoded
  rw [sha512_ff_input_words _ first i bound] at decoded
  rw [←decoded]
  simp only [instructionAdd64Word]
  have l0 := limbs i 0 bound (by decide)
  simp only [Nat.add_zero] at l0
  rw [l0,limbs i 1 bound (by decide),limbs i 2 bound (by decide),limbs i 3 bound (by decide)]
  simp only [Nat.add_zero,Nat.zero_add]


theorem sha384_chunk_message_bits (base count bits uses : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384NodeChunkAir base count bits uses) pub tr) (positive : 0<count) (small : count<P) (node word bit : Nat)
    (hn : node<count) (hw : word<16) (hb : bit<64) :
    (tr.cell 0 (80*node) (sha512ScheduleWindowBase word+bit)).toNat≤1 := by
  have pair := sha384_local_pair_holds count pub tr (sha384_chunk_core_local base count bits uses pub tr h positive)
    small node 0 hn (by decide)
  have schedule := sha512_combined_schedule_holds _ _ pub 0 (by decide) rfl pair
  have bits := sha512_window_bit_boolean _ _ pub 0 (by decide) rfl schedule 0 (Nat.two_pow_pos _) word hw bit hb
  simpa only [sha384BatchPairTrace,sha512CombinedProjection,Nat.add_zero,Nat.zero_add] using bits

/-- Ordered record limbs are the actual node's schedule-window limbs. -/
theorem sha384_chunk_record_M_limb (base count bits uses : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384NodeChunkAir base count bits uses) pub tr) (positive : 0<count) (small : count<P) (node word limb : Nat)
    (hn : node<count) (hw : word<16) (hl : limb<4) :
    tr.cell 2 node (2+bits+32+4*word+limb)=
      (instructionBitExpr (sha512ScheduleWindowBase word+16*limb) 16).evalWith
        (instructionAddEnv (tr.cell 0 (80*node))) := by
  have eq := congrArg List.tail (sha384_chunk_core_M base count bits uses pub tr h positive small node hn)
  change (List.range 16).flatMap (fun word => (List.range 4).map (fun limb =>
    (instructionBitExpr (sha512ScheduleWindowBase word+16*limb) 16).eval tr 0 (80*node) pub))=
    (List.range 64).map (fun j => tr.cell 2 node (2+bits+32+j)) at eq
  have atIndex := congrArg (fun xs : List Fp => xs.getD (word*4+limb) 0) eq
  rw [sha384_flat_payload_index 16 4 _ (by intro i;simp) word limb hw hl 0] at atIndex
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map,
    List.getElem?_range (by omega : word*4+limb<64),List.getElem?_range hl,
    Option.map_some,Option.getD_some] at atIndex
  rw [sha512_public_bitexpr_eval] at atIndex
  simpa only [Nat.mul_comm,Nat.add_assoc] using atIndex.symm

/-- All sixteen record words decode to the primitive's actual message block. -/
theorem sha384_chunk_record_M_words (base count bits uses : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384NodeChunkAir base count bits uses) pub tr) (positive : 0<count) (small : count<P) (node : Nat) (hn : node<count) :
    sharedFlatWords (tr.cell 2 node) (2+bits+32) 16=words (sha512DecodedBlock (tr.cell 0 (80*node))) := by
  rw [sha512_decoded_block_words]
  unfold sharedFlatWords sha512ScheduleWindow
  apply List.map_congr_left
  intro word hw
  have bound := List.mem_range.mp hw
  let limbs := (List.range 4).map (fun limb => tr.cell 2 node (2+bits+32+4*word+limb))
  have eq (limb : Nat) (hl : limb<4) : limbs.getD (0+limb) 0=
      (instructionBitExpr (sha512ScheduleWindowBase word+16*limb) 16).evalWith
        (instructionAddEnv (tr.cell 0 (80*node))) := by
    simpa [limbs,List.getD_eq_getElem?_getD,hl] using
      sha384_chunk_record_M_limb base count bits uses pub tr h positive small node word limb hn bound hl
  have decoded := (sha512_public_word_decode (tr.cell 0 (80*node)) limbs 0
    (sha512ScheduleWindowBase word)
    (fun bit hb => sha384_chunk_message_bits base count bits uses pub tr h positive small node word bit hn bound hb) eq).1
  simpa [sha512PublicWord,limbs,instructionAdd64Word,sha512ScheduleWindowWord,Nat.add_assoc] using decoded

end NearCompression
