import NearCompression.SHA384SharedNodes
import NearCompression.SHA384EndpointMessage
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 NearSpecV3.SHA512
set_option maxRecDepth 65536

def sharedFlatWords (row : Nat → Fp) (base words : Nat) : List Nat :=
  (List.range words).map (fun i => instructionAdd64Word row (base+4*i))

/-- The record's 32 output limbs are exactly the endpoint's eight words. -/
theorem sha384_shared_record_C_limbs (f0 f1 : List (Nat × Nat)) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384SharedAir f0 f1) pub tr) (node : Nat) (hn : node<5) :
    (List.range 32).map (fun j=>tr.cell 2 node (100+j))=sha384EndpointLimbs (tr.cell 1 node) 8 := by
  have eq:=sha384_shared_record_CD f0 f1 pub tr h node hn
  have take:=congrArg (List.take 32) eq
  exact take

/-- Exact complete output-state decoding; no digest truncation is used. -/
theorem sha384_shared_record_C_words (f0 f1 : List (Nat × Nat)) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384SharedAir f0 f1) pub tr) (node : Nat) (hn : node<5) :
    sharedFlatWords (tr.cell 2 node) 100 8=sha384BatchCompression tr node := by
  have eq:=sha384_shared_record_C_limbs f0 f1 pub tr h node hn
  have grouped : (List.range 8).flatMap (fun i=>(List.range 4).map (fun j=>tr.cell 2 node (100+4*i+j)))=
      sha384EndpointLimbs (tr.cell 1 node) 8 := eq
  have limbs:=sha384_endpoint_limb_ext _ _ grouped
  rw [←sha384_shared_endpoint_compression f0 f1 pub tr h node hn]
  unfold sharedFlatWords sha384EndpointOutput
  apply List.map_congr_left
  intro i hi
  have bound:=List.mem_range.mp hi
  simp only [instructionAdd64Word]
  have l0:=limbs i 0 bound (by decide)
  simp only [Nat.add_zero] at l0
  rw [l0,limbs i 1 bound (by decide),limbs i 2 bound (by decide),limbs i 3 bound (by decide)]

/-- The digest representation is exactly the last 48 fields of the record. -/
theorem sha384_shared_record_D_fields (f0 f1 : List (Nat × Nat)) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384SharedAir f0 f1) pub tr) (node : Nat) (hn : node<5) :
    (List.range 48).map (fun j=>tr.cell 2 node (132+j))=
      sha384EndpointDigestMessage.map (fun e=>e.eval tr 1 node pub) := by
  have eq:=sha384_shared_record_CD f0 f1 pub tr h node hn
  exact congrArg (List.drop 32) eq

/-- Generic endpoint digest decoding from the actual shared Add64 constraints. -/
theorem sha384_shared_digest_decode (f0 f1 : List (Nat × Nat)) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384SharedAir f0 f1) pub tr) (r : Nat) (hr : r<tr.height 1)
    (target : List Fp)
    (msg : sha384EndpointDigestMessage.map (fun e=>e.eval tr 1 r pub)=target) :
    ((digestBytes (sha384EndpointOutput (tr.cell 1 r))).take 48).map UInt8.toNat=
      (List.range 48).map (fun j=>(target.getD j 0).toNat) := by
  have add (i : Nat) (hi : i<8) := sha384_shared_add_holds f0 f1 pub tr h r i hr hi
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
theorem sha384_shared_record_D_bytes (f0 f1 : List (Nat × Nat)) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384SharedAir f0 f1) pub tr) (node : Nat) (hn : node<5) :
    ((digestBytes (sharedFlatWords (tr.cell 2 node) 100 8)).take 48).map UInt8.toNat=
      (List.range 48).map (fun j=>(tr.cell 2 node (132+j)).toNat) := by
  have cap:=shared_prefix_capacity (sha384_shared_endpoint_prefix f0 f1 pub tr h)
  have bytes:=sha384_shared_digest_decode f0 f1 pub tr h node (by omega)
    ((List.range 48).map (fun j=>tr.cell 2 node (132+j)))
    (sha384_shared_record_D_fields f0 f1 pub tr h node hn).symm
  rw [sha384_shared_record_C_words f0 f1 pub tr h node hn,
    ←sha384_shared_endpoint_compression f0 f1 pub tr h node hn]
  rw [bytes]
  apply List.map_congr_left
  intro j hj
  simp [List.getD,List.mem_range.mp hj]
/-- The record's complete input state decodes to the same core node. -/
theorem sha384_shared_record_A_words (f0 f1 : List (Nat × Nat)) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384SharedAir f0 f1) pub tr) (node : Nat) (hn : node<5) :
    sharedFlatWords (tr.cell 2 node) 4 8=sha512DecodedState (tr.cell 0 (80*node)) := by
  have core := sha384_shared_core_A f0 f1 pub tr h node hn
  have endpoint := sha384_shared_endpoint_A f0 f1 pub tr h node hn
  have eq := endpoint.trans core
  have grouped : sha384EndpointLimbs (tr.cell 1 node) 0=
      (List.range 8).flatMap (fun i=>(List.range 4).map (fun j=>tr.cell 2 node (4+4*i+j))) := eq
  have limbs := sha384_endpoint_limb_ext _ _ grouped.symm
  have first := sha384_local_round_holds 5 pub tr (sha384_shared_core_local f0 f1 pub tr h)
    (by decide) node 0 hn (by decide)
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

end NearCompression
