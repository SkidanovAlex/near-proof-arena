import NearCompression.SHA384PairedByteDecode
import NearCompression.SHA384SharedInputMatch
import NearCompression.SHA384SharedCallRecords
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 NearSpecV3.SHA512

theorem sha384_shared_padded_byte_bound (f0 f1 : List (Nat × Nat)) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384SharedAir f0 f1) pub tr) (call i : Nat) (hc : call<2) (hi : i<384) :
    (pad (sha384SharedMessage pub tr call)).getD i 0<256 := by
  rw [sha384_padding_byte _ i (by rw [sha384_shared_message_length];exact hi),sha384_shared_message_length]
  split
  · exact sha384_shared_message_byte_bound f0 f1 pub tr h call i hc ‹i<267›
  · split
    · decide
    · split
      · exact Nat.mod_lt _ (by decide)
      · decide

/-- Actual call matching and canonical input limbs fix the complete node block. -/
theorem sha384_shared_padded_block (f0 f1 : List (Nat × Nat)) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384SharedAir f0 f1) pub tr) (call block node : Nat)
    (hc : call<2) (hb : block<3) (hn : node<5)
    (tag : tr.cell 3 (3*call+block) 1=Fp.ofNat node) :
    sha512DecodedBlock (tr.cell 0 (80*node))=
      ((pad (sha384SharedMessage pub tr call)).drop (128*block)).take 128 := by
  have metadata := sha384_call_segment_metadata f0 f1 pub tr h call block hc hb
  obtain ⟨other,ho,otag,cells⟩ := sha384_shared_call_record_cells f0 f1 pub tr h
    (3*call+block) metadata.1 metadata.2.1
  have same := sha384_shared_node_tag_unique _ tr other node ho hn otag tag
  subst other
  have payload := sha384_shared_call_padded_limbs f0 f1 pub tr h call block hc hb
  have limb (word l : Nat) (hw : word<16) (hl : l<4) :
      (instructionBitExpr (sha512ScheduleWindowBase word+16*l) 16).evalWith
        (instructionAddEnv (tr.cell 0 (80*node)))=
      Fp.ofNat (256*(pad (sha384SharedMessage pub tr call)).getD (128*block+(8*word+6-2*l)) 0+
        (pad (sha384SharedMessage pub tr call)).getD (128*block+(8*word+7-2*l)) 0) := by
    have atIndex := congrArg (fun xs : List Fp => xs.getD (word*4+l) 0) payload
    rw [sha384_flat_payload_index 16 4 _ (by intro i;simp) word l hw hl 0] at atIndex
    simp only [List.getD_eq_getElem?_getD,List.getElem?_map,
      List.getElem?_range (by omega : word*4+l<64),List.getElem?_range hl,
      Option.map_some,Option.getD_some] at atIndex
    have cell := cells (32+4*word+l) (by omega)
    have record := sha384_shared_record_M_limb f0 f1 pub tr h node word l hn hw hl
    have c : tr.cell 3 (3*call+block) (38+(word*4+l))=tr.cell 2 node (36+4*word+l) := by
      simpa only [Nat.mul_comm,←Nat.add_assoc] using cell
    rw [c,record] at atIndex
    have high : 128*block+8*word+6-2*l=128*block+(8*word+6-2*l) := by omega
    have low : 128*block+8*word+7-2*l=128*block+(8*word+7-2*l) := by omega
    simpa only [high,low,List.getD_eq_getElem?_getD] using atIndex
  have decoded := sha384_paired_decoded_block (tr.cell 0 (80*node))
    (fun j => (pad (sha384SharedMessage pub tr call)).getD (128*block+j) 0)
    (fun j hj => sha384_shared_padded_byte_bound f0 f1 pub tr h call (128*block+j) hc (by omega))
    (fun word bit hw hi => sha384_shared_message_bits f0 f1 pub tr h node word bit hn hw hi) limb
  rw [decoded]
  have length : (pad (sha384SharedMessage pub tr call)).length=384 := by
    rw [sha384_padding_length,sha384_shared_message_length];rfl
  apply List.ext_getElem
  · simp only [List.length_map,List.length_range,List.length_take,List.length_drop,length]
    omega
  · intro j hj hj'
    have jb : j<128 := by simpa using hj
    have pos : j+128*block<(pad (sha384SharedMessage pub tr call)).length := by omega
    simp [List.getD_eq_getElem?_getD,Nat.add_comm,List.getElem?_eq_getElem pos]
end NearCompression
