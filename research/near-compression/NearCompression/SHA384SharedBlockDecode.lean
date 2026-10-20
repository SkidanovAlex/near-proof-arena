import NearCompression.SHA384SharedDecode
import NearCompression.SHA384BatchedPayloadIndex
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 NearSpecV3.SHA512

theorem sha384_shared_message_bits (f0 f1 : List (Nat × Nat)) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384SharedAir f0 f1) pub tr) (node word bit : Nat)
    (hn : node<5) (hw : word<16) (hb : bit<64) :
    (tr.cell 0 (80*node) (sha512ScheduleWindowBase word+bit)).toNat≤1 := by
  have pair := sha384_local_pair_holds 5 pub tr (sha384_shared_core_local f0 f1 pub tr h)
    (by decide) node 0 hn (by decide)
  have schedule := sha512_combined_schedule_holds _ _ pub 0 (by decide) rfl pair
  have bits := sha512_window_bit_boolean _ _ pub 0 (by decide) rfl schedule 0 (Nat.two_pow_pos _) word hw bit hb
  simpa only [sha384BatchPairTrace,sha512CombinedProjection,Nat.add_zero,Nat.zero_add] using bits

/-- Ordered record limbs are the actual node's schedule-window limbs. -/
theorem sha384_shared_record_M_limb (f0 f1 : List (Nat × Nat)) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384SharedAir f0 f1) pub tr) (node word limb : Nat)
    (hn : node<5) (hw : word<16) (hl : limb<4) :
    tr.cell 2 node (36+4*word+limb)=
      (instructionBitExpr (sha512ScheduleWindowBase word+16*limb) 16).evalWith
        (instructionAddEnv (tr.cell 0 (80*node))) := by
  have eq := congrArg List.tail (sha384_shared_core_M f0 f1 pub tr h node hn)
  change (List.range 16).flatMap (fun word => (List.range 4).map (fun limb =>
    (instructionBitExpr (sha512ScheduleWindowBase word+16*limb) 16).eval tr 0 (80*node) pub))=
    (List.range 64).map (fun j => tr.cell 2 node (36+j)) at eq
  have atIndex := congrArg (fun xs : List Fp => xs.getD (word*4+limb) 0) eq
  rw [sha384_flat_payload_index 16 4 _ (by intro i;simp) word limb hw hl 0] at atIndex
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map,
    List.getElem?_range (by omega : word*4+limb<64),List.getElem?_range hl,
    Option.map_some,Option.getD_some] at atIndex
  rw [sha512_public_bitexpr_eval] at atIndex
  simpa only [Nat.mul_comm,Nat.add_assoc] using atIndex.symm

/-- All sixteen record words decode to the primitive's actual message block. -/
theorem sha384_shared_record_M_words (f0 f1 : List (Nat × Nat)) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384SharedAir f0 f1) pub tr) (node : Nat) (hn : node<5) :
    sharedFlatWords (tr.cell 2 node) 36 16=words (sha512DecodedBlock (tr.cell 0 (80*node))) := by
  rw [sha512_decoded_block_words]
  unfold sharedFlatWords sha512ScheduleWindow
  apply List.map_congr_left
  intro word hw
  have bound := List.mem_range.mp hw
  let limbs := (List.range 4).map (fun limb => tr.cell 2 node (36+4*word+limb))
  have eq (limb : Nat) (hl : limb<4) : limbs.getD (0+limb) 0=
      (instructionBitExpr (sha512ScheduleWindowBase word+16*limb) 16).evalWith
        (instructionAddEnv (tr.cell 0 (80*node))) := by
    simpa [limbs,List.getD_eq_getElem?_getD,hl] using
      sha384_shared_record_M_limb f0 f1 pub tr h node word limb hn bound hl
  have decoded := (sha512_public_word_decode (tr.cell 0 (80*node)) limbs 0
    (sha512ScheduleWindowBase word)
    (fun bit hb => sha384_shared_message_bits f0 f1 pub tr h node word bit hn bound hb) eq).1
  simpa [sha512PublicWord,limbs,instructionAdd64Word,sha512ScheduleWindowWord,Nat.add_assoc] using decoded
end NearCompression
