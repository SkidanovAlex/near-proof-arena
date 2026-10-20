import NearCompression.SHA384SharedChain
import NearCompression.SHA384SharedPaddedBlock

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 NearSpecV3.SHA512

/-- Actual shared AIR yields each call's standard compression step. No caller
matching, state-link, padding, or compression premise is used. -/
theorem sha384_shared_call_compression (f0 f1 : List (Nat × Nat)) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384SharedAir f0 f1) pub tr) (call block : Nat) (hc : call<2) (hb : block<3) :
    sharedFlatWords (tr.cell 3 (3*call+block)) 102 8=
      compress (sharedFlatWords (tr.cell 3 (3*call+block)) 6 8)
        (((pad (sha384SharedMessage pub tr call)).drop (128*block)).take 128) := by
  have metadata := sha384_call_segment_metadata f0 f1 pub tr h call block hc hb
  obtain ⟨node,hn,tag,a,m,c,d⟩ := sha384_shared_call_word_vectors f0 f1 pub tr h _ metadata.1 metadata.2.1
  rw [c,sha384_shared_record_C_words f0 f1 pub tr h node hn,
    a,sha384_shared_record_A_words f0 f1 pub tr h node hn]
  unfold sha384BatchCompression
  rw [sha384_shared_padded_block f0 f1 pub tr h call block node hc hb hn tag]

/-- All three actual routed blocks compose from the fixed full SHA-384 IV. -/
theorem sha384_shared_final_state (f0 f1 : List (Nat × Nat)) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384SharedAir f0 f1) pub tr) (call : Nat) (hc : call<2) :
    blocks 3 sha384ChainIV (pad (sha384SharedMessage pub tr call))=
      sharedFlatWords (tr.cell 3 (3*call+2)) 102 8 := by
  have chain := sha384_shared_blocks_chain f0 f1 pub tr h call hc
    (sha384_shared_call_compression f0 f1 pub tr h call · hc) 2 0 (by decide)
  simp only [Nat.add_zero,Nat.zero_add,Nat.mul_zero,List.drop_zero] at chain
  rw [sha384_shared_call_initial_words f0 f1 pub tr h call hc] at chain
  exact chain

/-- Byte conversion is exact, derived from the actual committed input bits. -/
theorem sha384_shared_message_roundtrip (f0 f1 : List (Nat × Nat)) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384SharedAir f0 f1) pub tr) (call : Nat) (hc : call<2) :
    ((sha384SharedMessage pub tr call).map UInt8.ofNat).map UInt8.toNat=
      sha384SharedMessage pub tr call := by
  rw [List.map_map]
  apply Eq.trans (b := (sha384SharedMessage pub tr call).map id) _ (List.map_id _)
  apply List.map_congr_left
  intro byte hb
  obtain ⟨i,hi,eq⟩ := List.getElem_of_mem hb
  subst byte
  have bound := sha384_shared_message_byte_bound f0 f1 pub tr h call i hc
    (by rw [sha384_shared_message_length] at hi;exact hi)
  simp only [Function.comp_apply]
  apply Nat.mod_eq_of_lt
  simpa [List.getD,hi] using bound

/-- Component soundness: each call's actual decoded committed input hashes to
its public digest slice under standard SHA-384. This theorem starts from exact
AIR HoldsP; it makes no cryptographic proof-system or root-binding claim. -/
theorem sha384_shared_message_sound (f0 f1 : List (Nat × Nat)) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384SharedAir f0 f1) pub tr) (call : Nat) (hc : call<2) :
    (sha384ChainDigest ((sha384SharedMessage pub tr call).map UInt8.ofNat)).map UInt8.toNat=
      (List.range 48).map (fun j => (pub.getD (48*call+j) 0).toNat) := by
  unfold sha384ChainDigest
  rw [sha384_shared_message_roundtrip f0 f1 pub tr h call hc]
  have len : (pad (sha384SharedMessage pub tr call)).length=384 := by
    rw [sha384_padding_length,sha384_shared_message_length]
    rfl
  dsimp only
  rw [len]
  change ((digestBytes (blocks 3 sha384ChainIV (pad (sha384SharedMessage pub tr call)))).take 48).map UInt8.toNat=_
  rw [sha384_shared_final_state f0 f1 pub tr h call hc]
  exact sha384_shared_call_final_words f0 f1 pub tr h call hc

end NearCompression
