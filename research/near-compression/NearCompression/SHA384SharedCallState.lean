import NearCompression.SHA384SharedCallRecords
import NearCompression.SHA384SharedCalls
import NearCompression.SHA384Chain

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 NearSpecV3.SHA512

/-- Full eight-word IV is fixed by the actual call phase-zero constraints. -/
theorem sha384_shared_call_initial_words (f0 f1 : List (Nat × Nat)) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384SharedAir f0 f1) pub tr) (call : Nat) (hc : call<2) :
    sharedFlatWords (tr.cell 3 (3*call)) 6 8=sha384ChainIV := by
  have cells := sha384_call_initial f0 f1 pub tr h call
  have transfer := shared_flat_words_transfer (tr.cell 3 (3*call))
    (fun j => Fp.ofNat (sha384BatchIVPayload[j]!)) 6 0 8
    (by intro j hj; simpa using cells j hc hj)
  rw [transfer]
  decide

/-- Consecutive call blocks transfer all 512 state bits, including hidden digest words. -/
theorem sha384_shared_call_link_words (f0 f1 : List (Nat × Nat)) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384SharedAir f0 f1) pub tr) (call block : Nat) (hc : call<2) (hb : block<2) :
    sharedFlatWords (tr.cell 3 (3*call+(block+1))) 6 8=
      sharedFlatWords (tr.cell 3 (3*call+block)) 102 8 := by
  apply shared_flat_words_transfer
  intro j hj
  exact sha384_call_state_link f0 f1 pub tr h call block j hc hb hj

/-- Final digest bytes are bound to the selected call's public slice. -/
theorem sha384_shared_call_final_words (f0 f1 : List (Nat × Nat)) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384SharedAir f0 f1) pub tr) (call : Nat) (hc : call<2) :
    ((digestBytes (sharedFlatWords (tr.cell 3 (3*call+2)) 102 8)).take 48).map UInt8.toNat=
      (List.range 48).map (fun j => (pub.getD (48*call+j) 0).toNat) := by
  have metadata := sha384_call_segment_metadata f0 f1 pub tr h call 2 hc (by decide)
  obtain ⟨node,hn,tag,state,bytes⟩ := sha384_shared_call_output f0 f1 pub tr h _ metadata.1 metadata.2.1
  rw [bytes]
  apply List.map_congr_left
  intro j hj
  rw [sha384_call_final_byte f0 f1 pub tr h call j hc (List.mem_range.mp hj)]

end NearCompression
