import NearCompression.SHA384SharedCallState
import NearCompression.SHA384SharedInputMatch

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 NearSpecV3.SHA512

/-- Deterministic three-block ledger. The semantic compression premise is an
internal composition interface, to be discharged by the shared node decoder. -/
theorem sha384_shared_blocks_chain (f0 f1 : List (Nat × Nat)) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384SharedAir f0 f1) pub tr) (call : Nat) (hc : call<2)
    (decoded : ∀ block,block<3 →
      sharedFlatWords (tr.cell 3 (3*call+block)) 102 8=
        compress (sharedFlatWords (tr.cell 3 (3*call+block)) 6 8)
          (((pad (sha384SharedMessage pub tr call)).drop (128*block)).take 128))
    (k t : Nat) (ht : t+k<3) :
    blocks (k+1) (sharedFlatWords (tr.cell 3 (3*call+t)) 6 8)
        ((pad (sha384SharedMessage pub tr call)).drop (128*t))=
      sharedFlatWords (tr.cell 3 (3*call+(t+k))) 102 8 := by
  have size : (pad (sha384SharedMessage pub tr call)).length=384 := by
    rw [sha384_padding_length,sha384_shared_message_length]
    rfl
  have step (t k : Nat) (ht : t<3) :
      blocks (k+1) (sharedFlatWords (tr.cell 3 (3*call+t)) 6 8)
        ((pad (sha384SharedMessage pub tr call)).drop (128*t))=
      blocks k (sharedFlatWords (tr.cell 3 (3*call+t)) 102 8)
        ((pad (sha384SharedMessage pub tr call)).drop (128*(t+1))) := by
    let rest := (pad (sha384SharedMessage pub tr call)).drop (128*t)
    have len : (rest.take 128).length=128 := by
      simp only [rest,List.length_take,List.length_drop,size]
      omega
    have result := sha512_blocks_cons_exact k (sharedFlatWords (tr.cell 3 (3*call+t)) 6 8)
      (rest.take 128) (rest.drop 128) len
    rw [List.take_append_drop] at result
    dsimp only [rest] at result
    rw [←decoded t ht] at result
    simpa only [List.drop_drop,Nat.mul_add,Nat.mul_one] using result
  induction k generalizing t with
  | zero =>
    rw [step t 0 (by omega)]
    rfl
  | succ k ih =>
    rw [step t (k+1) (by omega),←sha384_shared_call_link_words f0 f1 pub tr h call t hc (by omega)]
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (t+1) (by omega)

end NearCompression
