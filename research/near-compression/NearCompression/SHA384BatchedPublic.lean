import NearCompression.SHA384BatchedCore
import NearCompression.SHA384Message

namespace NearCompression
open ZkFormal.Algebra NearSpecV3.SHA512

/-- Exact deterministic public expansion used by the experimental batched
profile. These values are derived from message bytes, not arbitrary witnesses. -/
def sha384BatchPayload (message : List UInt8) : List Nat :=
  let padded := pad (message.map UInt8.toNat)
  (List.range (sha384PaddedLength message.length/128)).flatMap fun b =>
    (List.range 16).flatMap fun i => (List.range 4).map fun j =>
      256*padded.getD (128*b+8*i+6-2*j) 0+padded.getD (128*b+8*i+7-2*j) 0

def sha384BatchIVPayload : List Nat :=
  (List.range 8).flatMap fun i => (List.range 4).map fun j =>
    (sha384ChainIV.getD i 0 /65536^j)%65536

def sha384BatchCountBytes (count : Nat) : List Nat :=
  (List.range 4).map fun j => count/256^j%256

def sha384BatchedPublicNat (message digest : List UInt8) : List Nat :=
  (message++digest).map UInt8.toNat ++ [1,0,0,0] ++ sha384BatchPayload message ++
    sha384BatchCountBytes (sha384PaddedLength message.length/128) ++
    sha384BatchIVPayload ++ [1,0,0,0]

def sha384BatchedPublic (message digest : List UInt8) : List Fp :=
  (sha384BatchedPublicNat message digest).map Fp.ofNat

private theorem flat_range_length {α : Type} (n width : Nat) (f : Nat → List α)
    (shape : ∀ i,(f i).length=width) :
    ((List.range n).flatMap f).length=n*width := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ,List.flatMap_append,ih,shape,Nat.succ_mul]

theorem sha384_batch_payload_length (message : List UInt8) :
    (sha384BatchPayload message).length=(sha384PaddedLength message.length/128)*64 := by
  unfold sha384BatchPayload
  apply flat_range_length
  intro b
  have h := flat_range_length 16 4
    (fun i => (List.range 4).map (fun j =>
      256*(pad (message.map UInt8.toNat)).getD (128*b+8*i+6-2*j) 0+
      (pad (message.map UInt8.toNat)).getD (128*b+8*i+7-2*j) 0))
    (by intro i;simp)
  exact h

theorem sha384_batch_iv_payload_length : sha384BatchIVPayload.length=32 := by
  unfold sha384BatchIVPayload
  exact flat_range_length 8 4 _ (by intro i;simp)

theorem sha384_batch_count_bytes_length (count : Nat) :
    (sha384BatchCountBytes count).length=4 := by simp [sha384BatchCountBytes]

theorem sha384_batched_public_length (message digest : List UInt8) (size : digest.length=48) :
    (sha384BatchedPublic message digest).length=
      message.length+92+64*(sha384PaddedLength message.length/128) := by
  simp only [sha384BatchedPublic,sha384BatchedPublicNat,List.length_map,List.length_append,
    sha384_batch_payload_length,sha384_batch_count_bytes_length,sha384_batch_iv_payload_length,size]
  simp only [List.length_cons,List.length_nil]
  omega

/-- The original message and claimed digest remain the exact public prefix. -/
theorem sha384_batched_public_prefix (message digest : List UInt8) :
    (sha384BatchedPublic message digest).take (message.length+digest.length)=
      sha384MessagePublic message digest := by
  unfold sha384BatchedPublic sha384BatchedPublicNat
  rw [List.map_append,List.map_append,List.map_append,List.map_append,List.map_append]
  rw [List.append_assoc,List.append_assoc,List.append_assoc,List.append_assoc]
  have len : ((message++digest).map UInt8.toNat |>.map Fp.ofNat).length=
      message.length+digest.length := by simp
  rw [←len,List.take_left]
  simp [sha384MessagePublic,List.map_map,Function.comp_def]

end NearCompression
