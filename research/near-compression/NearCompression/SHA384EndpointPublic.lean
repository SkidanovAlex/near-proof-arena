import NearCompression.SHA384EndpointMessage
import NearCompression.SHA384Message

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2

def sha384EndpointPublic (message digest : List UInt8) : List Fp :=
  sha384MessagePublic message digest ++ [1,0,0,0]

theorem sha384_endpoint_public_prefix (message digest : List UInt8) (i : Nat) (hi : i<message.length) :
    (sha384EndpointPublic message digest).getD i 0=
      Fp.ofNat ((message.map UInt8.toNat).getD i 0) := by
  have bound : i<(sha384MessagePublic message digest).length := by simp [sha384MessagePublic];omega
  simp only [sha384EndpointPublic,List.getD_eq_getElem?_getD,List.getElem?_append_left bound]
  exact sha384_message_public_prefix message digest i hi

theorem sha384_endpoint_public_digest_layout (message digest : List UInt8) (size : digest.length=48) :
    (List.range 48).map (fun j=>((sha384EndpointPublic message digest).getD (message.length+j) 0).toNat)=
      digest.map UInt8.toNat := by
  rw [←sha384_message_public_digest message digest size]
  apply List.map_congr_left
  intro j hj
  have bound : message.length+j<(sha384MessagePublic message digest).length := by
    have h:=List.mem_range.mp hj
    simp only [sha384MessagePublic,List.length_map,List.length_append,size]
    omega
  simp only [sha384EndpointPublic,List.getD_eq_getElem?_getD,List.getElem?_append_left bound]

theorem sha384_endpoint_public_count_layout (message digest : List UInt8) (size : digest.length=48)
    (j : Nat) (hj : j<4) :
    (sha384EndpointPublic message digest).getD (message.length+48+j) 0=if j=0 then 1 else 0 := by
  have len : (sha384MessagePublic message digest).length=message.length+48 := by simp [sha384MessagePublic,size]
  simp only [sha384EndpointPublic,List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by rw [len];omega : (sha384MessagePublic message digest).length≤message.length+48+j),
    len,Nat.add_sub_cancel_left]
  have cases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
  rcases cases with rfl|rfl|rfl|rfl <;> rfl

/-- Concrete message,48-byte digest and fixed natural public count. No manual
message-prefix/count binding or standalone routing correctness is assumed. -/
theorem sha384_endpoint_message_sound (message digest : List UInt8) (size : digest.length=48)
    (tr : Trace Fp)
    (holds : HoldsP (sha384EndpointAir message.length) (sha384EndpointPublic message digest) tr)
    (blocks : sha384PaddedLength message.length/128<P) :
    sha384ChainDigest message=digest := by
  have eq:=sha384_endpoint_digest_sound message _ tr holds
    (sha384_endpoint_public_prefix message digest) blocks
    (sha384_endpoint_public_count_layout message digest size)
  rw [sha384_endpoint_public_digest_layout message digest size] at eq
  have injective : ∀ a b : List UInt8,a.map UInt8.toNat=b.map UInt8.toNat → a=b := by
    intro a
    induction a with
    | nil => intro b h;cases b <;> simp_all
    | cons x xs ih =>
      intro b h
      cases b with
      | nil => simp at h
      | cons y ys =>
        obtain ⟨head,tail⟩:=List.cons.inj h
        rw [UInt8.toNat_inj.mp head,ih ys tail]
  exact injective _ _ eq

end NearCompression
