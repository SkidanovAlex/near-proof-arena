import NearCompression.SHA384MultiBlockSemantics

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra

def sha384MessagePublic (message digest : List UInt8) : List Fp :=
  (message++digest).map (fun b=>Fp.ofNat b.toNat)

private theorem byte_field_decode (b : UInt8) : (Fp.ofNat b.toNat).toNat=b.toNat := by
  rw [Fp.toNat_ofNat,Nat.mod_eq_of_lt]
  have bound:=b.toNat_lt
  unfold P
  omega

theorem sha384_message_public_prefix (message digest : List UInt8) (i : Nat) (hi : i<message.length) :
    (sha384MessagePublic message digest).getD i 0=
      Fp.ofNat ((message.map UInt8.toNat).getD i 0) := by
  simp only [sha384MessagePublic,List.getD_eq_getElem?_getD,List.getElem?_map,
    List.getElem?_append_left hi,List.getElem?_eq_getElem hi,Option.map_some,Option.getD_some]

theorem sha384_message_public_digest (message digest : List UInt8) (size : digest.length=48) :
    (List.range 48).map (fun j=>((sha384MessagePublic message digest).getD (message.length+j) 0).toNat)=
      digest.map UInt8.toNat := by
  apply List.ext_getElem
  · simp [size]
  · intro i hi hi'
    have bound : i<digest.length := by simpa using hi'
    simp only [List.getElem_map,List.getElem_range]
    simp only [sha384MessagePublic,List.getD_eq_getElem?_getD,List.getElem?_map,
      List.getElem?_append_right (by omega : message.length≤message.length+i),
      Nat.add_sub_cancel_left,List.getElem?_eq_getElem bound,Option.map_some,Option.getD_some]
    exact byte_field_decode _

/-- Concrete public message||digest layout: no separately assumed public-byte
binding or hash/compression correctness premise. Cryptographic acceptance still
needs its separate implication to actual HoldsP. -/
theorem sha384_message_sound (message digest : List UInt8) (size : digest.length=48)
    (tr : Trace Fp)
    (holds : ZkFormal.V2.HoldsP (sha384MultiBlockAir message.length)
      (sha384MessagePublic message digest) tr)
    (blocks : sha384PaddedLength message.length/128<P) :
    sha384ChainDigest message=digest := by
  have eq:=sha384_multiblock_digest_sound message _ tr holds
    (sha384_message_public_prefix message digest) blocks
  rw [sha384_message_public_digest message digest size] at eq
  have injective : ∀ a b : List UInt8,a.map UInt8.toNat=b.map UInt8.toNat → a=b := by
    intro a
    induction a with
    | nil => intro b h; cases b <;> simp_all
    | cons x xs ih =>
      intro b h
      cases b with
      | nil => simp at h
      | cons y ys =>
        obtain ⟨head,tail⟩:=List.cons.inj h
        rw [UInt8.toNat_inj.mp head,ih ys tail]
  exact injective _ _ eq

end NearCompression
