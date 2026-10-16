import NearCompression.SHA384DirectSoundness

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2

/-- Claimed digest bytes. Acceptance below checks exact field reconstruction,
so reducing a nonbyte field to UInt8 cannot silently accept an alias. -/
def sha384DirectPublicDecode (pub : List Fp) : List UInt8 :=
  (pub.take 48).map (fun x=>UInt8.ofNat x.toNat)

/-- Executable exact direct-profile statement check. Raw field serialization
must separately reject noncanonical integers before constructing Fp values. -/
def sha384DirectPublicCheck (pub : List Fp) : Bool :=
  pub.length==88 && pub==sha384DirectPublic (sha384DirectPublicDecode pub)

theorem sha384_direct_public_check_canonical (pub : List Fp)
    (accepted : sha384DirectPublicCheck pub=true) :
    (sha384DirectPublicDecode pub).length=48 ∧
      pub=sha384DirectPublic (sha384DirectPublicDecode pub) := by
  have checks : pub.length=88 ∧ pub=sha384DirectPublic (sha384DirectPublicDecode pub) := by
    simpa only [sha384DirectPublicCheck,Bool.and_eq_true,beq_iff_eq] using accepted
  exact ⟨by simp [sha384DirectPublicDecode,checks.1],checks.2⟩

theorem sha384_direct_public_check_exists (pub : List Fp)
    (accepted : sha384DirectPublicCheck pub=true) :
    ∃digest : List UInt8,digest.length=48 ∧ pub=sha384DirectPublic digest :=
  ⟨sha384DirectPublicDecode pub,sha384_direct_public_check_canonical pub accepted⟩

theorem sha384_direct_public_decode (digest : List UInt8) (size : digest.length=48) :
    sha384DirectPublicDecode (sha384DirectPublic digest)=digest := by
  have headPart : (sha384DirectPublic digest).take 48=
      digest.map (fun b=>Fp.ofNat b.toNat) := by
    unfold sha384DirectPublic
    rw [List.append_assoc,List.append_assoc]
    have len : (digest.map (fun b=>Fp.ofNat b.toNat)).length=48 := by simp [size]
    rw [←len,List.take_left]
  unfold sha384DirectPublicDecode
  rw [headPart,List.map_map]
  conv => rhs; rw [←List.map_id digest]
  apply List.map_congr_left
  intro x hx
  dsimp only [Function.comp_def]
  rw [Fp.toNat_ofNat,Nat.mod_eq_of_lt (show x.toNat<P from by have h:x.toNat<256:=x.toNat_lt_size;unfold P;omega)]
  exact UInt8.ofNat_toNat

theorem sha384_direct_public_check_complete (digest : List UInt8) (size : digest.length=48) :
    sha384DirectPublicCheck (sha384DirectPublic digest)=true := by
  simp only [sha384DirectPublicCheck,sha384_direct_public_length digest size,
    sha384_direct_public_decode digest size,beq_self_eq_true,Bool.and_self]

theorem sha384_direct_public_check_sound (n : Nat) (fixed : List (Nat × Nat))
    (pub : List Fp) (tr : Trace Fp) (accepted : sha384DirectPublicCheck pub=true)
    (holds : HoldsP (sha384DirectInputAir n fixed) pub tr)
    (bound : sha384PaddedLength n/128<P) :
    sha384ChainDigest (sha384DirectMessageBytes n pub tr)=sha384DirectPublicDecode pub := by
  obtain ⟨size,canonical⟩:=sha384_direct_public_check_canonical pub accepted
  have sound:=sha384_direct_message_sound n fixed (sha384DirectPublicDecode pub) size tr
    (canonical ▸ holds) bound
  rw [←canonical] at sound
  exact sound

end NearCompression
