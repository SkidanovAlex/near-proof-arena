import NearCompression.SHA384SharedBlockDecode
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Sha.View ZkFormal.Sha.Sound NearSpecV3.SHA512

/-- Boolean schedule bits and bounded target bytes make each field limb split unique. -/
theorem sha384_paired_limb_bytes (row : Nat → Fp) (target : Nat → Nat)
    (bounded : ∀ j,j<128 → target j<256)
    (bits : ∀ word bit,word<16 → bit<64 → (row (sha512ScheduleWindowBase word+bit)).toNat≤1)
    (limbs : ∀ word limb,word<16 → limb<4 →
      (instructionBitExpr (sha512ScheduleWindowBase word+16*limb) 16).evalWith (instructionAddEnv row)=
        Fp.ofNat (256*target (8*word+6-2*limb)+target (8*word+7-2*limb)))
    (word limb : Nat) (hw : word<16) (hl : limb<4) :
    sha512WindowByte row (sha512ScheduleWindowBase word) (2*limb)=target (8*word+7-2*limb) ∧
    sha512WindowByte row (sha512ScheduleWindowBase word) (2*limb+1)=target (8*word+6-2*limb) := by
  have low := bounded (8*word+7-2*limb) (by omega)
  have high := bounded (8*word+6-2*limb) (by omega)
  have decoded := (sha512_public_limb_decode row _ (sha512ScheduleWindowBase word+16*limb)
    (fun bit hb => by simpa only [Nat.add_assoc] using bits word (16*limb+bit) hw (by omega))
    (limbs word limb hw hl).symm).1
  rw [Fp.toNat_ofNat,Nat.mod_eq_of_lt (by unfold P;omega),show 16=8+8 from rfl,ofBits_add] at decoded
  have lo := sha512_window_byte_bound row (sha512ScheduleWindowBase word) (2*limb) (by omega)
    (fun bit hb => bits word bit hw hb)
  have hi := sha512_window_byte_bound row (sha512ScheduleWindowBase word) (2*limb+1) (by omega)
    (fun bit hb => bits word bit hw hb)
  have lowIndex : sha512ScheduleWindowBase word+8*(2*limb)=sha512ScheduleWindowBase word+16*limb := by omega
  have highIndex : sha512ScheduleWindowBase word+8*(2*limb+1)=sha512ScheduleWindowBase word+16*limb+8 := by omega
  have split : 256*target (8*word+6-2*limb)+target (8*word+7-2*limb)=
      sha512WindowByte row (sha512ScheduleWindowBase word) (2*limb)+
        256*sha512WindowByte row (sha512ScheduleWindowBase word) (2*limb+1) := by
    simpa only [sha512WindowByte,lowIndex,highIndex,Nat.add_assoc,Nat.reducePow] using decoded
  omega

/-- All 64 paired limbs determine the entire ordered 128-byte block. -/
theorem sha384_paired_decoded_block (row : Nat → Fp) (target : Nat → Nat)
    (bounded : ∀ j,j<128 → target j<256)
    (bits : ∀ word bit,word<16 → bit<64 → (row (sha512ScheduleWindowBase word+bit)).toNat≤1)
    (limbs : ∀ word limb,word<16 → limb<4 →
      (instructionBitExpr (sha512ScheduleWindowBase word+16*limb) 16).evalWith (instructionAddEnv row)=
        Fp.ofNat (256*target (8*word+6-2*limb)+target (8*word+7-2*limb))) :
    sha512DecodedBlock row=(List.range 128).map target := by
  rw [sha384_multiblock_decoded_block_shape]
  apply List.map_congr_left
  intro j hj
  have jb := List.mem_range.mp hj
  have pair := sha384_paired_limb_bytes row target bounded bits limbs (j/8) ((7-j%8)/2) (by omega) (by omega)
  have cases : 7-j%8=2*((7-j%8)/2) ∨ 7-j%8=2*((7-j%8)/2)+1 := by omega
  rcases cases with low | high
  · have idx : 8*(j/8)+7-2*((7-j%8)/2)=j := by omega
    rw [idx,←low] at pair
    exact pair.1
  · have idx : 8*(j/8)+6-2*((7-j%8)/2)=j := by omega
    rw [idx,←high] at pair
    exact pair.2
end NearCompression
