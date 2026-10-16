import NearCompression.SHA384BatchedPublic

namespace NearCompression
open ZkFormal.Algebra NearSpecV3.SHA512

private theorem flat_length {α : Type} (n width : Nat) (f : Nat → List α)
    (shape : ∀ i,(f i).length=width) :
    ((List.range n).flatMap f).length=n*width := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ,List.flatMap_append,ih,shape,Nat.succ_mul]

/-- Indexing a fixed-width concatenation uses the same block-major order as
the public bus payload. No lookup or index equality is assumed. -/
theorem sha384_flat_payload_index {α : Type} (n width : Nat) (f : Nat → List α)
    (shape : ∀ i,(f i).length=width) (block offset : Nat)
    (hb : block<n) (ho : offset<width) (fallback : α) :
    ((List.range n).flatMap f).getD (block*width+offset) fallback=
      (f block).getD offset fallback := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ,List.flatMap_append]
    simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil]
    by_cases smaller : block<n
    · have index : block*width+offset<((List.range n).flatMap f).length := by
        rw [flat_length n width f shape]
        have step := Nat.mul_le_mul_right width (show block+1≤n by omega)
        rw [Nat.add_mul] at step
        omega
      simp only [List.getD_eq_getElem?_getD,List.getElem?_append_left index]
      exact ih smaller
    · have eq : block=n := by omega
      subst block
      have index : ((List.range n).flatMap f).length≤n*width+offset := by
        rw [flat_length n width f shape];omega
      simp only [List.getD_eq_getElem?_getD,List.getElem?_append_right index,
        flat_length n width f shape,Nat.add_sub_cancel_left]

theorem sha384_batch_payload_index (message : List UInt8) (block word limb : Nat)
    (hb : block<sha384PaddedLength message.length/128) (hw : word<16) (hl : limb<4) :
    (sha384BatchPayload message).getD (block*64+word*4+limb) 0=
      256*(pad (message.map UInt8.toNat)).getD (128*block+8*word+6-2*limb) 0+
      (pad (message.map UInt8.toNat)).getD (128*block+8*word+7-2*limb) 0 := by
  unfold sha384BatchPayload
  rw [show block*64+word*4+limb=block*64+(word*4+limb) by omega]
  rw [sha384_flat_payload_index _ 64 _ (by intro b; exact flat_length 16 4 _ (by intro i;simp)) block (word*4+limb) hb (by omega) 0]
  rw [sha384_flat_payload_index 16 4 _ (by intro i;simp) word limb hw hl 0]
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range hl,
    Option.map_some,Option.getD_some]

theorem sha384_batch_iv_payload_index (word limb : Nat) (hw : word<8) (hl : limb<4) :
    sha384BatchIVPayload.getD (word*4+limb) 0=
      (sha384ChainIV.getD word 0/65536^limb)%65536 := by
  unfold sha384BatchIVPayload
  rw [sha384_flat_payload_index 8 4 _ (by intro i;simp) word limb hw hl 0]
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range hl,
    Option.map_some,Option.getD_some]

/-- The payload limb is at the actual public bus offset n+52. -/
theorem sha384_batched_public_payload_index (message digest : List UInt8)
    (size : digest.length=48) (block word limb : Nat)
    (hb : block<sha384PaddedLength message.length/128) (hw : word<16) (hl : limb<4) :
    (sha384BatchedPublicNat message digest).getD
      (message.length+52+(block*64+word*4+limb)) 0=
      256*(pad (message.map UInt8.toNat)).getD (128*block+8*word+6-2*limb) 0+
      (pad (message.map UInt8.toNat)).getD (128*block+8*word+7-2*limb) 0 := by
  let pre := (message++digest).map UInt8.toNat ++ [1,0,0,0]
  let tail := sha384BatchCountBytes (sha384PaddedLength message.length/128) ++
    sha384BatchIVPayload ++ [1,0,0,0]
  have layout : sha384BatchedPublicNat message digest=
      pre ++ (sha384BatchPayload message ++ tail) := by
    simp only [sha384BatchedPublicNat,pre,tail,List.append_assoc]
  have len : pre.length=message.length+52 := by simp [pre,size]
  have inside : block*64+word*4+limb<(sha384BatchPayload message).length := by
    rw [sha384_batch_payload_length]
    omega
  rw [layout]
  simp only [List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by rw [len];omega : pre.length≤message.length+52+(block*64+word*4+limb)),
    len,Nat.add_sub_cancel_left,List.getElem?_append_left inside]
  exact sha384_batch_payload_index message block word limb hb hw hl

end NearCompression
