import NearCompression.SHA384MultiBlock

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra NearSpecV3.SHA512 ArenaCore


-- Private list/byte helpers follow ZkFormal.Sha.Complete.Pad, avoiding its unrelated SHA256 build chain.
private theorem getD_append_left' (l1 l2 : List Nat) (i : Nat) (h : i < l1.length) :
    (l1 ++ l2).getD i 0 = l1.getD i 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

private theorem getD_append_right' (l1 l2 : List Nat) (i : Nat) (h : l1.length ≤ i) :
    (l1 ++ l2).getD i 0 = l2.getD (i - l1.length) 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

private theorem beN_getD (w x i : Nat) (hi : i < w) :
    ((Bytes.beN w x).map UInt8.toNat).getD i 0 = x / 256 ^ (w - 1 - i) % 256 := by
  induction w generalizing x i with
  | zero => omega
  | succ w ih =>
    simp only [Bytes.beN, List.map_append, List.map_cons, List.map_nil]
    by_cases h : i < w
    · rw [getD_append_left' _ _ _ (by simp [Bytes.beN_length]; omega), ih _ _ h,
        Nat.div_div_eq_div_mul, ← Nat.pow_succ']
      congr 3 <;> omega
    · rw [getD_append_right' _ _ _ (by simp [Bytes.beN_length]; omega)]
      simp only [List.length_map, Bytes.beN_length, show i - w = 0 by omega, List.getD_cons_zero,
        show w + 1 - 1 - i = 0 by omega, Nat.pow_zero, Nat.div_one, UInt8.toNat_ofNat']
      exact Nat.mod_mod_of_dvd _ (by decide)


theorem sha384_padding_length (m : List Nat) :
    (pad m).length=sha384PaddedLength m.length := by
  simp only [pad,List.length_append,List.length_singleton,List.length_replicate,
    List.length_map,Bytes.beN_length,sha384PaddedLength]
  omega

theorem sha384_padding_byte (m : List Nat) (i : Nat) (hi : i<sha384PaddedLength m.length) :
    (pad m).getD i 0=
      if i<m.length then m.getD i 0 else if i=m.length then 128
      else if sha384PaddedLength m.length-16≤i then
        (8*m.length)/256^(sha384PaddedLength m.length-1-i)%256 else 0 := by
  have length := sha384_padding_length m
  have size : sha384PaddedLength m.length=m.length+1+(239-m.length%128)%128+16 := by
    rw [←length]
    simp only [pad,List.length_append,List.length_singleton,List.length_replicate,List.length_map,Bytes.beN_length]
  by_cases data : i<m.length
  · simp only [data,ite_true]
    unfold pad
    rw [List.append_assoc,List.append_assoc,getD_append_left' _ _ _ data]
  · simp only [data,ite_false]
    by_cases marker : i=m.length
    · subst i
      simp only [ite_true]
      unfold pad
      rw [List.append_assoc,List.append_assoc,getD_append_right' _ _ _ (Nat.le_refl _),Nat.sub_self]
      rfl
    · simp only [marker,ite_false]
      by_cases suffix : sha384PaddedLength m.length-16≤i
      · simp only [suffix,ite_true]
        unfold pad
        rw [getD_append_right' _ _ _ (by simp;omega)]
        simp only [List.length_append,List.length_singleton,List.length_replicate]
        rw [beN_getD 16 _ _ (by omega)]
        congr 3
        omega
      · simp only [suffix,ite_false]
        unfold pad
        rw [List.append_assoc,List.append_assoc,getD_append_right' _ _ _ (by omega)]
        rw [show i-m.length=(i-m.length-1)+1 by omega,List.singleton_append,List.getD_cons_succ]
        rw [getD_append_left' _ _ _ (by simp;omega)]
        simp only [List.getD_eq_getElem?_getD,List.getElem?_replicate]
        split <;> rfl

theorem sha384_padding_expr (m : List Nat) (tr : Trace Fp) (t r : Nat) (pub : List Fp)
    (bound : ∀ i,i<m.length → pub.getD i 0=Fp.ofNat (m.getD i 0))
    (i : Nat) (hi : i<sha384PaddedLength m.length) :
    (sha384PaddedByte m.length i).eval tr t r pub=Fp.ofNat ((pad m).getD i 0) := by
  rw [sha384_padding_byte m i hi]
  unfold sha384PaddedByte
  by_cases data : i<m.length
  · simp only [data,ite_true,Expr.eval,Expr.evalWith,rowEnv]
    exact bound i data
  · simp only [data,ite_false]
    split
    · rfl
    · split <;> rfl

theorem sha384_word_bytes (word : Nat) :
    (Bytes.beN 8 word).map UInt8.toNat=sha512NatWordBytes word := by
  simp [Bytes.beN,sha512NatWordBytes,Nat.div_div_eq_div_mul]

end NearCompression
