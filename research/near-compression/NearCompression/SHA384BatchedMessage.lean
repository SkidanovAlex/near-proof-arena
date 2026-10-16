import NearCompression.SHA384BatchedIVLayout
import NearCompression.SHA384EndpointPublic

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 NearSpecV3.SHA512
set_option maxRecDepth 65536

theorem sha384_batch_digest_count (n : Nat) (pub : List Fp)
    (countBytes : ∀ j,j<4 → pub.getD (n+48+j) 0=if j=0 then 1 else 0) :
    pubCount (sha384BatchedAir n) pub 3 false (sha384EndpointPublicDigest n pub)=1 ∧
    pubCount (sha384BatchedAir n) pub 3 true (sha384EndpointPublicDigest n pub)=0 := by
  have c0 := countBytes 0 (by decide)
  have c1 := countBytes 1 (by decide)
  have c2 := countBytes 2 (by decide)
  have c3 := countBytes 3 (by decide)
  have count : ({bus:=3,send:=false,width:=48,countAt:=n+48,start:=n}:PubSeg).count pub=1 := by
    simp only [PubSeg.count,show List.range 4=[0,1,2,3] from rfl,List.map_cons,List.map_nil,
      c0,c1,c2,c3,leNat]
    decide
  simp only [pubCount,pubMsgs,sha384BatchedAir,List.flatMap_cons,List.flatMap_nil,List.append_nil,
    PubSeg.msgs,count,show List.range 1=[0] from rfl,List.map_cons,List.map_nil]
  simp [PubSeg.record,PubSeg.startOffset,sha384EndpointPublicDigest]



theorem sha384_batch_digest_match (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384BatchedAir n) pub tr)
    (countBytes : ∀ j,j<4 → pub.getD (n+48+j) 0=if j=0 then 1 else 0) :
    ∃ r,r<tr.height 1 ∧
      tr.cell 1 r 1665=1 ∧
      tr.cell 1 r 1666=1 ∧
      sha384EndpointDigestMessage.map (fun e => e.eval tr 1 r pub)=
        sha384EndpointPublicDigest n pub := by
  have counts := sha384_batch_digest_count n pub countBytes
  have balance := h.balance 3 (sha384EndpointPublicDigest n pub)
  rw [counts.1,counts.2,Nat.add_zero] at balance
  have positive : busCount (sha384BatchedAir n).toAir tr pub 3 true (sha384EndpointPublicDigest n pub)≠0 := by omega
  obtain ⟨t,ht,hc⟩ := ZkFormal.Chacha.busCount_go_pos tr pub 3 true _ _ 0 positive
  simp only [Nat.zero_add] at hc
  obtain ⟨r,hr,i,hi,hb,hs,msg,mult⟩ := ZkFormal.Chacha.exists_of_tableBusCount hc
  obtain ⟨rfl,rfl⟩ := sha384_batch_output_sender n t ht true i hi hb hs
  have active := sha384_batch_endpoint_send_active n pub tr h r hr true mult
  have last : tr.cell 1 r 1666=1 := by
    simp only [sha384EndpointTable,ite_true,List.getElem!_cons_zero,List.getElem!_cons_succ,
      Interaction.multNat,Interaction.multNat.go,Expr.eval,Expr.evalWith,rowEnv] at mult
    split at mult
    · rename_i eq; simp at eq
    · simp_all; grind
  exact ⟨r,hr,active,last,msg⟩

theorem sha384_batch_digest_bytes (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384BatchedAir n) pub tr) (r : Nat)
    (hr : r<tr.height 1)
    (msg : sha384EndpointDigestMessage.map (fun e => e.eval tr 1 r pub)=
      sha384EndpointPublicDigest n pub) :
    ((digestBytes (sha384EndpointOutput (tr.cell 1 r))).take 48).map UInt8.toNat=
      (List.range 48).map (fun j => (pub.getD (n+j) 0).toNat) := by
  have add (i : Nat) (hi : i<8) := sha384_endpoint_add_holds (sha384BatchedAir n) tr pub
    1 (by simp [sha384BatchedAir]) n (by simp [sha384BatchedAir]) h r i hr hi
  have full : (digestBytes (sha384EndpointOutput (tr.cell 1 r))).map UInt8.toNat=
      (List.range 8).flatMap (fun i => sha512WindowWordBytes (fun c => tr.cell 1 r (208*i+c)) 144) := by
    simp only [digestBytes,sha384EndpointOutput,List.flatMap_map,List.map_flatMap]
    apply congrArg List.flatten
    apply List.map_congr_left
    intro i hi
    have ai := add i (List.mem_range.mp hi)
    rw [sha384_word_bytes,sha512_add_word_bits _ ai 8 (by decide)]
    exact sha512_nat_word_bytes_bits _ 144 (fun bit hb => sha512_add_word_bit _ ai 8 bit (by decide) hb)
  rw [List.map_take,full]
  change (List.range 48).map (fun j => sha512WindowByte (fun c => tr.cell 1 r (208*(j/8)+c)) 144 (7-j%8))=_
  apply List.map_congr_left
  intro j hj
  have jb := List.mem_range.mp hj
  have ai := add (j/8) (by omega)
  have bits (bit : Nat) (hb : bit<64) := sha512_add_word_bit _ ai 8 bit (by decide) hb
  have bounded := sha512_window_byte_bound (fun c => tr.cell 1 r (208*(j/8)+c)) 144 (7-j%8) (by omega) bits
  have field := congrArg (fun xs : List Fp => xs.getD j 0) msg
  simp only [sha384EndpointDigestMessage,sha384EndpointPublicDigest,List.map_map] at field
  simp [List.getD_eq_getElem?_getD,jb] at field
  rw [sha512_public_bitexpr_eval,sha512_bit_expr_field] at field
  have value := congrArg Fp.toNat field
  rw [Fp.toNat_ofNat] at value
  have small : sha512WindowByte (fun c => tr.cell 1 r (208*(j/8)+c)) 144 (7-j%8)<P := by unfold P;omega
  have value' : sha512WindowByte (fun c => tr.cell 1 r (208*(j/8)+c)) 144 (7-j%8)%P=(pub.getD (n+j) 0).toNat := by
    simpa only [sha512WindowByte,Nat.add_assoc,List.getD_eq_getElem?_getD] using value
  rwa [Nat.mod_eq_of_lt small] at value'

/-- Final endpoint selection is derived from its zero-test and exact public bus balance. -/
theorem sha384_batch_final_digest (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384BatchedAir n) pub tr) (bound : sha384PaddedLength n/128<P)
    (countBytes : ∀ j,j<4 → pub.getD (n+48+j) 0=if j=0 then 1 else 0) :
    ((digestBytes (sha384BatchCompression tr (sha384PaddedLength n/128-1))).take 48).map UInt8.toNat=
      (List.range 48).map (fun j => (pub.getD (n+j) 0).toNat) := by
  obtain ⟨r,hr,active,last,msg⟩ := sha384_batch_digest_match n pub tr h countBytes
  obtain ⟨t,ht,tag,out⟩ := sha384_batch_endpoint_compression n pub tr h bound r hr active
  have finalTag := (sha384_endpoint_last_iff (sha384BatchedAir n) tr pub 1
    (by simp [sha384BatchedAir]) n (by simp [sha384BatchedAir]) h r hr).mp last
  have same := congrArg Fp.toNat (tag.symm.trans finalTag)
  rw [Fp.toNat_ofNat,Fp.toNat_ofNat,Nat.mod_eq_of_lt (by omega : t<P),
    Nat.mod_eq_of_lt (by omega : sha384PaddedLength n/128-1<P)] at same
  subst t
  rw [←out]
  exact sha384_batch_digest_bytes n pub tr h r hr msg


theorem sha384_batched_endpoint_expansion (message digest : List UInt8) :
    sha384BatchedPublic message digest=sha384EndpointPublic message digest ++
      (sha384BatchPayload message ++ sha384BatchCountBytes (sha384PaddedLength message.length/128) ++
        sha384BatchIVPayload ++ [1,0,0,0]).map Fp.ofNat := by
  simp [sha384BatchedPublic,sha384BatchedPublicNat,sha384EndpointPublic,sha384MessagePublic,
    List.map_append,List.map_map,Function.comp_def,List.append_assoc]
  exact ⟨rfl,rfl⟩

theorem sha384_batched_endpoint_public_get (message digest : List UInt8) (size : digest.length=48)
    (i : Nat) (hi : i<message.length+52) :
    (sha384BatchedPublic message digest).getD i 0=(sha384EndpointPublic message digest).getD i 0 := by
  rw [sha384_batched_endpoint_expansion]
  have len : (sha384EndpointPublic message digest).length=message.length+52 := by
    simp [sha384EndpointPublic,sha384MessagePublic,size]
  simp only [List.getD_eq_getElem?_getD,List.getElem?_append_left (by omega : i<(sha384EndpointPublic message digest).length)]

theorem sha384_batched_digest_count_layout (message digest : List UInt8) (size : digest.length=48)
    (j : Nat) (hj : j<4) :
    (sha384BatchedPublic message digest).getD (message.length+48+j) 0=if j=0 then 1 else 0 := by
  rw [sha384_batched_endpoint_public_get message digest size _ (by omega)]
  exact sha384_endpoint_public_count_layout message digest size j hj

theorem sha384_batched_digest_layout (message digest : List UInt8) (size : digest.length=48) :
    (List.range 48).map (fun j => ((sha384BatchedPublic message digest).getD (message.length+j) 0).toNat)=
      digest.map UInt8.toNat := by
  rw [←sha384_endpoint_public_digest_layout message digest size]
  apply List.map_congr_left
  intro j hj
  rw [sha384_batched_endpoint_public_get message digest size _ (by have jb:=List.mem_range.mp hj;omega)]

theorem sha384_batch_blocks_step (message : List UInt8) (pub : List Fp) (tr : Trace Fp)
    (_h : HoldsP (sha384BatchedAir message.length) pub tr)
    (decoded : ∀ block,block<sha384PaddedLength message.length/128 →
      sha512DecodedBlock (tr.cell 0 (80*block))=((pad (message.map UInt8.toNat)).drop (128*block)).take 128)
    (t k : Nat) (ht : t<sha384PaddedLength message.length/128) :
    blocks (k+1) (sha512DecodedState (tr.cell 0 (80*t))) ((pad (message.map UInt8.toNat)).drop (128*t))=
      blocks k (sha384BatchCompression tr t) ((pad (message.map UInt8.toNat)).drop (128*(t+1))) := by
  let rest := (pad (message.map UInt8.toNat)).drop (128*t)
  have size := sha384_padding_length (message.map UInt8.toNat)
  simp only [List.length_map] at size
  have len : (rest.take 128).length=128 := by
    simp only [rest,List.length_take,List.length_drop,size]
    unfold sha384PaddedLength at ht ⊢
    omega
  have step := sha512_blocks_cons_exact k (sha512DecodedState (tr.cell 0 (80*t))) (rest.take 128) (rest.drop 128) len
  rw [List.take_append_drop] at step
  dsimp only [rest] at step
  rw [←decoded t ht] at step
  simpa only [sha384BatchCompression,List.drop_drop,Nat.mul_add,Nat.mul_one] using step

theorem sha384_batch_blocks_chain (message : List UInt8) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384BatchedAir message.length) pub tr)
    (decoded : ∀ block,block<sha384PaddedLength message.length/128 →
      sha512DecodedBlock (tr.cell 0 (80*block))=((pad (message.map UInt8.toNat)).drop (128*block)).take 128)
    (bound : sha384PaddedLength message.length/128<P) (k t : Nat)
    (ht : t+k<sha384PaddedLength message.length/128) :
    blocks (k+1) (sha512DecodedState (tr.cell 0 (80*t))) ((pad (message.map UInt8.toNat)).drop (128*t))=
      sha384BatchCompression tr (t+k) := by
  induction k generalizing t with
  | zero =>
    rw [sha384_batch_blocks_step message pub tr h decoded t 0 (by omega)]
    rfl
  | succ k ih =>
    rw [sha384_batch_blocks_step message pub tr h decoded t (k+1) (by omega),
      sha384_batch_compression_link message.length pub tr h bound t (by omega)]
    have result := ih (t+1) (by omega)
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using result


theorem sha384_batched_final_state_of_decoded (message digest : List UInt8) (size : digest.length=48)
    (tr : Trace Fp)
    (h : HoldsP (sha384BatchedAir message.length) (sha384BatchedPublic message digest) tr)
    (bound : sha384PaddedLength message.length/128<P)
    (decoded : ∀ block,block<sha384PaddedLength message.length/128 →
      sha512DecodedBlock (tr.cell 0 (80*block))=((pad (message.map UInt8.toNat)).drop (128*block)).take 128) :
    blocks (sha384PaddedLength message.length/128) sha384ChainIV (pad (message.map UInt8.toNat))=
      sha384BatchCompression tr (sha384PaddedLength message.length/128-1) := by
  have pos : 0<sha384PaddedLength message.length/128 := by unfold sha384PaddedLength;omega
  have result := sha384_batch_blocks_chain message _ tr h decoded bound
    (sha384PaddedLength message.length/128-1) 0 (by omega)
  simp only [Nat.mul_zero] at result
  rw [sha384_batched_public_initial message digest size tr h bound] at result
  simpa only [Nat.zero_add,Nat.mul_zero,List.drop_zero,
    Nat.sub_add_cancel (by omega : 1≤sha384PaddedLength message.length/128)] using result

/-- Whole-message composition with exactly one remaining semantic interface:
public payload records must decode to the padded message blocks. All phases,
round arithmetic, natural state routing, IV and final digest binding are derived
from actual batched AIR satisfaction and its canonical public layout. -/
theorem sha384_batched_message_sound_of_decoded (message digest : List UInt8) (size : digest.length=48)
    (tr : Trace Fp)
    (h : HoldsP (sha384BatchedAir message.length) (sha384BatchedPublic message digest) tr)
    (bound : sha384PaddedLength message.length/128<P)
    (decoded : ∀ block,block<sha384PaddedLength message.length/128 →
      sha512DecodedBlock (tr.cell 0 (80*block))=((pad (message.map UInt8.toNat)).drop (128*block)).take 128) :
    sha384ChainDigest message=digest := by
  have final := sha384_batched_final_state_of_decoded message digest size tr h bound decoded
  have bytes := sha384_batch_final_digest message.length _ tr h bound
    (sha384_batched_digest_count_layout message digest size)
  rw [sha384_batched_digest_layout message digest size] at bytes
  have eq : (sha384ChainDigest message).map UInt8.toNat=digest.map UInt8.toNat := by
    dsimp only [sha384ChainDigest]
    rw [sha384_padding_length,List.length_map,final]
    exact bytes
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
