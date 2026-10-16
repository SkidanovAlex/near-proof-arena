import NearCompression.SHA384EndpointRouting

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 NearSpecV3.SHA512
set_option maxRecDepth 65536

def sha384EndpointPublicDigest (n : Nat) (pub : List Fp) : List Fp :=
  (List.range 48).map (fun j => pub.getD (n+j) 0)

theorem sha384_endpoint_public_count (n : Nat) (pub : List Fp)
    (countBytes : ∀ j,j<4 → pub.getD (n+48+j) 0=if j=0 then 1 else 0) :
    pubCount (sha384EndpointAir n) pub 3 false (sha384EndpointPublicDigest n pub)=1 ∧
    pubCount (sha384EndpointAir n) pub 3 true (sha384EndpointPublicDigest n pub)=0 := by
  have c0 := countBytes 0 (by decide)
  have c1 := countBytes 1 (by decide)
  have c2 := countBytes 2 (by decide)
  have c3 := countBytes 3 (by decide)
  have count : ({bus:=3,send:=false,width:=48,countAt:=n+48,start:=n}:PubSeg).count pub=1 := by
    simp only [PubSeg.count,show List.range 4=[0,1,2,3] from rfl,List.map_cons,List.map_nil,
      c0,c1,c2,c3,leNat]
    decide
  simp only [pubCount,pubMsgs,sha384EndpointAir,List.flatMap_cons,List.flatMap_nil,List.append_nil,
    PubSeg.msgs,count,show List.range 1=[0] from rfl,List.map_cons,List.map_nil]
  simp [PubSeg.record,PubSeg.startOffset,sha384EndpointPublicDigest]



theorem sha384_endpoint_public_match (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384EndpointAir n) pub tr)
    (countBytes : ∀ j,j<4 → pub.getD (n+48+j) 0=if j=0 then 1 else 0) :
    ∃ r,r<tr.height (sha384PaddedLength n/128) ∧
      tr.cell (sha384PaddedLength n/128) r 1665=1 ∧
      tr.cell (sha384PaddedLength n/128) r 1666=1 ∧
      sha384EndpointDigestMessage.map (fun e => e.eval tr (sha384PaddedLength n/128) r pub)=
        sha384EndpointPublicDigest n pub := by
  have counts := sha384_endpoint_public_count n pub countBytes
  have balance := h.balance 3 (sha384EndpointPublicDigest n pub)
  rw [counts.1,counts.2,Nat.add_zero] at balance
  have positive : busCount (sha384EndpointAir n).toAir tr pub 3 true (sha384EndpointPublicDigest n pub)≠0 := by omega
  obtain ⟨t,ht,hc⟩ := ZkFormal.Chacha.busCount_go_pos tr pub 3 true _ _ 0 positive
  simp only [Nat.zero_add] at hc
  obtain ⟨r,hr,i,hi,hb,hs,msg,mult⟩ := ZkFormal.Chacha.exists_of_tableBusCount hc
  obtain ⟨rfl,rfl⟩ := sha384_endpoint_output_sender n t ht true i hi hb hs
  have active := sha384_endpoint_send_active n pub tr h r hr true mult
  have last : tr.cell (sha384PaddedLength n/128) r 1666=1 := by
    simp only [sha384EndpointTable,ite_true,List.getElem!_cons_zero,List.getElem!_cons_succ,
      Interaction.multNat,Interaction.multNat.go,Expr.eval,Expr.evalWith,rowEnv] at mult
    split at mult
    · rename_i eq; simp at eq
    · simp_all; grind
  exact ⟨r,hr,active,last,msg⟩

theorem sha384_endpoint_blocks_step (message : List UInt8) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384EndpointAir message.length) pub tr)
    (pubBound : ∀ i,i<message.length → pub.getD i 0=Fp.ofNat ((message.map UInt8.toNat).getD i 0))
    (t k : Nat) (ht : t<sha384PaddedLength message.length/128) :
    blocks (k+1) (sha512DecodedState (tr.cell t 0)) ((pad (message.map UInt8.toNat)).drop (128*t))=
      blocks k (sha384CoreCompression tr t) ((pad (message.map UInt8.toNat)).drop (128*(t+1))) := by
  let rest := (pad (message.map UInt8.toNat)).drop (128*t)
  have size := sha384_padding_length (message.map UInt8.toNat)
  simp only [List.length_map] at size
  have len : (rest.take 128).length=128 := by
    simp only [rest,List.length_take,List.length_drop,size]
    unfold sha384PaddedLength at ht ⊢
    omega
  have step := sha512_blocks_cons_exact k (sha512DecodedState (tr.cell t 0)) (rest.take 128) (rest.drop 128) len
  rw [List.take_append_drop] at step
  dsimp only [rest] at step
  rw [←sha384_split_padded_block message pub tr h pubBound t ht] at step
  simpa only [sha384CoreCompression,List.drop_drop,Nat.mul_add,Nat.mul_one] using step

theorem sha384_endpoint_blocks_chain (message : List UInt8) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384EndpointAir message.length) pub tr)
    (pubBound : ∀ i,i<message.length → pub.getD i 0=Fp.ofNat ((message.map UInt8.toNat).getD i 0))
    (bound : sha384PaddedLength message.length/128<P) (k t : Nat)
    (ht : t+k<sha384PaddedLength message.length/128) :
    blocks (k+1) (sha512DecodedState (tr.cell t 0)) ((pad (message.map UInt8.toNat)).drop (128*t))=
      sha384CoreCompression tr (t+k) := by
  induction k generalizing t with
  | zero =>
    rw [sha384_endpoint_blocks_step message pub tr h pubBound t 0 (by omega)]
    rfl
  | succ k ih =>
    rw [sha384_endpoint_blocks_step message pub tr h pubBound t (k+1) (by omega),
      sha384_endpoint_compression_link message.length pub tr h bound t (by omega)]
    have result := ih (t+1) (by omega)
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using result

/-- The complete compression chain is derived from the actual multiblock AIR,
including exact natural bus balance, public message bytes, padding and IV. -/
theorem sha384_endpoint_final_state (message : List UInt8) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384EndpointAir message.length) pub tr)
    (pubBound : ∀ i,i<message.length → pub.getD i 0=Fp.ofNat ((message.map UInt8.toNat).getD i 0))
    (bound : sha384PaddedLength message.length/128<P) :
    blocks (sha384PaddedLength message.length/128) sha384ChainIV (pad (message.map UInt8.toNat))=
      sha384CoreCompression tr (sha384PaddedLength message.length/128-1) := by
  have pos : 0<sha384PaddedLength message.length/128 := by unfold sha384PaddedLength;omega
  have result := sha384_endpoint_blocks_chain message pub tr h pubBound bound
    (sha384PaddedLength message.length/128-1) 0 (by omega)
  rw [sha384_split_initial message.length pub tr h] at result
  simpa only [Nat.zero_add,Nat.mul_zero,List.drop_zero,Nat.sub_add_cancel (by omega : 1≤sha384PaddedLength message.length/128)] using result


theorem sha384_endpoint_digest_bytes (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384EndpointAir n) pub tr) (r : Nat)
    (hr : r<tr.height (sha384PaddedLength n/128))
    (msg : sha384EndpointDigestMessage.map (fun e => e.eval tr (sha384PaddedLength n/128) r pub)=
      sha384EndpointPublicDigest n pub) :
    ((digestBytes (sha384EndpointOutput (tr.cell (sha384PaddedLength n/128) r))).take 48).map UInt8.toNat=
      (List.range 48).map (fun j => (pub.getD (n+j) 0).toNat) := by
  have add (i : Nat) (hi : i<8) := sha384_endpoint_add_holds (sha384EndpointAir n) tr pub
    (sha384PaddedLength n/128) (by simp [sha384EndpointAir]) n (by simp [sha384EndpointAir]) h r i hr hi
  have full : (digestBytes (sha384EndpointOutput (tr.cell (sha384PaddedLength n/128) r))).map UInt8.toNat=
      (List.range 8).flatMap (fun i => sha512WindowWordBytes (fun c => tr.cell (sha384PaddedLength n/128) r (208*i+c)) 144) := by
    simp only [digestBytes,sha384EndpointOutput,List.flatMap_map,List.map_flatMap]
    apply congrArg List.flatten
    apply List.map_congr_left
    intro i hi
    have ai := add i (List.mem_range.mp hi)
    rw [sha384_word_bytes,sha512_add_word_bits _ ai 8 (by decide)]
    exact sha512_nat_word_bytes_bits _ 144 (fun bit hb => sha512_add_word_bit _ ai 8 bit (by decide) hb)
  rw [List.map_take,full]
  change (List.range 48).map (fun j => sha512WindowByte (fun c => tr.cell (sha384PaddedLength n/128) r (208*(j/8)+c)) 144 (7-j%8))=_
  apply List.map_congr_left
  intro j hj
  have jb := List.mem_range.mp hj
  have ai := add (j/8) (by omega)
  have bits (bit : Nat) (hb : bit<64) := sha512_add_word_bit _ ai 8 bit (by decide) hb
  have bounded := sha512_window_byte_bound (fun c => tr.cell (sha384PaddedLength n/128) r (208*(j/8)+c)) 144 (7-j%8) (by omega) bits
  have field := congrArg (fun xs : List Fp => xs.getD j 0) msg
  simp only [sha384EndpointDigestMessage,sha384EndpointPublicDigest,List.map_map] at field
  simp [List.getD_eq_getElem?_getD,jb] at field
  rw [sha512_public_bitexpr_eval,sha512_bit_expr_field] at field
  have value := congrArg Fp.toNat field
  rw [Fp.toNat_ofNat] at value
  have small : sha512WindowByte (fun c => tr.cell (sha384PaddedLength n/128) r (208*(j/8)+c)) 144 (7-j%8)<P := by unfold P;omega
  have value' : sha512WindowByte (fun c => tr.cell (sha384PaddedLength n/128) r (208*(j/8)+c)) 144 (7-j%8)%P=(pub.getD (n+j) 0).toNat := by
    simpa only [sha512WindowByte,Nat.add_assoc,List.getD_eq_getElem?_getD] using value
  rwa [Nat.mod_eq_of_lt small] at value'

/-- Final endpoint selection is derived from its zero-test and exact public bus balance. -/
theorem sha384_endpoint_final_digest (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384EndpointAir n) pub tr) (bound : sha384PaddedLength n/128<P)
    (countBytes : ∀ j,j<4 → pub.getD (n+48+j) 0=if j=0 then 1 else 0) :
    ((digestBytes (sha384CoreCompression tr (sha384PaddedLength n/128-1))).take 48).map UInt8.toNat=
      (List.range 48).map (fun j => (pub.getD (n+j) 0).toNat) := by
  obtain ⟨r,hr,active,last,msg⟩ := sha384_endpoint_public_match n pub tr h countBytes
  obtain ⟨t,ht,tag,out⟩ := sha384_endpoint_output_compression n pub tr h bound r hr active
  have finalTag := (sha384_endpoint_last_iff (sha384EndpointAir n) tr pub (sha384PaddedLength n/128)
    (by simp [sha384EndpointAir]) n (by simp [sha384EndpointAir]) h r hr).mp last
  have same := congrArg Fp.toNat (tag.symm.trans finalTag)
  rw [Fp.toNat_ofNat,Fp.toNat_ofNat,Nat.mod_eq_of_lt (by omega : t<P),
    Nat.mod_eq_of_lt (by omega : sha384PaddedLength n/128-1<P)] at same
  subst t
  rw [←out]
  exact sha384_endpoint_digest_bytes n pub tr h r hr msg

/-- Semantic soundness of the endpoint-split AIR: the public digest is SHA384
of the public message. Cryptographic extraction from a proof remains separate. -/
theorem sha384_endpoint_digest_sound (message : List UInt8) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384EndpointAir message.length) pub tr)
    (pubBound : ∀ i,i<message.length → pub.getD i 0=Fp.ofNat ((message.map UInt8.toNat).getD i 0))
    (bound : sha384PaddedLength message.length/128<P)
    (countBytes : ∀ j,j<4 → pub.getD (message.length+48+j) 0=if j=0 then 1 else 0) :
    (sha384ChainDigest message).map UInt8.toNat=
      (List.range 48).map (fun j => (pub.getD (message.length+j) 0).toNat) := by
  have final := sha384_endpoint_final_state message pub tr h pubBound bound
  dsimp only [sha384ChainDigest]
  rw [sha384_padding_length,List.length_map,final]
  exact sha384_endpoint_final_digest message.length pub tr h bound countBytes


end NearCompression
