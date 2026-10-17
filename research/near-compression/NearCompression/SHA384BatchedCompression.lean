import NearCompression.SHA384BatchedSlice

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 NearSpecV3.SHA512
set_option maxRecDepth 65536

theorem sha384_batch_constant_sum (tr : Trace Fp) (pub : List Fp) (r phase limb count : Nat)
    (hc : count≤80)
    (phases : ∀ i,i<80 → tr.cell 0 r (5152+i)=if i=phase then 1 else 0) :
    (sha512ConstantSum limb count).eval tr 0 r pub=
      if phase<count then Fp.ofNat (sha512ConstantDigit phase limb) else 0 := by
  induction count with
  | zero => rfl
  | succ count ih =>
    change (sha512ConstantSum limb count).eval tr 0 r pub+
      tr.cell 0 r (5152+count)*Fp.ofNat (sha512ConstantDigit count limb)=_
    rw [ih (by omega),phases count (by omega)]
    by_cases eq : count=phase
    · subst count
      simp only [Nat.lt_irrefl,ite_false,ite_true,Nat.lt_succ_self]
      grind
    · by_cases lt : phase<count
      · have lt' : phase<count+1 := by omega
        rw [ite_eq_left lt,ite_eq_left lt',ite_eq_right eq]
        grind
      · have lt' : ¬phase<count+1 := by omega
        rw [ite_eq_right lt,ite_eq_right lt',ite_eq_right eq]
        grind

theorem sha384_batch_key_limb (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384BatchedAir n) pub tr) (bound : sha384PaddedLength n/128<P)
    (block phase limb : Nat) (hb : block<sha384PaddedLength n/128) (hp : phase<80) (hl : limb<4) :
    (tr.cell 0 (80*block+phase) (4116+limb)).toNat=sha512ConstantDigit phase limb := by
  have metadata := sha384_batch_segment_metadata n pub tr h bound block phase hb hp
  have hc := sha384_batch_constraint n pub tr h _ metadata.1
    (.mul sha384BatchActive (.add (.col (4116+limb) false) (.neg (sha512ConstantSum limb 80))))
    (by simp only [sha384BatchCoreConstraints,List.mem_append];exact Or.inl (Or.inr (List.mem_map.mpr ⟨limb,List.mem_range.mpr hl,rfl⟩)))
  change tr.cell 0 (80*block+phase) 5232*(tr.cell 0 (80*block+phase) (4116+limb)+
    -(sha512ConstantSum limb 80).eval tr 0 (80*block+phase) pub)=0 at hc
  rw [metadata.2.1,sha384_batch_constant_sum tr pub _ phase limb 80 (by decide) metadata.2.2.2,ite_eq_left hp] at hc
  have eq : tr.cell 0 (80*block+phase) (4116+limb)=Fp.ofNat (sha512ConstantDigit phase limb) := by grind
  rw [eq,Fp.toNat_ofNat]
  have small : sha512ConstantDigit phase limb<65536 := Nat.mod_lt _ (by decide)
  apply Nat.mod_eq_of_lt
  unfold P
  omega

theorem sha384_batch_key (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384BatchedAir n) pub tr) (bound : sha384PaddedLength n/128<P)
    (block phase : Nat) (hb : block<sha384PaddedLength n/128) (hp : phase<80) :
    sha512CombinedK (tr.cell 0 (80*block+phase))=K.getD phase 0 := by
  have l0 := sha384_batch_key_limb n pub tr h bound block phase 0 hb hp (by decide)
  have l1 := sha384_batch_key_limb n pub tr h bound block phase 1 hb hp (by decide)
  have l2 := sha384_batch_key_limb n pub tr h bound block phase 2 hb hp (by decide)
  have l3 := sha384_batch_key_limb n pub tr h bound block phase 3 hb hp (by decide)
  change (tr.cell 0 (80*block+phase) (4116+0)).toNat+65536*(tr.cell 0 (80*block+phase) (4116+1)).toNat+
    4294967296*(tr.cell 0 (80*block+phase) (4116+2)).toNat+281474976710656*(tr.cell 0 (80*block+phase) (4116+3)).toNat=_
  rw [l0,l1,l2,l3]
  exact sha512_constants_digits phase (by omega)

theorem sha384_batch_round_segment (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384BatchedAir n) pub tr) (bound : sha384PaddedLength n/128<P)
    (block count phase : Nat) (hb : block<sha384PaddedLength n/128) (hp : phase+count<80) :
    rounds (sha512CombinedVars (tr.cell 0 (80*block+phase)))
      ((List.range' phase (count+1)).map (fun i => K.getD i 0))
      (sha512CombinedWindow (tr.cell 0 (80*block+phase)))=
      sha512CombinedOutput (tr.cell 0 (80*block+(phase+count))) := by
  induction count generalizing phase with
  | zero =>
    have out := sha384_batch_output n pub tr h bound block phase hb (by omega)
    rw [sha384_batch_key n pub tr h bound block phase hb (by omega)] at out
    simpa only [List.range'_succ,List.range'_zero,List.map_cons,List.map_nil,rounds,Nat.add_zero] using out.symm
  | succ count ih =>
    have link := sha384_batch_recurrence n pub tr h bound block phase hb (by omega)
    rw [sha384_batch_key n pub tr h bound block phase hb (by omega)] at link
    rw [List.range'_succ,List.map_cons,rounds]
    rw [←link.1,←link.2]
    have result := ih (phase+1) (by omega)
    simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using result

/-- All eighty actual SHA512 rounds follow from batched AIR constraints. -/
theorem sha384_batch_rounds (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384BatchedAir n) pub tr) (bound : sha384PaddedLength n/128<P)
    (block : Nat) (hb : block<sha384PaddedLength n/128) :
    rounds (sha512CombinedVars (tr.cell 0 (80*block))) K
      (sha512CombinedWindow (tr.cell 0 (80*block)))=
      sha512CombinedOutput (tr.cell 0 (80*block+79)) := by
  have result := sha384_batch_round_segment n pub tr h bound block 79 0 hb (by decide)
  have keys : (List.range' 0 80).map (fun i => K.getD i 0)=K := by decide
  simpa only [Nat.zero_add,Nat.add_zero,keys] using result

def sha384BatchCompression (tr : Trace Fp) (block : Nat) : List Nat :=
  compress (sha512DecodedState (tr.cell 0 (80*block)))
    (sha512DecodedBlock (tr.cell 0 (80*block)))

/-- Exact compression arithmetic at the batched segment boundary. Endpoint
feed-forward routing and public message decoding are separate compositions. -/
theorem sha384_batch_compression (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384BatchedAir n) pub tr) (bound : sha384PaddedLength n/128<P)
    (block : Nat) (hb : block<sha384PaddedLength n/128) :
    sha384BatchCompression tr block=(List.range 8).map (fun i =>
      add64 (sha512FeedForwardVarsWord (sha512CombinedVars (tr.cell 0 (80*block))) i)
        (sha512FeedForwardVarsWord (sha512CombinedOutput (tr.cell 0 (80*block+79))) i)) := by
  unfold sha384BatchCompression sha512DecodedState
  rw [sha512_compress_vars,sha512_decoded_block_words]
  have result := sha384_batch_rounds n pub tr h bound block hb
  dsimp only [sha512CombinedWindow] at result
  rw [result]


end NearCompression
