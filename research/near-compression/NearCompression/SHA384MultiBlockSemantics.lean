import NearCompression.SHA384Padding
import ZkFormal.Chacha.Bus
import ZkFormal.V2.VerifierDefs

/-! Semantic soundness of the canonical multiblock SHA384 AIR.

The final theorem consumes actual `HoldsP`, public-message byte binding, and
an explicit block-count bound preventing field-tag aliases. Compression,
phase, intermediate states, bit ranges, padded blocks, IV and digest boundaries
are derived from constraints and exact natural bus balance. No cryptographic
PCS/fingerprint/Fiat-Shamir soundness claim is made by this module.
-/
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 NearSpecV3.SHA512
set_option maxRecDepth 65536

theorem sha384_multiblock_holds (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384MultiBlockAir n) pub tr) :
    Holds (sha384MultiBlockAir n).toAir pub tr :=
  (holdsP_iff_holds _ rfl _ _).mp h

theorem sha384_multiblock_table (n t : Nat) (ht : t<sha384PaddedLength n/128) :
    (sha384MultiBlockAir n).tables[t]'(by simpa [sha384MultiBlockAir] using ht)=sha384MultiBlockTable n t := by
  simp [sha384MultiBlockAir]

theorem sha384_multiblock_compression (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384MultiBlockAir n) pub tr) (t : Nat) (ht : t<sha384PaddedLength n/128) :
    sha512FeedForwardOutput (tr.cell t 79)=
      compress (sha512DecodedState (tr.cell t 0)) (sha512DecodedBlock (tr.cell t 0)) := by
  have ff := sha384_multiblock_ff_holds _ tr pub t (by simpa [sha384MultiBlockAir] using ht)
    n t (sha384_multiblock_table n t ht) (sha384_multiblock_holds n pub tr h)
  exact sha512_compression_sound _ _ pub 0 (by decide) rfl ff

theorem sha384_multiblock_height_phase (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384MultiBlockAir n) pub tr) (t : Nat) (ht : t<sha384PaddedLength n/128) :
    tr.height t=128 ∧ ∀ r, r<tr.height t → tr.cell t r 5231=if r=79 then 1 else 0 := by
  have ff := sha384_multiblock_ff_holds _ tr pub t (by simpa [sha384MultiBlockAir] using ht)
    n t (sha384_multiblock_table n t ht) (sha384_multiblock_holds n pub tr h)
  have constants := sha512_ff_constants_holds _ _ pub 0 (by decide) rfl ff
  refine ⟨sha512_constants_height _ _ pub 0 (by decide) rfl constants,?_⟩
  intro r hr
  have phase := sha512_constants_phase _ _ pub 0 (by decide) rfl constants r hr 79 (by decide)
  simpa [sha512CombinedProjection,eq_comm] using phase

/-- Exact natural count balance supplies an actual matching send. This uses
no fingerprint identity or equality of field-valued multiplicity sums. -/
theorem sha384_multiblock_receive_match (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384MultiBlockAir n) pub tr) {t r : Nat}
    (ht : t<(sha384MultiBlockAir n).tables.length) (hr : r<tr.height t)
    {i : Interaction} (hi : i ∈ (sha384MultiBlockAir n).tables[t]!.interactions)
    (hb : i.bus=0) (hs : i.send=false) (hm : i.multNat tr t r pub≠0) :
    ∃ t', t'<(sha384MultiBlockAir n).tables.length ∧ ∃ r', r'<tr.height t' ∧
      ∃ i' ∈ (sha384MultiBlockAir n).tables[t']!.interactions,
        i'.bus=0 ∧ i'.send=true ∧ i'.msgVal tr t' r' pub=i.msgVal tr t r pub ∧
        i'.multNat tr t' r' pub≠0 := by
  have positive := ZkFormal.Chacha.tableBusCount_pos hr hi hm
  rw [hb,hs] at positive
  have bound := ZkFormal.Chacha.busCount_go_ge tr pub 0 false (i.msgVal tr t r pub)
    (sha384MultiBlockAir n).tables 0 t ht
  simp only [Nat.zero_add] at bound
  have recv : busCount (sha384MultiBlockAir n).toAir tr pub 0 false (i.msgVal tr t r pub)≠0 := by
    unfold busCount
    omega
  have balance := (sha384_multiblock_holds n pub tr h).balance 0 (i.msgVal tr t r pub)
  have send : busCount (sha384MultiBlockAir n).toAir tr pub 0 true (i.msgVal tr t r pub)≠0 := by
    rwa [balance]
  obtain ⟨t',ht',hc⟩ := ZkFormal.Chacha.busCount_go_pos tr pub 0 true _ _ 0 send
  simp only [Nat.zero_add] at hc
  obtain ⟨r',hr',i',hi',hb',hs',msg,mult⟩ := ZkFormal.Chacha.exists_of_tableBusCount hc
  exact ⟨t',ht',r',hr',i',hi',hb',hs',msg,mult⟩

theorem sha384_multiblock_sender (n t : Nat) (i : Interaction)
    (hi : i ∈ (sha384MultiBlockTable n t).interactions) (hs : i.send=true) :
    t+1<sha384PaddedLength n/128 ∧
      i=⟨0,[.col 5231 false],sha384StateMessage t 8,true⟩ := by
  simp only [sha384MultiBlockTable,sha384BlockInteractions,List.mem_append] at hi
  rcases hi with hi | hi
  · split at hi
    · simp only [List.mem_singleton] at hi
      subst i
      contradiction
    · simp at hi
  · split at hi
    · exact ⟨by assumption,by simpa using hi⟩
    · simp at hi

theorem sha384_multiblock_state_message (tr : Trace Fp) (pub : List Fp)
    (t r tag offset : Nat) :
    (⟨0,[],sha384StateMessage tag offset,true⟩ : Interaction).msgVal tr t r pub=
      Fp.ofNat tag :: (List.range 8).flatMap (fun i => (List.range 4).map
        (fun limb => tr.cell t r (sha512FeedForwardBase i+offset+limb))) := by
  simp [Interaction.msgVal,sha384StateMessage,List.map_flatMap,List.map_map,
    Expr.eval,Expr.evalWith,rowEnv,Function.comp_def]
  rfl

/-- Adjacent states agree as exact lists of 32 field limbs. Tag injectivity
requires the explicit number-of-blocks bound; there is no field-count argument. -/
theorem sha384_multiblock_state_link (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384MultiBlockAir n) pub tr)
    (bound : sha384PaddedLength n/128<P) (t : Nat)
    (ht : t+1<sha384PaddedLength n/128) :
    (List.range 8).flatMap (fun i => (List.range 4).map
      (fun limb => tr.cell t 79 (sha512FeedForwardBase i+8+limb)))=
    (List.range 8).flatMap (fun i => (List.range 4).map
      (fun limb => tr.cell (t+1) 0 (sha512FeedForwardBase i+limb))) := by
  let receiver : Interaction := ⟨0,[.isFirst],sha384StateMessage t 0,false⟩
  have height := (sha384_multiblock_height_phase n pub tr h (t+1) ht).1
  have table : (sha384MultiBlockAir n).tables[t+1]! = sha384MultiBlockTable n (t+1) := by
    simp [sha384MultiBlockAir,ht]
  have member : receiver ∈ (sha384MultiBlockAir n).tables[t+1]!.interactions := by
    rw [table]
    simp [receiver,sha384MultiBlockTable,sha384BlockInteractions]
  have active : receiver.multNat tr (t+1) 0 pub≠0 := by
    simp [receiver,Interaction.multNat,Interaction.multNat.go,Expr.eval,Expr.evalWith,rowEnv]
  obtain ⟨t',ht',r',hr',sender,member',hb,hs,msg,active'⟩ :=
    sha384_multiblock_receive_match n pub tr h (by simpa [sha384MultiBlockAir] using ht)
      (by omega) member rfl rfl active
  have ht'' : t'<sha384PaddedLength n/128 := by simpa [sha384MultiBlockAir] using ht'
  have table' : (sha384MultiBlockAir n).tables[t']! = sha384MultiBlockTable n t' := by
    simp [sha384MultiBlockAir,ht'']
  rw [table'] at member'
  obtain ⟨_,senderEq⟩ := sha384_multiblock_sender n t' sender member' hs
  subst sender
  have phase := (sha384_multiblock_height_phase n pub tr h t' ht'').2 r' hr'
  have row : r'=79 := by
    by_cases yes : r'=79
    · exact yes
    · simp [Interaction.multNat,Interaction.multNat.go,Expr.eval,Expr.evalWith,rowEnv,
      phase,yes] at active'
      have impossible := congrArg Fp.toNat active'
      change 0=1 at impossible
      omega
  subst r'
  have messages : Fp.ofNat t' :: (List.range 8).flatMap (fun i => (List.range 4).map
      (fun limb => tr.cell t' 79 (sha512FeedForwardBase i+8+limb)))=
      Fp.ofNat t :: (List.range 8).flatMap (fun i => (List.range 4).map
      (fun limb => tr.cell (t+1) 0 (sha512FeedForwardBase i+limb))) := by
    simp [Interaction.msgVal,sha384StateMessage,List.map_flatMap,List.map_map,
      Expr.eval,Expr.evalWith,rowEnv,receiver,Function.comp_def] at msg
    simp only [List.cons.injEq]
    exact ⟨msg.1,msg.2⟩
  have tags := (List.cons.inj messages).1
  have equal : t'=t := by
    have values := congrArg Fp.toNat tags
    rw [Fp.toNat_ofNat,Fp.toNat_ofNat,Nat.mod_eq_of_lt (by omega : t'<P),
      Nat.mod_eq_of_lt (by omega : t<P)] at values
    exact values
  subst t'
  exact (List.cons.inj messages).2

theorem sha384_multiblock_boundary_zero (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384MultiBlockAir n) pub tr) (t : Nat)
    (ht : t<sha384PaddedLength n/128) (r : Nat) (hr : r<tr.height t)
    (e : Expr) (he : e ∈ sha384BlockBoundaryConstraints n t) : e.eval tr t r pub=0 := by
  have hc := h.constr t (by simpa [sha384MultiBlockAir] using ht) r hr e
  rw [sha384_multiblock_table n t ht] at hc
  exact hc (List.mem_append_right _ he)

theorem sha384_multiblock_byte_field (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384MultiBlockAir n) pub tr) (t : Nat)
    (ht : t<sha384PaddedLength n/128) (j : Nat) (hj : j<128) :
    (instructionBitExpr (sha512ScheduleWindowBase (j/8)+8*(7-j%8)) 8).eval tr t 0 pub=
      (sha384PaddedByte n (t*128+j)).eval tr t 0 pub := by
  have hv := sha384_multiblock_boundary_zero n pub tr h t ht 0 (Nat.two_pow_pos _)
    (sha384BlockByteConstraint n t j)
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨j,List.mem_range.mpr hj,rfl⟩)))
  change (1:Fp)*((instructionBitExpr (sha512ScheduleWindowBase (j/8)+8*(7-j%8)) 8).eval tr t 0 pub+
    -(sha384PaddedByte n (t*128+j)).eval tr t 0 pub)=0 at hv
  grind

theorem sha384_multiblock_digest_field (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384MultiBlockAir n) pub tr) (t : Nat)
    (ht : t<sha384PaddedLength n/128) (last : t+1=sha384PaddedLength n/128)
    (j : Nat) (hj : j<48) :
    (instructionBitExpr (sha512FeedForwardBase (j/8)+144+8*(7-j%8)) 8).eval tr t 79 pub=
      pub.getD (n+j) 0 := by
  have hp := sha384_multiblock_height_phase n pub tr h t ht
  have member : sha384DigestConstraint n j ∈ sha384BlockBoundaryConstraints n t := by
    apply List.mem_append_right
    simp only [last,ite_true]
    exact List.mem_map.mpr ⟨j,List.mem_range.mpr hj,rfl⟩
  have hv := sha384_multiblock_boundary_zero n pub tr h t ht 79 (by omega) _ member
  change tr.cell t 79 5231*((instructionBitExpr (sha512FeedForwardBase (j/8)+144+8*(7-j%8)) 8).eval tr t 79 pub+
    -pub.getD (n+j) 0)=0 at hv
  have phase := hp.2 79 (by omega)
  simp only [ite_true] at phase
  rw [phase] at hv
  grind

private theorem state_limb_ext (a b : Nat → Nat → Fp)
    (eq : (List.range 8).flatMap (fun i => (List.range 4).map (a i))=
      (List.range 8).flatMap (fun i => (List.range 4).map (b i)))
    (i j : Nat) (hi : i<8) (hj : j<4) : a i j=b i j := by
  have ic : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 := by omega
  have jc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
  simp only [show List.range 8=[0,1,2,3,4,5,6,7] from rfl,show List.range 4=[0,1,2,3] from rfl,List.append_nil,List.nil_append,List.flatMap_cons,
    List.flatMap_nil,List.map_cons,List.map_nil,List.cons_append,List.cons.injEq] at eq
  rcases ic with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases jc with rfl | rfl | rfl | rfl <;> grind

theorem sha384_multiblock_decoded_link (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384MultiBlockAir n) pub tr) (bound : sha384PaddedLength n/128<P)
    (t : Nat) (ht : t+1<sha384PaddedLength n/128) :
    sha512FeedForwardOutput (tr.cell t 79)=sha512DecodedState (tr.cell (t+1) 0) := by
  have link := sha384_multiblock_state_link n pub tr h bound t ht
  have ff := sha384_multiblock_ff_holds _ tr pub (t+1) (by simpa [sha384MultiBlockAir] using ht)
    n (t+1) (sha384_multiblock_table n (t+1) ht) (sha384_multiblock_holds n pub tr h)
  apply List.map_congr_left
  intro i hi
  have bounds := List.mem_range.mp hi
  have input := (sha512_ff_inputs _ _ pub 0 (by decide) rfl ff 0 i (Nat.two_pow_pos _) bounds).1
  simp only [sha512CombinedProjection,Nat.zero_add] at input
  rw [←input]
  have limb (j : Nat) (hj : j<4) := state_limb_ext _ _ link i j bounds hj
  have l0 := congrArg Fp.toNat (limb 0 (by decide))
  have l1 := congrArg Fp.toNat (limb 1 (by decide))
  have l2 := congrArg Fp.toNat (limb 2 (by decide))
  have l3 := congrArg Fp.toNat (limb 3 (by decide))
  simp only [instructionAdd64Word,sha512FeedForwardRow,Nat.add_assoc,Nat.zero_add,Nat.add_zero] at *
  rw [l0,l1,l2,l3]

theorem sha384_multiblock_message_bits (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384MultiBlockAir n) pub tr) (t : Nat)
    (ht : t<sha384PaddedLength n/128) (i bit : Nat) (hi : i<16) (hb : bit<64) :
    (tr.cell t 0 (sha512ScheduleWindowBase i+bit)).toNat≤1 := by
  have ff := sha384_multiblock_ff_holds _ tr pub t (by simpa [sha384MultiBlockAir] using ht)
    n t (sha384_multiblock_table n t ht) (sha384_multiblock_holds n pub tr h)
  have constants := sha512_ff_constants_holds _ _ pub 0 (by decide) rfl ff
  have combined := sha512_constants_combined_holds _ _ pub 0 (by decide) rfl constants
  have schedule := sha512_combined_schedule_holds _ _ pub 0 (by decide) rfl combined
  have bits := sha512_window_bit_boolean _ _ pub 0 (by decide) rfl schedule 0 (Nat.two_pow_pos _) i hi bit hb
  simpa only [sha512CombinedProjection,Nat.zero_add] using bits

theorem sha384_multiblock_byte_nat (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384MultiBlockAir n) pub tr) (t : Nat)
    (ht : t<sha384PaddedLength n/128) (j : Nat) (hj : j<128) :
    sha512WindowByte (tr.cell t 0) (sha512ScheduleWindowBase (j/8)) (7-j%8)=
      ((sha384PaddedByte n (t*128+j)).eval tr t 0 pub).toNat := by
  have field := sha384_multiblock_byte_field n pub tr h t ht j hj
  rw [sha512_public_bitexpr_eval,sha512_bit_expr_field] at field
  have bound := sha512_window_byte_bound (tr.cell t 0) (sha512ScheduleWindowBase (j/8)) (7-j%8)
    (by omega) (fun bit hb => sha384_multiblock_message_bits n pub tr h t ht (j/8) bit (by omega) hb)
  have small : sha512WindowByte (tr.cell t 0) (sha512ScheduleWindowBase (j/8)) (7-j%8)<P := by
    unfold P
    omega
  have value := congrArg Fp.toNat field
  rw [Fp.toNat_ofNat] at value
  change sha512WindowByte (tr.cell t 0) (sha512ScheduleWindowBase (j/8)) (7-j%8)%P=_ at value
  rwa [Nat.mod_eq_of_lt small] at value

theorem sha384_multiblock_iv_field (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384MultiBlockAir n) pub tr) (i limb : Nat) (hi : i<8) (hl : limb<4) :
    (instructionBitExpr (sha512FeedForwardInputBase i+16*limb) 16).eval tr 0 0 pub=
      Fp.ofNat ((sha384ChainIV.getD i 0)/65536^limb%65536) := by
  have ht : 0<sha384PaddedLength n/128 := by unfold sha384PaddedLength; omega
  have member : sha384IVConstraint i limb ∈ sha384BlockBoundaryConstraints n 0 := by
    apply List.mem_append_left
    apply List.mem_append_right
    simp only [ite_true]
    exact List.mem_flatMap.mpr ⟨i,List.mem_range.mpr hi,List.mem_map.mpr ⟨limb,List.mem_range.mpr hl,rfl⟩⟩
  have hv := sha384_multiblock_boundary_zero n pub tr h 0 ht 0 (Nat.two_pow_pos _) _ member
  change (1:Fp)*((instructionBitExpr (sha512FeedForwardInputBase i+16*limb) 16).eval tr 0 0 pub+
    -Fp.ofNat ((sha384ChainIV.getD i 0)/65536^limb%65536))=0 at hv
  grind

theorem sha384_multiblock_state_bits (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384MultiBlockAir n) pub tr) (t : Nat)
    (ht : t<sha384PaddedLength n/128) (i bit : Nat) (hi : i<8) (hb : bit<64) :
    (tr.cell t 0 (sha512FeedForwardInputBase i+bit)).toNat≤1 := by
  have ff := sha384_multiblock_ff_holds _ tr pub t (by simpa [sha384MultiBlockAir] using ht)
    n t (sha384_multiblock_table n t ht) (sha384_multiblock_holds n pub tr h)
  have add := sha512_ff_add_holds _ _ pub 0 (by decide) rfl ff 0 i (Nat.two_pow_pos _) hi
  have bound := sha512_add_word_bit _ add 0 bit (by decide) hb
  have first := sha512_ff_first_bit _ _ pub 0 (by decide) rfl ff i bit hi hb
  have bound' : (tr.cell t 0 (sha512FeedForwardBase i+16+bit)).toNat≤1 := by
    simpa only [sha512CombinedProjection,sha512FeedForwardRow,Nat.zero_add,Nat.mul_zero,
      Nat.add_zero,Nat.add_assoc] using bound
  have first' : tr.cell t 0 (sha512FeedForwardBase i+16+bit)=tr.cell t 0 (sha512FeedForwardInputBase i+bit) := by
    simpa only [sha512CombinedProjection,Nat.zero_add] using first
  rwa [first'] at bound'

private def sha384IVLimbs (i : Nat) : List Fp :=
  (List.range 4).map (fun limb => Fp.ofNat ((sha384ChainIV.getD i 0)/65536^limb%65536))

theorem sha384_multiblock_initial (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384MultiBlockAir n) pub tr) :
    sha512DecodedState (tr.cell 0 0)=sha384ChainIV := by
  have ht : 0<sha384PaddedLength n/128 := by unfold sha384PaddedLength; omega
  have ff := sha384_multiblock_ff_holds _ tr pub 0 (by simpa [sha384MultiBlockAir] using ht)
    n 0 (sha384_multiblock_table n 0 ht) (sha384_multiblock_holds n pub tr h)
  have word (i : Nat) (hi : i<8) :
      sha512FeedForwardVarsWord (sha512CombinedVars (tr.cell 0 0)) i=sha384ChainIV.getD i 0 := by
    have field (limb : Nat) (hl : limb<4) : (sha384IVLimbs i).getD limb 0=
        (instructionBitExpr (sha512FeedForwardInputBase i+16*limb) 16).evalWith (instructionAddEnv (tr.cell 0 0)) := by
      have eq := sha384_multiblock_iv_field n pub tr h i limb hi hl
      rw [sha512_public_bitexpr_eval] at eq
      rw [eq]
      simp [sha384IVLimbs,List.getD_eq_getElem?_getD,hl]
    have decoded := (sha512_public_word_decode (tr.cell 0 0) (sha384IVLimbs i) 0
      (sha512FeedForwardInputBase i)
      (fun bit hb => sha384_multiblock_state_bits n pub tr h 0 ht i bit hi hb)
      (by simpa only [Nat.zero_add] using field)).1
    have round := sha512_ff_round_holds _ _ pub 0 (by decide) rfl ff 0 (Nat.two_pow_pos _)
    have round' : sha512RoundHolds (sha512CombinedRoundRow (tr.cell 0 0)) := by
      simpa only [sha512CombinedProjection,Nat.zero_add] using round
    rw [sha512_ff_input_words _ round' i hi] at decoded
    rw [←decoded]
    have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  calc
    sha512DecodedState (tr.cell 0 0)=(List.range 8).map (fun i => sha384ChainIV.getD i 0) := by
      apply List.map_congr_left
      intro i hi
      exact word i (List.mem_range.mp hi)
    _ = sha384ChainIV := rfl

theorem sha384_multiblock_decoded_block_shape (row : Nat → Fp) :
    sha512DecodedBlock row=(List.range 128).map
      (fun j => sha512WindowByte row (sha512ScheduleWindowBase (j/8)) (7-j%8)) := by rfl

private theorem padded_byte_bound (message : List UInt8) (i : Nat)
    (hi : i<(pad (message.map UInt8.toNat)).length) :
    (pad (message.map UInt8.toNat)).getD i 0<256 := by
  have member (v : Nat) (hv : v ∈ pad (message.map UInt8.toNat)) : v<256 := by
    simp only [pad,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,List.mem_replicate] at hv
    rcases hv with ((hv | hv) | hv) | hv
    · obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hv
      exact x.toNat_lt
    · subst v; decide
    · rcases hv with ⟨_,rfl⟩; decide
    · obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hv
      exact x.toNat_lt
  have value := member _ (List.getElem_mem hi)
  simpa [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem,hi] using value

theorem sha384_multiblock_padded_block (message : List UInt8) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384MultiBlockAir message.length) pub tr)
    (pubBound : ∀ i,i<message.length → pub.getD i 0=Fp.ofNat ((message.map UInt8.toNat).getD i 0))
    (t : Nat) (ht : t<sha384PaddedLength message.length/128) :
    sha512DecodedBlock (tr.cell t 0)=((pad (message.map UInt8.toNat)).drop (128*t)).take 128 := by
  have size := sha384_padding_length (message.map UInt8.toNat)
  simp only [List.length_map] at size
  rw [sha384_multiblock_decoded_block_shape]
  apply List.ext_getElem
  · simp only [List.length_map,List.length_range,List.length_take,List.length_drop,size]
    unfold sha384PaddedLength at ht ⊢
    omega
  · intro j hj hj'
    have jbound : j<128 := by simpa using hj
    have pos : 128*t+j<sha384PaddedLength message.length := by
      unfold sha384PaddedLength at ht ⊢
      omega
    have actual := sha384_multiblock_byte_nat message.length pub tr h t ht j jbound
    have padded := sha384_padding_expr (message.map UInt8.toNat) tr t 0 pub
      (by simpa using pubBound) (128*t+j) (by simpa using pos)
    simp only [List.length_map] at padded
    rw [Nat.mul_comm t 128,padded,Fp.toNat_ofNat] at actual
    have bounded := padded_byte_bound message (128*t+j) (by omega)
    have small : (pad (message.map UInt8.toNat)).getD (128*t+j) 0<P := by unfold P;omega
    rw [Nat.mod_eq_of_lt small] at actual
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem (by omega),Option.getD_some] at actual
    simpa [Nat.add_comm] using actual

theorem sha384_multiblock_output_add (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384MultiBlockAir n) pub tr) (t i : Nat)
    (ht : t<sha384PaddedLength n/128) (hi : i<8) :
    instructionAdd64Holds (sha512FeedForwardRow (tr.cell t 79) i) := by
  have height := (sha384_multiblock_height_phase n pub tr h t ht).1
  have ff := sha384_multiblock_ff_holds _ tr pub t (by simpa [sha384MultiBlockAir] using ht)
    n t (sha384_multiblock_table n t ht) (sha384_multiblock_holds n pub tr h)
  have add := sha512_ff_add_holds _ _ pub 0 (by decide) rfl ff 79 i (by change 79<tr.height t;omega) hi
  simpa only [sha512CombinedProjection,Nat.zero_add] using add

theorem sha384_multiblock_digest_nat (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384MultiBlockAir n) pub tr) (t : Nat)
    (ht : t<sha384PaddedLength n/128) (last : t+1=sha384PaddedLength n/128)
    (j : Nat) (hj : j<48) :
    sha512WindowByte (sha512FeedForwardRow (tr.cell t 79) (j/8)) 144 (7-j%8)=
      (pub.getD (n+j) 0).toNat := by
  have add := sha384_multiblock_output_add n pub tr h t (j/8) ht (by omega)
  have bits (bit : Nat) (hb : bit<64) := sha512_add_word_bit _ add 8 bit (by decide) hb
  have bounded := sha512_window_byte_bound (sha512FeedForwardRow (tr.cell t 79) (j/8)) 144
    (7-j%8) (by omega) bits
  have field := sha384_multiblock_digest_field n pub tr h t ht last j hj
  rw [sha512_public_bitexpr_eval,sha512_bit_expr_field] at field
  have value := congrArg Fp.toNat field
  rw [Fp.toNat_ofNat] at value
  have small : sha512WindowByte (sha512FeedForwardRow (tr.cell t 79) (j/8)) 144 (7-j%8)<P := by
    unfold P;omega
  have value' : sha512WindowByte (sha512FeedForwardRow (tr.cell t 79) (j/8)) 144 (7-j%8)%P=(pub.getD (n+j) 0).toNat := by
    simpa only [sha512WindowByte,sha512FeedForwardRow,Nat.add_assoc] using value
  rwa [Nat.mod_eq_of_lt small] at value'

theorem sha384_multiblock_digest_bytes (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384MultiBlockAir n) pub tr) (t : Nat)
    (ht : t<sha384PaddedLength n/128) (last : t+1=sha384PaddedLength n/128) :
    ((digestBytes (sha512FeedForwardOutput (tr.cell t 79))).take 48).map UInt8.toNat=
      (List.range 48).map (fun j => (pub.getD (n+j) 0).toNat) := by
  have full : (digestBytes (sha512FeedForwardOutput (tr.cell t 79))).map UInt8.toNat=
      (List.range 8).flatMap (fun i => sha512WindowWordBytes (sha512FeedForwardRow (tr.cell t 79) i) 144) := by
    simp only [digestBytes,sha512FeedForwardOutput,List.flatMap_map,List.map_flatMap]
    apply congrArg List.flatten
    apply List.map_congr_left
    intro i hi
    have add := sha384_multiblock_output_add n pub tr h t i ht (List.mem_range.mp hi)
    rw [sha384_word_bytes,sha512_add_word_bits _ add 8 (by decide)]
    exact sha512_nat_word_bytes_bits _ 144 (fun bit hb => sha512_add_word_bit _ add 8 bit (by decide) hb)
  rw [List.map_take,full]
  change (List.range 48).map (fun j => sha512WindowByte (sha512FeedForwardRow (tr.cell t 79) (j/8)) 144 (7-j%8))=_
  apply List.map_congr_left
  intro j hj
  exact sha384_multiblock_digest_nat n pub tr h t ht last j (List.mem_range.mp hj)

theorem sha384_multiblock_blocks_step (message : List UInt8) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384MultiBlockAir message.length) pub tr)
    (pubBound : ∀ i,i<message.length → pub.getD i 0=Fp.ofNat ((message.map UInt8.toNat).getD i 0))
    (t k : Nat) (ht : t<sha384PaddedLength message.length/128) :
    blocks (k+1) (sha512DecodedState (tr.cell t 0)) ((pad (message.map UInt8.toNat)).drop (128*t))=
      blocks k (sha512FeedForwardOutput (tr.cell t 79)) ((pad (message.map UInt8.toNat)).drop (128*(t+1))) := by
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
  rw [←sha384_multiblock_padded_block message pub tr h pubBound t ht,
    ←sha384_multiblock_compression message.length pub tr h t ht] at step
  simpa only [List.drop_drop,Nat.mul_add,Nat.mul_one] using step

theorem sha384_multiblock_blocks_chain (message : List UInt8) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384MultiBlockAir message.length) pub tr)
    (pubBound : ∀ i,i<message.length → pub.getD i 0=Fp.ofNat ((message.map UInt8.toNat).getD i 0))
    (bound : sha384PaddedLength message.length/128<P) (k t : Nat)
    (ht : t+k<sha384PaddedLength message.length/128) :
    blocks (k+1) (sha512DecodedState (tr.cell t 0)) ((pad (message.map UInt8.toNat)).drop (128*t))=
      sha512FeedForwardOutput (tr.cell (t+k) 79) := by
  induction k generalizing t with
  | zero =>
    rw [sha384_multiblock_blocks_step message pub tr h pubBound t 0 (by omega)]
    rfl
  | succ k ih =>
    rw [sha384_multiblock_blocks_step message pub tr h pubBound t (k+1) (by omega),
      sha384_multiblock_decoded_link message.length pub tr h bound t (by omega)]
    have result := ih (t+1) (by omega)
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using result

/-- The complete compression chain is derived from the actual multiblock AIR,
including exact natural bus balance, public message bytes, padding and IV. -/
theorem sha384_multiblock_final_state (message : List UInt8) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384MultiBlockAir message.length) pub tr)
    (pubBound : ∀ i,i<message.length → pub.getD i 0=Fp.ofNat ((message.map UInt8.toNat).getD i 0))
    (bound : sha384PaddedLength message.length/128<P) :
    blocks (sha384PaddedLength message.length/128) sha384ChainIV (pad (message.map UInt8.toNat))=
      sha512FeedForwardOutput (tr.cell (sha384PaddedLength message.length/128-1) 79) := by
  have pos : 0<sha384PaddedLength message.length/128 := by unfold sha384PaddedLength;omega
  have result := sha384_multiblock_blocks_chain message pub tr h pubBound bound
    (sha384PaddedLength message.length/128-1) 0 (by omega)
  rw [sha384_multiblock_initial message.length pub tr h] at result
  simpa only [Nat.zero_add,Nat.mul_zero,List.drop_zero,Nat.sub_add_cancel (by omega : 1≤sha384PaddedLength message.length/128)] using result

/-- Public digest bytes equal SHA384 of the public message. This theorem is
semantic AIR soundness; it does not assert cryptographic proof-system soundness. -/
theorem sha384_multiblock_digest_sound (message : List UInt8) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384MultiBlockAir message.length) pub tr)
    (pubBound : ∀ i,i<message.length → pub.getD i 0=Fp.ofNat ((message.map UInt8.toNat).getD i 0))
    (bound : sha384PaddedLength message.length/128<P) :
    (sha384ChainDigest message).map UInt8.toNat=
      (List.range 48).map (fun j => (pub.getD (message.length+j) 0).toNat) := by
  have pos : 0<sha384PaddedLength message.length/128 := by unfold sha384PaddedLength;omega
  have final := sha384_multiblock_final_state message pub tr h pubBound bound
  have digest := sha384_multiblock_digest_bytes message.length pub tr h
    (sha384PaddedLength message.length/128-1) (by omega) (by omega)
  dsimp only [sha384ChainDigest]
  rw [sha384_padding_length,List.length_map,final]
  exact digest

end NearCompression
