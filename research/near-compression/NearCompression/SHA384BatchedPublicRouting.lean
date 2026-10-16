import NearCompression.SHA384BatchedRouting
import NearCompression.SHA384BatchedPublic

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 NearSpecV3.SHA512
set_option maxRecDepth 65536

/-- All dynamic sends are internal state/endpoint buses0..3. -/
theorem sha384_batch_no_high_sender (n t : Nat) (ht : t<(sha384BatchedAir n).tables.length)
    (i : Interaction) (hi : i∈(sha384BatchedAir n).tables[t]!.interactions) (hb : 4≤i.bus) : i.send=false := by
  have cases : t=0 ∨ t=1 := by simp only [sha384BatchedAir,List.length_cons,List.length_nil] at ht;omega
  rcases cases with rfl | rfl
  · simp only [sha384BatchedAir,List.getElem!_cons_zero,sha384BatchCoreTable,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl <;> simp_all
  · simp only [sha384BatchedAir,List.getElem!_cons_succ,List.getElem!_cons_zero,sha384EndpointTable,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> simp_all

/-- Public bus records are recovered from exact natural balance. This interface
covers both padded-block input(bus4) and initial-IV input(bus5). -/
theorem sha384_batch_public_receive (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384BatchedAir n) pub tr) {t r : Nat}
    (ht : t<(sha384BatchedAir n).tables.length) (hr : r<tr.height t)
    {i : Interaction} (hi : i∈(sha384BatchedAir n).tables[t]!.interactions)
    (hs : i.send=false) (hb : 4≤i.bus) (hm : i.multNat tr t r pub≠0) :
    ∃ seg∈(sha384BatchedAir n).pubSegs,seg.bus=i.bus ∧ seg.send=true ∧
      ∃ index,index<seg.count pub ∧ seg.record pub index=i.msgVal tr t r pub := by
  have positive := ZkFormal.Chacha.tableBusCount_pos hr hi hm
  rw [hs] at positive
  have lower := ZkFormal.Chacha.busCount_go_ge tr pub i.bus false (i.msgVal tr t r pub)
    (sha384BatchedAir n).tables 0 t ht
  simp only [Nat.zero_add] at lower
  have recv : busCount (sha384BatchedAir n).toAir tr pub i.bus false (i.msgVal tr t r pub)≠0 := by unfold busCount;omega
  have sendZero : busCount (sha384BatchedAir n).toAir tr pub i.bus true (i.msgVal tr t r pub)=0 := by
    by_cases zero : busCount (sha384BatchedAir n).toAir tr pub i.bus true (i.msgVal tr t r pub)=0
    · exact zero
    · obtain ⟨t',ht',hc⟩ := ZkFormal.Chacha.busCount_go_pos tr pub i.bus true _ _ 0 zero
      simp only [Nat.zero_add] at hc
      obtain ⟨r',hr',i',hi',bus,send,msg,mult⟩ := ZkFormal.Chacha.exists_of_tableBusCount hc
      have no := sha384_batch_no_high_sender n t' ht' i' hi' (by omega)
      simp_all
  have balance := h.balance i.bus (i.msgVal tr t r pub)
  rw [sendZero,Nat.zero_add] at balance
  have pubPositive : pubCount (sha384BatchedAir n) pub i.bus true (i.msgVal tr t r pub)≠0 := by omega
  unfold pubCount at pubPositive
  have nonempty := mt List.length_eq_zero_iff.mpr pubPositive
  obtain ⟨x,hx⟩ := List.exists_mem_of_ne_nil _ nonempty
  have filtered := List.mem_filter.mp hx
  have eq := of_decide_eq_true filtered.2
  obtain ⟨seg,hseg,y⟩ := List.mem_flatMap.mp filtered.1
  obtain ⟨record,hrecord,rfl⟩ := List.mem_map.mp y
  obtain ⟨index,hindex,rfl⟩ := List.mem_map.mp hrecord
  have data := Prod.mk.inj eq
  have tail := Prod.mk.inj data.2
  exact ⟨seg,hseg,data.1,tail.1,index,List.mem_range.mp hindex,tail.2⟩

def sha384BatchIVSegment (n : Nat) : PubSeg :=
  {bus:=5,send:=true,width:=32,countAt:=n+88+64*(sha384PaddedLength n/128),start:=n+56+64*(sha384PaddedLength n/128)}

/-- The initial state's limbs are the unique IV public record. Only the public
count premise is supplied; the receive-to-record match is proved from HoldsP. -/
theorem sha384_batch_iv_record (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384BatchedAir n) pub tr)
    (count : (sha384BatchIVSegment n).count pub=1) :
    sha384CoreLimbs (tr.cell 0 0) false=(sha384BatchIVSegment n).record pub 0 := by
  let i : Interaction := ⟨5,[.isFirst],(sha384CoreStateMessage 0 false).tail,false⟩
  have hi : i∈(sha384BatchedAir n).tables[0]!.interactions := by simp [i,sha384BatchedAir,sha384BatchCoreTable]
  have hm : i.multNat tr 0 0 pub≠0 := by simp [i,Interaction.multNat,Interaction.multNat.go,Expr.eval,Expr.evalWith,rowEnv]
  obtain ⟨seg,hseg,bus,send,index,hindex,msg⟩ := sha384_batch_public_receive n pub tr h
    (by simp [sha384BatchedAir]) (Nat.two_pow_pos _) hi rfl (by decide) hm
  have segment : seg=sha384BatchIVSegment n := by
    simp only [sha384BatchedAir,List.mem_cons,List.not_mem_nil,or_false] at hseg
    rcases hseg with rfl | rfl | rfl
    · simp [i] at bus
    · simp [i] at bus
    · rfl
  subst seg
  rw [count] at hindex
  have zero : index=0 := by omega
  subst index
  have eval : i.msgVal tr 0 0 pub=sha384CoreLimbs (tr.cell 0 0) false := by
    simp only [i,Interaction.msgVal,sha384CoreStateMessage,List.tail_cons,List.map_flatMap,List.map_map,
      Function.comp_def,sha512_public_bitexpr_eval,sha384CoreLimbs]
  exact (msg.trans eval).symm

private def sha384BatchFixedIVLimbs (i : Nat) : List Fp :=
  (List.range 4).map (fun limb => Fp.ofNat ((sha384ChainIV.getD i 0)/65536^limb%65536))

/-- IV composition with explicit public layout premises. No caller routing or
trace-state premise is assumed. Canonical public-layout lemmas discharge these. -/
theorem sha384_batch_initial (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384BatchedAir n) pub tr) (bound : sha384PaddedLength n/128<P)
    (count : (sha384BatchIVSegment n).count pub=1)
    (content : (sha384BatchIVSegment n).record pub 0=sha384BatchIVPayload.map Fp.ofNat) :
    sha512DecodedState (tr.cell 0 0)=sha384ChainIV := by
  have record := (sha384_batch_iv_record n pub tr h count).trans content
  simp only [sha384BatchIVPayload,List.map_flatMap,List.map_map,Function.comp_def] at record
  have ht : 0<sha384PaddedLength n/128 := by unfold sha384PaddedLength;omega
  have round' := sha384_batch_round_holds n pub tr h bound 0 0 ht (by decide)
  simp only [Nat.mul_zero,Nat.zero_add] at round'
  have word (i : Nat) (hi : i<8) :
      sha512FeedForwardVarsWord (sha512CombinedVars (tr.cell 0 0)) i=sha384ChainIV.getD i 0 := by
    have field (limb : Nat) (hl : limb<4) : (sha384BatchFixedIVLimbs i).getD limb 0=
        (instructionBitExpr (sha512FeedForwardInputBase i+16*limb) 16).evalWith (instructionAddEnv (tr.cell 0 0)) := by
      have eq := sha384_endpoint_limb_ext _ _ record i limb hi hl
      simp only [Bool.false_eq_true,ite_false] at eq
      rw [eq]
      simp [sha384BatchFixedIVLimbs,List.getD_eq_getElem?_getD,hl]
    have decoded := (sha512_public_word_decode (tr.cell 0 0) (sha384BatchFixedIVLimbs i) 0
      (sha512FeedForwardInputBase i)
      (fun bit hb => sha384_endpoint_state_bits _ round' false i bit hi hb)
      (by simpa only [Nat.zero_add] using field)).1
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


end NearCompression
