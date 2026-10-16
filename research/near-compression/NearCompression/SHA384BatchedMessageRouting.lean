import NearCompression.SHA384BatchedPublicRouting
import NearCompression.SHA384BatchedPayloadField

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 NearSpecV3.SHA512

def sha384BatchMessageSegment (n : Nat) : PubSeg :=
  {bus:=4,send:=true,width:=64,countAt:=n+52+64*(sha384PaddedLength n/128),
    start:=n+52,indexBase:=some 0}

/-- A message receive at block start matches the public record with exactly
that block index. The explicit count bound prevents modular tag aliases. -/
theorem sha384_batch_message_record (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384BatchedAir n) pub tr) (bound : sha384PaddedLength n/128<P)
    (countBound : (sha384BatchMessageSegment n).count pub≤P)
    (block : Nat) (hb : block<sha384PaddedLength n/128) :
    (sha384BatchMessageSegment n).record pub block=
      sha384BatchMessage.map (fun e => e.eval tr 0 (80*block) pub) := by
  let i : Interaction := ⟨4,[sha384BatchPhase 0],sha384BatchMessage,false⟩
  have hi : i∈(sha384BatchedAir n).tables[0]!.interactions := by
    simp [i,sha384BatchedAir,sha384BatchCoreTable]
  have metadata:=sha384_batch_segment_metadata n pub tr h bound block 0 hb (by decide)
  simp only [Nat.add_zero] at metadata
  have phase:=metadata.2.2.2 0 (by decide)
  simp only [ite_true] at phase
  have hm : i.multNat tr 0 (80*block) pub≠0 := by
    simp [i,Interaction.multNat,Interaction.multNat.go,sha384BatchPhase,
      Expr.eval,Expr.evalWith,rowEnv,phase]
  obtain ⟨seg,hseg,bus,send,index,hindex,msg⟩:=sha384_batch_public_receive n pub tr h
    (by simp [sha384BatchedAir]) metadata.1 hi rfl (by decide) hm
  have segment : seg=sha384BatchMessageSegment n := by
    simp only [sha384BatchedAir,List.mem_cons,List.not_mem_nil,or_false] at hseg
    rcases hseg with rfl|rfl|rfl
    · simp [i] at bus
    · rfl
    · simp [i] at bus
  subst seg
  have tag : Fp.ofNat index=tr.cell 0 (80*block) 5233 := by
    have head:=congrArg (fun xs : List Fp => xs.getD 0 0) msg
    simpa [sha384BatchMessageSegment,PubSeg.record,Interaction.msgVal,i,
      sha384BatchMessage,sha384BatchTag,Expr.eval,Expr.evalWith,rowEnv,←Lean.Grind.Semiring.ofNat_eq_natCast,←Fp.ofNat_def] using head
  rw [metadata.2.2.1] at tag
  have same:=congrArg Fp.toNat tag
  rw [Fp.toNat_ofNat,Fp.toNat_ofNat,Nat.mod_eq_of_lt (by omega : index<P),
    Nat.mod_eq_of_lt (by omega : block<P)] at same
  subst index
  exact msg

/-- Removing the matched tag leaves exactly the ordered64 message limbs. -/
theorem sha384_batch_message_payload (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384BatchedAir n) pub tr) (bound : sha384PaddedLength n/128<P)
    (countBound : (sha384BatchMessageSegment n).count pub≤P)
    (block : Nat) (hb : block<sha384PaddedLength n/128) :
    (List.range 64).map (fun c => pub.getD (n+52+block*64+c) 0)=
      (List.range 16).flatMap (fun word => (List.range 4).map (fun limb =>
        (instructionBitExpr (sha512ScheduleWindowBase word+16*limb) 16).eval
          tr 0 (80*block) pub)) := by
  have eq:=sha384_batch_message_record n pub tr h bound countBound block hb
  have tail:=congrArg List.tail eq
  simpa [sha384BatchMessageSegment,PubSeg.record,PubSeg.startOffset,
    sha384BatchMessage,List.map_flatMap,List.map_map,Function.comp_def] using tail

/-- Each receiving schedule limb equals the corresponding public field value. -/
theorem sha384_batch_message_limb (n : Nat) (pub : List Fp) (tr : Trace Fp)
    (h : HoldsP (sha384BatchedAir n) pub tr) (bound : sha384PaddedLength n/128<P)
    (countBound : (sha384BatchMessageSegment n).count pub≤P)
    (block word limb : Nat) (hb : block<sha384PaddedLength n/128)
    (hw : word<16) (hl : limb<4) :
    pub.getD (n+52+block*64+(word*4+limb)) 0=
      (instructionBitExpr (sha512ScheduleWindowBase word+16*limb) 16).eval
        tr 0 (80*block) pub := by
  have eq:=sha384_batch_message_payload n pub tr h bound countBound block hb
  have atIndex:=congrArg (fun xs : List Fp => xs.getD (word*4+limb) 0) eq
  rw [sha384_flat_payload_index 16 4 _ (by intro i;simp) word limb hw hl 0] at atIndex
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map,
    List.getElem?_range (by omega : word*4+limb<64),List.getElem?_range hl,
    Option.map_some,Option.getD_some] at atIndex
  exact atIndex

end NearCompression
