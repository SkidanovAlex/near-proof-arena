import NearCompression.SHA384HashFrameDecoder
namespace NearCompression
open NearSpec ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 NearSpecV3.SHA512

private theorem takeN_sound (n : Nat) (bs head tail : Bytes)
    (h : takeN n bs=some (head,tail)) : head.length=n ∧ bs=head++tail := by
  induction n generalizing bs head with
  | zero => simp only [takeN,Option.some.injEq,Prod.mk.injEq] at h;rcases h with ⟨rfl,rfl⟩;simp
  | succ n ih =>
    cases bs with
    | nil => simp [takeN] at h
    | cons b bs =>
      cases step : takeN n bs with
      | none => simp [takeN,step] at h
      | some pair =>
        rcases pair with ⟨hh,tt⟩
        simp only [takeN,step,Option.map_some,Option.some.injEq,Prod.mk.injEq] at h
        rcases h with ⟨rfl,rfl⟩
        obtain ⟨len,eq⟩ := ih bs hh step
        simp [len,eq]

private theorem leN_decode (bs : Bytes) : leN bs.length (leNat bs)=bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    have bound := b.toNat_lt
    have modulo : (b.toNat+256*leNat bs)%256=b.toNat := by omega
    have div : (b.toNat+256*leNat bs)/256=leNat bs := by omega
    simp only [List.length_cons,NearSpec.leNat,leN,modulo,div,ih,UInt8.ofNat_toNat]

private theorem readLE_sound (n : Nat) (bs tail : Bytes) (value : Nat)
    (h : readLE n bs=some (value,tail)) : bs=leN n value++tail := by
  cases step : takeN n bs with
  | none => simp [readLE,step] at h
  | some pair =>
    rcases pair with ⟨head,rest⟩
    simp only [readLE,step,Option.map_some,Option.some.injEq,Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩
    obtain ⟨len,eq⟩ := takeN_sound n bs head rest step
    rw [eq,←len,leN_decode]

theorem sha384_read_parts_sound (n : Nat) (bs tail : Bytes) (parts : List Bytes)
    (h : sha384ReadParts n bs=some (parts,tail)) :
    parts.length=n ∧ bs=sha384FramedParts parts++tail := by
  induction n generalizing bs parts with
  | zero =>
    simp only [sha384ReadParts,Option.some.injEq,Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩
    simp [sha384FramedParts]
  | succ n ih =>
    cases sizeStep : readLE 8 bs with
    | none => simp [sha384ReadParts,sizeStep] at h
    | some pair =>
      rcases pair with ⟨size,rest⟩
      cases partStep : takeN size rest with
      | none => simp [sha384ReadParts,sizeStep,partStep] at h
      | some pair =>
        rcases pair with ⟨part,more⟩
        cases tailStep : sha384ReadParts n more with
        | none => simp [sha384ReadParts,sizeStep,partStep,tailStep] at h
        | some pair =>
          rcases pair with ⟨ps,last⟩
          simp [sha384ReadParts,sizeStep,partStep,tailStep] at h
          rcases h with ⟨rfl,rfl⟩
          obtain ⟨len,eq⟩ := ih more ps tailStep
          obtain ⟨plen,peq⟩ := takeN_sound size rest part more partStep
          have sizeEq := readLE_sound 8 bs rest size sizeStep
          constructor
          · simp [len]
          · simp only [sha384FramedParts,List.flatMap_cons,List.append_assoc]
            rw [sizeEq,peq,←plen]
            simpa only [sha384FramedParts,List.append_assoc] using congrArg (fun x=>leN 8 part.length++part++x) eq
theorem sha384_read_frame_sound (bs tail tag : Bytes) (parts : List Bytes)
    (h : sha384ReadFrame bs=some ((tag,parts),tail)) :
    bs=sha384HashFrame tag parts++tail := by
  cases pfxStep : takeN 24 bs with
  | none => simp [sha384ReadFrame,pfxStep] at h
  | some pair =>
    rcases pair with ⟨pfx,r0⟩
    by_cases same : pfx=sha384HashPrefix
    · subst pfx
      cases lenStep : readLE 4 r0 with
      | none => simp [sha384ReadFrame,pfxStep,lenStep] at h
      | some pair =>
        rcases pair with ⟨size,r1⟩
        cases tagStep : takeN size r1 with
        | none => simp [sha384ReadFrame,pfxStep,lenStep,tagStep] at h
        | some pair =>
          rcases pair with ⟨got,r2⟩
          cases countStep : readLE 4 r2 with
          | none => simp [sha384ReadFrame,pfxStep,lenStep,tagStep,countStep] at h
          | some pair =>
            rcases pair with ⟨count,r3⟩
            cases partsStep : sha384ReadParts count r3 with
            | none => simp [sha384ReadFrame,pfxStep,lenStep,tagStep,countStep,partsStep] at h
            | some pair =>
              rcases pair with ⟨found,last⟩
              simp [sha384ReadFrame,pfxStep,lenStep,tagStep,countStep,partsStep] at h
              rcases h with ⟨⟨rfl,rfl⟩,rfl⟩
              have a := (takeN_sound 24 bs sha384HashPrefix r0 pfxStep).2
              have b := readLE_sound 4 r0 r1 size lenStep
              have c := takeN_sound size r1 got r2 tagStep
              have d := readLE_sound 4 r2 r3 count countStep
              have e := sha384_read_parts_sound count r3 last found partsStep
              simp only [sha384HashFrame,a,b,c.2,d,e.2,←c.1,←e.1,List.append_assoc]
    · simp [sha384ReadFrame,pfxStep,same] at h

/-- Successful strict decoding forces the complete supplied bytes to be the
canonical encoding of the returned tuple, without an encoder-origin premise. -/
theorem sha384_decode_frame_sound (bs tag : Bytes) (parts : List Bytes)
    (h : sha384DecodeFrame bs=some (tag,parts)) : bs=sha384HashFrame tag parts := by
  cases parsed : sha384ReadFrame bs with
  | none => simp [sha384DecodeFrame,parsed] at h
  | some pair =>
    rcases pair with ⟨⟨t,ps⟩,rest⟩
    by_cases empty : rest=[]
    · subst rest
      simp [sha384DecodeFrame,parsed] at h
      rcases h with ⟨rfl,rfl⟩
      simpa only [List.append_nil] using sha384_read_frame_sound bs [] t ps parsed
    · simp [sha384DecodeFrame,parsed,empty] at h

/-- Actual chunk AIR claims plus a successful typed frame decode imply the
SHA384 digest for exactly that caller tuple. No hash injectivity, assumed
compression fact, or assumed supplied-message/encoded-message equality. -/
theorem sha384_chunks_decoded_call_sound (nodes : List Nat) (payload : Nat→Nat→Fp)
    (total capacity chunks : Nat) (fanoutBits : Nat→Nat) (traces : Nat→Trace Fp)
    (positive : 0<capacity) (capacitySmall : capacity<P) (totalSmall : total<P)
    (coverage : total≤chunks*capacity) (nodeBound : ∀ i,i<nodes.length → nodes.getD i 0<total)
    (useBound : nodes.length<P)
    (claims : ∀ c,c<chunks → 0<chunkNodeCount total capacity c →
      HoldsP (sha384NodeChunkAir (capacity*c) (chunkNodeCount total capacity c) (fanoutBits c)
        (chunkOrdinals nodes capacity c).length) [] (traces c))
    (binding : SHA384ChunkUseBinding nodes payload capacity chunks traces)
    (message tag : ArenaCore.Bytes) (parts : List ArenaCore.Bytes)
    (decoded : sha384DecodeFrame message=some (tag,parts)) (items : List (Nat × List Nat)) (final : List Nat)
    (declared : ∀ item,item∈items → item.1<nodes.length)
    (lengths : ∀ item,item∈items → item.2.length=128)
    (canonical : (items.map Prod.snd).flatten=pad (message.map UInt8.toNat))
    (messageWords : ∀ item,item∈items →
      sharedFlatWords (chunkGlobalUseRow nodes payload item.1) 35 16=words item.2)
    (wiring : chunkCallWiring nodes payload sha384ChainIV items final) :
    (digestBytes final).take 48=sha384ChainDigest (sha384HashFrame tag parts) := by
  have semantic := sha384_chunks_call_sound nodes payload total capacity chunks fanoutBits traces
    positive capacitySmall totalSmall coverage nodeBound useBound claims binding message items final
    declared lengths canonical messageWords wiring
  rw [sha384_decode_frame_sound message tag parts decoded] at semantic
  exact semantic

end NearCompression
