import NearCompression.SHA384HashFraming
namespace NearCompression
open NearSpec

/-- Count-directed parser. Each part consumes a checked eight-byte length and
exactly that many bytes. This is a semantic parser, not a resource-bound claim. -/
def sha384ReadParts : Nat → Parser (List Bytes)
  | 0 => fun bs=>some ([],bs)
  | n+1 => fun bs=>do
      let (size,rest) ← readLE 8 bs
      let (part,rest) ← takeN size rest
      let (parts,rest) ← sha384ReadParts n rest
      pure (part::parts,rest)

def sha384ReadFrame : Parser (Bytes × List Bytes) := fun bs=>do
  let (pfx,rest) ← takeN 24 bs
  if pfx≠sha384HashPrefix then none else do
    let (size,rest) ← readLE 4 rest
    let (tag,rest) ← takeN size rest
    let (count,rest) ← readLE 4 rest
    let (parts,rest) ← sha384ReadParts count rest
    pure ((tag,parts),rest)

/-- Complete decoding rejects an unknown prefix, truncation or trailing bytes.
The theorem below only concerns bounded canonical encoder output. -/
def sha384DecodeFrame (bs : Bytes) : Option (Bytes × List Bytes) := do
  let (value,rest) ← sha384ReadFrame bs
  if rest=[] then some value else none

theorem sha384_read_parts_append (parts : List Bytes) (rest : Bytes)
    (bounds : ∀ part,part∈parts → part.length<2^64) :
    sha384ReadParts parts.length (sha384FramedParts parts++rest)=some (parts,rest) := by
  induction parts with
  | nil => rfl
  | cons p ps ih =>
    have hp : p.length<256^8 := bounds p (by simp)
    have ht := ih (by intro x hx;exact bounds x (by simp [hx]))
    simp only [sha384FramedParts,List.flatMap_cons,List.length_cons,List.append_assoc,sha384ReadParts]
    rw [readLE_append 8 _ _ hp]
    dsimp only [Bind.bind,Option.bind]
    rw [takeN_append p]
    dsimp only [Bind.bind,Option.bind]
    unfold sha384FramedParts at ht
    rw [ht]
    rfl

theorem sha384_read_frame_append (tag : Bytes) (parts : List Bytes) (rest : Bytes)
    (fits : SHA384HashFrameFits tag parts) :
    sha384ReadFrame (sha384HashFrame tag parts++rest)=some ((tag,parts),rest) := by
  have pfx : takeN 24 (sha384HashPrefix ++
      (leN 4 tag.length ++ tag ++ leN 4 parts.length ++ sha384FramedParts parts ++ rest))=
      some (sha384HashPrefix,leN 4 tag.length ++ tag ++ leN 4 parts.length ++ sha384FramedParts parts ++ rest) := by
    rw [←sha384_hash_prefix_length]
    exact takeN_append _ _
  simp only [sha384ReadFrame,sha384HashFrame,List.append_assoc]
  rw [show takeN 24 (sha384HashPrefix ++ (leN 4 tag.length ++ (tag ++ (leN 4 parts.length ++ (sha384FramedParts parts ++ rest)))))=
      some (sha384HashPrefix,leN 4 tag.length ++ (tag ++ (leN 4 parts.length ++ (sha384FramedParts parts ++ rest)))) from by
        simpa only [List.append_assoc] using pfx]
  simp only [Bind.bind,Option.bind,ne_eq,not_true_eq_false,ite_false]
  rw [readLE_append 4 _ _ fits.1]
  dsimp only [Bind.bind,Option.bind]
  rw [takeN_append tag]
  dsimp only [Bind.bind,Option.bind]
  rw [readLE_append 4 _ _ fits.2.1]
  dsimp only [Bind.bind,Option.bind]
  rw [sha384_read_parts_append parts rest fits.2.2]
  rfl

theorem sha384_decode_frame_encode (tag : Bytes) (parts : List Bytes)
    (fits : SHA384HashFrameFits tag parts) :
    sha384DecodeFrame (sha384HashFrame tag parts)=some (tag,parts) := by
  have parsed := sha384_read_frame_append tag parts [] fits
  simp only [List.append_nil] at parsed
  simp only [sha384DecodeFrame,parsed,Bind.bind,Option.bind,ite_true]

theorem sha384_hash_frame_injective (tag1 tag2 : Bytes) (parts1 parts2 : List Bytes)
    (fit1 : SHA384HashFrameFits tag1 parts1) (fit2 : SHA384HashFrameFits tag2 parts2)
    (encoded : sha384HashFrame tag1 parts1=sha384HashFrame tag2 parts2) :
    tag1=tag2 ∧ parts1=parts2 := by
  have eq := congrArg sha384DecodeFrame encoded
  rw [sha384_decode_frame_encode _ _ fit1,sha384_decode_frame_encode _ _ fit2] at eq
  have pairs := Option.some.inj eq
  exact ⟨congrArg Prod.fst pairs,congrArg Prod.snd pairs⟩
theorem sha384_decode_frame_trailing (tag : Bytes) (parts : List Bytes) (extra : Bytes)
    (fits : SHA384HashFrameFits tag parts) (nonempty : extra≠[]) :
    sha384DecodeFrame (sha384HashFrame tag parts++extra)=none := by
  simp only [sha384DecodeFrame,sha384_read_frame_append tag parts extra fits,
    Bind.bind,Option.bind,ite_eq_right nonempty]

end NearCompression
