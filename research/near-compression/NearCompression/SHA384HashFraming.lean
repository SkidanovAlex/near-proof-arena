import NearCompression.SHA384ChunkCallChain
import NearSpec.ClaimCodec
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 NearSpecV3.SHA512

def sha384HashPrefix : List UInt8 := [78, 69, 65, 82, 45, 80, 81, 51, 56, 52, 45, 80, 82, 73, 77, 73, 84, 73, 86, 69, 83, 45, 86, 49]

def sha384FramedParts (parts : List (List UInt8)) : List UInt8 :=
  parts.flatMap (fun part=>NearSpec.leN 8 part.length++part)

def sha384HashFrame (tag : List UInt8) (parts : List (List UInt8)) : List UInt8 :=
  sha384HashPrefix ++ NearSpec.leN 4 tag.length ++ tag ++
    NearSpec.leN 4 parts.length ++ sha384FramedParts parts

/-- Bounds exactly mirror Python's u32 framing and checked u64 part lengths. -/
def SHA384HashFrameFits (tag : List UInt8) (parts : List (List UInt8)) : Prop :=
  tag.length<2^32 ∧ parts.length<2^32 ∧ ∀ part,part∈parts → part.length<2^64

theorem sha384_hash_prefix_length : sha384HashPrefix.length=24 := by decide

theorem sha384_framed_parts_length (parts : List (List UInt8)) :
    (sha384FramedParts parts).length=8*parts.length+(parts.map List.length).sum := by
  induction parts with
  | nil => rfl
  | cons p ps ih =>
    simp only [sha384FramedParts,List.flatMap_cons,List.length_append,NearSpec.leN_length,
      List.length_cons,List.map_cons,List.sum_cons] at *
    omega

theorem sha384_hash_frame_length (tag : List UInt8) (parts : List (List UInt8)) :
    (sha384HashFrame tag parts).length=32+tag.length+8*parts.length+(parts.map List.length).sum := by
  simp only [sha384HashFrame,List.length_append,sha384_hash_prefix_length,
    NearSpec.leN_length,sha384_framed_parts_length]
  omega

theorem sha384_hash_frame_lengths_exact (tag : List UInt8) (parts : List (List UInt8))
    (fits : SHA384HashFrameFits tag parts) :
    NearSpec.leNat (NearSpec.leN 4 tag.length)=tag.length ∧
    NearSpec.leNat (NearSpec.leN 4 parts.length)=parts.length ∧
    ∀ part,part∈parts → NearSpec.leNat (NearSpec.leN 8 part.length)=part.length := by
  refine ⟨NearSpec.leNat_leN _ _ ?_,NearSpec.leNat_leN _ _ ?_,?_⟩
  · exact fits.1
  · exact fits.2.1
  · intro part hp
    exact NearSpec.leNat_leN _ _ (fits.2.2 part hp)

/-- A message-identity interface suffices to transfer any chunk-derived digest
relation to canonical hash_parts bytes. Operand provenance remains a premise. -/
theorem sha384_hash_frame_digest_transfer (tag : List UInt8) (parts : List (List UInt8))
    (message digest : List UInt8) (framing : message=sha384HashFrame tag parts)
    (semantic : digest=sha384ChainDigest message) :
    digest=sha384ChainDigest (sha384HashFrame tag parts) := by
  rw [←framing]
  exact semantic
end NearCompression
