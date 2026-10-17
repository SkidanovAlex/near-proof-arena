import NearCompression.SHA384HashDecodeSound
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 NearSpecV3.SHA512

/-- Exact ASCII domain separator used by pq384_primitives.Transcript.commit. -/
def sha384CommitTag : List UInt8 := [116, 114, 97, 110, 115, 99, 114, 105, 112, 116, 47, 99, 111, 109, 109, 105, 116]

def sha384TranscriptCommit (seed label payload : List UInt8) : List UInt8 :=
  sha384ChainDigest (sha384HashFrame sha384CommitTag [seed,label,payload])

/-- A typed operational update. The 48-byte seed invariant is checked here;
the Python primitive itself assumes its seed comes from an earlier SHA384 call. -/
def SHA384TranscriptCommitStep (seed label payload next : List UInt8) : Prop :=
  seed.length=48 ∧ next=sha384TranscriptCommit seed label payload

/-- Match actual decoded operands to caller wires before accepting the new seed.
This check does not itself implement recursive AIR wiring. -/
def sha384CommitOperandCheck (seed label payload message : List UInt8) : Bool :=
  seed.length==48 && sha384DecodeFrame message==some (sha384CommitTag,[seed,label,payload])

theorem sha384_commit_operand_check (seed label payload message : List UInt8) :
    sha384CommitOperandCheck seed label payload message=true ↔
      seed.length=48 ∧ sha384DecodeFrame message=some (sha384CommitTag,[seed,label,payload]) := by
  simp only [sha384CommitOperandCheck,Bool.and_eq_true,beq_iff_eq]

/-- The checker binds each position, including empty labels/payloads. A
permutation is accepted only when its actual byte values are equal in place. -/
theorem sha384_commit_operand_positions (seed label payload message tag : List UInt8)
    (parts : List (List UInt8))
    (check : sha384CommitOperandCheck seed label payload message=true)
    (decoded : sha384DecodeFrame message=some (tag,parts)) :
    tag=sha384CommitTag ∧ parts=[seed,label,payload] := by
  have eq := decoded.symm.trans ((sha384_commit_operand_check _ _ _ _).mp check).2
  have pair := Option.some.inj eq
  exact ⟨congrArg Prod.fst pair,congrArg Prod.snd pair⟩

/-- One actual commit operation: chunk AIR supplies compression correctness,
while a concrete operand check supplies domain separation and positional routing.
No hash injectivity or caller-supplied digest correctness premise. -/
theorem sha384_chunks_transcript_commit (nodes : List Nat) (payload : Nat→Nat→Fp)
    (total capacity chunks : Nat) (fanoutBits : Nat→Nat) (traces : Nat→Trace Fp)
    (positive : 0<capacity) (capacitySmall : capacity<P) (totalSmall : total<P)
    (coverage : total≤chunks*capacity) (nodeBound : ∀ i,i<nodes.length → nodes.getD i 0<total)
    (useBound : nodes.length<P)
    (claims : ∀ c,c<chunks → 0<chunkNodeCount total capacity c →
      HoldsP (sha384NodeChunkAir (capacity*c) (chunkNodeCount total capacity c) (fanoutBits c)
        (chunkOrdinals nodes capacity c).length) [] (traces c))
    (binding : SHA384ChunkUseBinding nodes payload capacity chunks traces)
    (message seed label data : ArenaCore.Bytes)
    (operands : sha384CommitOperandCheck seed label data message=true) (items : List (Nat × List Nat)) (final : List Nat)
    (declared : ∀ item,item∈items → item.1<nodes.length)
    (lengths : ∀ item,item∈items → item.2.length=128)
    (canonical : (items.map Prod.snd).flatten=pad (message.map UInt8.toNat))
    (messageWords : ∀ item,item∈items →
      sharedFlatWords (chunkGlobalUseRow nodes payload item.1) 35 16=words item.2)
    (wiring : chunkCallWiring nodes payload sha384ChainIV items final) :
    SHA384TranscriptCommitStep seed label data ((digestBytes final).take 48) := by
  have checks := (sha384_commit_operand_check seed label data message).mp operands
  refine ⟨checks.1,?_⟩
  exact sha384_chunks_decoded_call_sound nodes payload total capacity chunks fanoutBits traces
    positive capacitySmall totalSmall coverage nodeBound useBound claims binding
    message sha384CommitTag [seed,label,data] checks.2 items final declared lengths canonical messageWords wiring

end NearCompression
