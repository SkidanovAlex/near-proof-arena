import NearCompression.SHA384BatchedMessage
import NearCompression.SHA384BatchedTraceBytes

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2

/-- Full semantic correctness of the batched80 SHA384 AIR with its canonical
public expansion. All message decoding, phase/reset behavior, round constants,
compression arithmetic, natural bus routing, IV and digest binding are derived.
Cryptographic proof acceptance implying HoldsP remains a separate obligation. -/
theorem sha384_batched_message_sound (message digest : List UInt8) (size : digest.length=48)
    (tr : Trace Fp)
    (h : HoldsP (sha384BatchedAir message.length) (sha384BatchedPublic message digest) tr)
    (bound : sha384PaddedLength message.length/128<P) :
    sha384ChainDigest message=digest :=
  sha384_batched_message_sound_of_decoded message digest size tr h bound
    (sha384_batched_decoded_block message digest size tr h bound)

end NearCompression
