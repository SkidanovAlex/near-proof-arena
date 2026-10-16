import NearCompression.SHA384DirectBalance

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2

/-- The direct committed-input AIR refines standard SHA384 on its actual
input bytes. Canonical digest/IV/count layout and all block-count replacement
obligations are discharged; no padding, message-routing, or compression
correctness premise remains. This is semantic HoldsP refinement, not a
cryptographic acceptance/extraction theorem. -/
theorem sha384_direct_message_sound (n : Nat) (fixed : List (Nat × Nat))
    (digest : List UInt8) (size : digest.length=48) (tr : Trace Fp)
    (h : HoldsP (sha384DirectInputAir n fixed) (sha384DirectPublic digest) tr)
    (bound : sha384PaddedLength n/128<P) :
    sha384ChainDigest (sha384DirectMessageBytes n (sha384DirectPublic digest) tr)=digest := by
  let message:=sha384DirectMessageBytes n (sha384DirectPublic digest) tr
  have length : message.length=n:=sha384_direct_message_bytes_length n _ tr
  have bound' : sha384PaddedLength message.length/128<P := by rw [length];exact bound
  have fits:=sha384_direct_batched_public_fit message digest size bound'
  rw [length] at fits
  have projected:=sha384_direct_project n fixed (sha384DirectPublic digest)
    (sha384BatchedPublic message digest) tr h fits
    (sha384_direct_public_counts n fixed digest size tr h bound)
  have old : HoldsP (sha384BatchedAir message.length) (sha384BatchedPublic message digest) tr := by
    rw [length];exact projected
  exact sha384_batched_message_sound message digest size tr old bound'

end NearCompression
