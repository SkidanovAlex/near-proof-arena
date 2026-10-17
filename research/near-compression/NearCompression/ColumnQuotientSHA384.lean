import NearCompression.ColumnQuotient
import NearCompression.SHA384MultiBlockSemantics

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2

/-- A quotient proof retains the full original SHA384 AIR semantics. The
column map can be arbitrary because every original obligation is rewritten;
no equality between old and new commitment roots is asserted. -/
theorem sha384_quotient_digest_sound (message : List UInt8) (pub : List Fp)
    (f : Nat → Nat → Nat) (width : Nat → Nat) (tr : Trace Fp)
    (h : HoldsP (quotientAir f width (sha384MultiBlockAir message.length)) pub tr)
    (pubBound : ∀ i,i<message.length → pub.getD i 0=Fp.ofNat ((message.map UInt8.toNat).getD i 0))
    (bound : sha384PaddedLength message.length/128<P) :
    (sha384ChainDigest message).map UInt8.toNat=
      (List.range 48).map (fun j => (pub.getD (message.length+j) 0).toNat) :=
  sha384_multiblock_digest_sound message pub (quotientTrace f tr)
    (quotient_holdsP f width _ tr pub h) pubBound bound

end NearCompression
