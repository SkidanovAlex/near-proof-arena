import ZkFormal.Stark.Field
import ZkFormal.Algebra.Fp8
import ZkFormal.Algebra.Decode
import ZkFormal.Stark.InstanceDefs

/-!
# ZkFormal.Stark.Instance — `StarkField` for L1's BabyBear and `Fp8`

The deployed instantiation: `F = ZkFormal.Algebra.Fp`, `K = ZkFormal.Algebra.Fp8`.
-/

namespace ZkFormal.Stark

open ZkFormal.Algebra

/-- The deployed verifier's field pair. -/
abbrev BB := Fp
abbrev BB8 := Fp8

end ZkFormal.Stark
