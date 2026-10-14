import ZkFormal.Algebra.Fp
import ZkFormal.Algebra.Fp8
import ZkFormal.Stark.Field

/-!
# `ZkFormal.Stark.InstanceDefs`

The definitions of `ZkFormal.Stark.Instance` that the deployed verifier model
(`NpUdrStarkV2.Model.verifier`) uses, moved verbatim (same names, statements and bodies).
`ZkFormal.Stark.Instance` imports this module, so its importers see the same names. Definitions only:
the model's import closure must not contain proof modules (judge native-lean build,
lane v3-model-split, docs/logs/v3-model-split-2026-10.md).
-/

namespace ZkFormal.Stark

open ZkFormal.Algebra

instance : StarkField Fp Fp8 where
  toNat := Fp.toNat
  embed := Fp8.ofBase
  limbs := fun a => [a.c0, a.c1, a.c2, a.c3, a.c4, a.c5, a.c6, a.c7]
  ofLimbs := fun l => Fp8.ofCoeffs fun i => l.getD i 0
  twoAdicGen := Fp.twoAdicGen
  shift := 31

end ZkFormal.Stark
