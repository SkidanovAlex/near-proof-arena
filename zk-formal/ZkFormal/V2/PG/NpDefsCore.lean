import ZkFormal.Stark.Params
import ZkFormal.V2.G.DefsCore

/-!
# `ZkFormal.V2.PG.NpDefsCore`

The definitions of `ZkFormal.V2.PG.NpDefs` that the deployed verifier model
(`NpUdrStarkV2.Model.verifier`) uses, moved verbatim (same names, statements and bodies).
`ZkFormal.V2.PG.NpDefs` imports this module, so its importers see the same names. Definitions only:
the model's import closure must not contain proof modules (judge native-lean build,
lane v3-model-split, docs/logs/v3-model-split-2026-10.md).
-/

namespace ZkFormal.Prover.Np.G

open Lean.Grind ZkFormal.Stark


attribute [local instance] Semiring.natCast

/-- P2: the running-product group size `g` (`1 ≤ g`), as an instance. -/
class AuxG where
  g : Nat
  one_le : 1 ≤ g

variable [AuxG]

/-- The parameters `pg g = {Params.default with auxGroup := g}`. -/
abbrev dp [AuxG] : Params := V2.G.pg AuxG.g

section

section

end

end

end ZkFormal.Prover.Np.G
