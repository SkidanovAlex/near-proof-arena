import ZkFormal.Stark.Params

/-!
# `ZkFormal.V2.G.DefsCore`

The definitions of `ZkFormal.V2.G.Defs` that the deployed verifier model
(`NpUdrStarkV2.Model.verifier`) uses, moved verbatim (same names, statements and bodies).
`ZkFormal.V2.G.Defs` imports this module, so its importers see the same names. Definitions only:
the model's import closure must not contain proof modules (judge native-lean build,
lane v3-model-split, docs/logs/v3-model-split-2026-10.md).
-/

namespace ZkFormal.V2.G

open Lean.Grind ZkFormal.Stark

open ZkFormal.V2

/-- v1's deployed parameters with `auxGroup := g`. -/
def pg (g : Nat) : Params := { Params.default with auxGroup := g }

section

end

end ZkFormal.V2.G
