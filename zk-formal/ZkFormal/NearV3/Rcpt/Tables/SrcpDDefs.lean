

/-!
# `ZkFormal.NearV3.Rcpt.Tables.SrcpDDefs`

The definitions of `ZkFormal.NearV3.Rcpt.Tables.SrcpD` that the deployed verifier model
(`NpUdrStarkV2.Model.verifier`) uses, moved verbatim (same names, statements and bodies).
`ZkFormal.NearV3.Rcpt.Tables.SrcpD` imports this module, so its importers see the same names. Definitions only:
the model's import closure must not contain proof modules (judge native-lean build,
lane v3-model-split, docs/logs/v3-model-split-2026-10.md).
-/

namespace ZkFormal.NearV3.SrcpV3


/-- The path-depth budget (`NearSpecV3.Dp0`). -/
def DP0 : Nat := 32

end ZkFormal.NearV3.SrcpV3
