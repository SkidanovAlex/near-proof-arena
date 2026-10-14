import ArenaCore.Bytes
import ArenaCore.Security.OracleComp
import ArenaCore.Security.ROMLemmas
import ZkFormal.GameDefs

/-!
# `ZkFormal.V3.HintDefs`

The definitions of `ZkFormal.V3.Hint` that the deployed verifier model
(`NpUdrStarkV2.Model.verifier`) uses, moved verbatim (same names, statements and bodies).
`ZkFormal.V3.Hint` imports this module, so its importers see the same names. Definitions only:
the model's import closure must not contain proof modules (judge native-lean build,
lane v3-model-split, docs/logs/v3-model-split-2026-10.md).
-/

namespace ZkFormal.V3

open ArenaCore ArenaCore.Security ZkFormal

/-- The composed verifier: split the proof, preprocess natively, run `V` on the
prepared statement. Rejects (without oracle queries) when either step fails. -/
def hintTree (split : Bytes → Option (Bytes × Bytes)) (prep : Bytes → Bytes → Option Bytes)
    (V : TreeVerifier) : TreeVerifier :=
  ⟨fun pub cb pb =>
    match split pb with
    | some (h, π) =>
      match prep cb h with
      | some cb' => V.tree pub cb' π
      | none => .pure false
    | none => .pure false⟩

/-- What the inner verifier sees for the composed verifier's input `(cb, pb)`.
On failure, any pair will do (the composed verifier rejects without queries). -/
def inner (split : Bytes → Option (Bytes × Bytes)) (prep : Bytes → Bytes → Option Bytes)
    (cb pb : Bytes) : Bytes × Bytes :=
  match split pb with
  | some (h, π) =>
    match prep cb h with
    | some cb' => (cb', π)
    | none => (cb, pb)
  | none => (cb, pb)

end ZkFormal.V3
