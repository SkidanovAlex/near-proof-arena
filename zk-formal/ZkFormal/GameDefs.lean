import ArenaCore.Bytes
import ArenaCore.Interp
import ArenaCore.Security.OracleComp
import ArenaCore.Security.ROMLemmas
import ArenaCore.Verifier

/-!
# `ZkFormal.GameDefs`

The definitions of `ZkFormal.Game` that the deployed verifier model
(`NpUdrStarkV2.Model.verifier`) uses, moved verbatim (same names, statements and bodies).
`ZkFormal.Game` imports this module, so its importers see the same names. Definitions only:
the model's import closure must not contain proof modules (judge native-lean build,
lane v3-model-split, docs/logs/v3-model-split-2026-10.md).
-/

namespace ZkFormal

open ArenaCore ArenaCore.Security

/-- Run a hash-query tree against any (stateful) hash oracle. -/
def runH {σ α : Type} (H : Interp.HashOracle σ) : OracleComp hashSpec α → σ → α × σ
  | .pure a, s => (a, s)
  | .query x k, s => runH H (k (H s x).1) (H s x).2

/-- A verifier given as a hash-query tree. -/
structure TreeVerifier where
  tree : Bytes → Bytes → Bytes → OracleComp hashSpec Bool

def TreeVerifier.toVerifier (V : TreeVerifier) : OracleVerifier :=
  ⟨fun H s pub cb pb => runH H (V.tree pub cb pb) s⟩

section

end

end ZkFormal
