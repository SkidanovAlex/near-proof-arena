import ZkFormal.Air.Basic
import ZkFormal.Near.Ids
import ZkFormal.Near.Tables.Dsl
import ZkFormal.NearV3.Qv.Candidates.CombinedTableDefs

/-!
# `ZkFormal.NearV3.Qv.Candidates.KeyTrafficRepairDefs`

The definitions of `ZkFormal.NearV3.Qv.Candidates.KeyTrafficRepair` that the deployed verifier model
(`NpUdrStarkV2.Model.verifier`) uses, moved verbatim (same names, statements and bodies).
`ZkFormal.NearV3.Qv.Candidates.KeyTrafficRepair` imports this module, so its importers see the same names. Definitions only:
the model's import closure must not contain proof modules (judge native-lean build,
lane v3-model-split, docs/logs/v3-model-split-2026-10.md).
-/

namespace ZkFormal.NearV3.Qv.Candidates.KeyTrafficRepair

open ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl

open CombinedTable

/-- Replace only the four original KEYNIB interactions by three compatible ones. -/
def interactions : List Interaction :=
  CombinedTable.interactions.take 5 ++
  [ send B_KEYNIB (c walk) [wid,smul 2 (c wp),nibble 4,k 0],
    send B_KEYNIB (c walk) [wid,.add (smul 2 (c wp)) (k 1),nibble 0,k 0],
    send B_KEYNIB (c wl) [wid,.add (smul 2 (c wp)) (k 2),k SYM_END,k 1] ] ++
  CombinedTable.interactions.drop 9

def table : Air.Table := { CombinedTable.table with interactions }

end ZkFormal.NearV3.Qv.Candidates.KeyTrafficRepair
