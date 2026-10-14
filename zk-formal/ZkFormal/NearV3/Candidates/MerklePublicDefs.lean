import ZkFormal.Air.Basic
import ZkFormal.Near.Ids
import ZkFormal.Near.Tables.Mrk
import ZkFormal.NearV3.Rcpt.Ids

/-!
# `ZkFormal.NearV3.Candidates.MerklePublicDefs`

The definitions of `ZkFormal.NearV3.Candidates.MerklePublic` that the deployed verifier model
(`NpUdrStarkV2.Model.verifier`) uses, moved verbatim (same names, statements and bodies).
`ZkFormal.NearV3.Candidates.MerklePublic` imports this module, so its importers see the same names. Definitions only:
the model's import closure must not contain proof modules (judge native-lean build,
lane v3-model-split, docs/logs/v3-model-split-2026-10.md).
-/

namespace ZkFormal.NearV3.Candidates.MerklePublic

open ZkFormal.Air ZkFormal.Near

/-- Translate only the two public fields consumed by the outcome Merkle table. -/
def publicIndex (i : Nat) : Nat :=
  if PV_N≤i ∧ i<PV_N+4 then PH_N+(i-PV_N)
  else if PV_OUT≤i ∧ i<PV_OUT+32 then PH_OUT+(i-PV_OUT)
  else i

def expression : Expr → Expr
  | .pub i => .pub (publicIndex i)
  | .add a b => .add (expression a) (expression b)
  | .mul a b => .mul (expression a) (expression b)
  | .neg a => .neg (expression a)
  | e => e

def interaction (i : Interaction) : Interaction :=
  {i with mult:=i.mult.map expression, msg:=i.msg.map expression}

def table : Air.Table :=
  { Mrk.table with
    constraints := Mrk.constraints.map expression
    interactions := Mrk.interactions.map interaction
    maxLog := 19 }

end ZkFormal.NearV3.Candidates.MerklePublic
