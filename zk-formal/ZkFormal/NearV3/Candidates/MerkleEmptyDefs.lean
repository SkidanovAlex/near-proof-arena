import ZkFormal.Air.Basic
import ZkFormal.Near.Tables.Dsl
import ZkFormal.Near.Tables.Mrk
import ZkFormal.NearV3.Candidates.MerklePublicDefs
import ZkFormal.NearV3.Rcpt.Ids

/-!
# `ZkFormal.NearV3.Candidates.MerkleEmptyDefs`

The definitions of `ZkFormal.NearV3.Candidates.MerkleEmpty` that the deployed verifier model
(`NpUdrStarkV2.Model.verifier`) uses, moved verbatim (same names, statements and bodies).
`ZkFormal.NearV3.Candidates.MerkleEmpty` imports this module, so its importers see the same names. Definitions only:
the model's import closure must not contain proof modules (judge native-lean build,
lane v3-model-split, docs/logs/v3-model-split-2026-10.md).
-/

namespace ZkFormal.NearV3.Candidates.MerkleEmpty

open ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl

def emptyCol : Nat := 58
def inverseCol : Nat := 59
def countE : Expr := MerklePublic.expression Mrk.nPubE
def active : Expr := Dsl.not (c emptyCol)
def gate (e : Expr) : Expr := .mul active e

def interaction (i : Interaction) : Interaction :=
  {i with mult:=i.mult.map gate}

/-- Empty trees use no Merkle/SHA traffic. The inverse distinguishes nonzero
counts; the public byte range and count bound are supplied by the whole AIR. -/
def controls : List Expr :=
  [Dsl.bool (c emptyCol), sub (n emptyCol) (c emptyCol),
   .mul (c emptyCol) countE,
   .mul active (sub (.mul countE (c inverseCol)) (k 1))] ++
  (List.range 32).map (fun i => .mul (c emptyCol) (.pub (PH_OUT+i)))

def table : Air.Table :=
  { MerklePublic.table with
    width:=60
    constraints:=controls ++ MerklePublic.table.constraints.map gate
    interactions:=MerklePublic.table.interactions.map interaction }

end ZkFormal.NearV3.Candidates.MerkleEmpty
