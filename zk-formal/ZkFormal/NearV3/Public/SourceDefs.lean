import NearSpec.Bytes
import NearSpecV3.PrepD0
import ZkFormal.NearV3.Public.PackingDefs
import ZkFormal.NearV3.Rcpt.Ids
import ZkFormal.V2.Air

/-!
# `ZkFormal.NearV3.Public.SourceDefs`

The definitions of `ZkFormal.NearV3.Public.Source` that the deployed verifier model
(`NpUdrStarkV2.Model.verifier`) uses, moved verbatim (same names, statements and bodies).
`ZkFormal.NearV3.Public.Source` imports this module, so its importers see the same names. Definitions only:
the model's import closure must not contain proof modules (judge native-lean build,
lane v3-model-split, docs/logs/v3-model-split-2026-10.md).
-/

namespace ZkFormal.NearV3.Public

open ZkFormal.V2 NearSpecV3

def sourceDup (sources : List SrcList) (j : Nat) : Bool :=
  (sources.take j).any (fun s => s.key == (sources.getD j ⟨[],0,[]⟩).key)

/-- The all-occurrence repetition bit (table 20, `SrcpDD`): the key of source `j` occurs at
least twice among the sources (every such occurrence has an empty receipt list). -/
def sourceRep (sources : List SrcList) (j : Nat) : Bool :=
  decide (2 ≤ (sources.map SrcList.key).count (sources.getD j ⟨[],0,[]⟩).key)

/-- Source `j` agrees (from-shard and root) with every earlier source of the same key.  A
later occurrence shares the earlier occurrence's witness entry, so natively the claim is
unsatisfiable unless this holds; table 20 checks a `dup` reference only by its key. -/
def sourceConsistent (sources : List SrcList) (j : Nat) : Bool :=
  (sources.take j).all fun s => !(s.key == (sources.getD j ⟨[],0,[]⟩).key) ||
    (s.fromShard == (sources.getD j ⟨[],0,[]⟩).fromShard && s.root == (sources.getD j ⟨[],0,[]⟩).root)

/-- The public `dup` byte: `0` (first occurrence), `1` (consistent later occurrence) or `2`
(inconsistent later occurrence: no boolean `dup` cell of table 20 matches it, so no trace). -/
def sourceDupByte (sources : List SrcList) (j : Nat) : Nat :=
  if sourceDup sources j then (if sourceConsistent sources j then 1 else 2) else 0

/-- `SRC34`: `[dup byte, rep] ++ root`. -/
def sourceRow (sources : List SrcList) (j : Nat) : ByteString :=
  [UInt8.ofNat (sourceDupByte sources j), if sourceRep sources j then 1 else 0] ++
    (sources.getD j ⟨[],0,[]⟩).root

def sourcePayload (sources : List SrcList) : Payload :=
  (List.range sources.length).map (sourceRow sources)

def sourcePlan : PubSeg :=
  { bus := B_SRC, send := true, width := 34, countAt := 0, start := 0, indexBase := some 0 }

end ZkFormal.NearV3.Public
