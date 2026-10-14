import ZkFormal.Air.Basic
import ZkFormal.Near.Tables.Dsl
import ZkFormal.Near.Tables.Sort

/-!
# `ZkFormal.NearV3.Candidates.SortEmptyDefs`

The definitions of `ZkFormal.NearV3.Candidates.SortEmpty` that the deployed verifier model
(`NpUdrStarkV2.Model.verifier`) uses, moved verbatim (same names, statements and bodies).
`ZkFormal.NearV3.Candidates.SortEmpty` imports this module, so its importers see the same names. Definitions only:
the model's import closure must not contain proof modules (judge native-lean build,
lane v3-model-split, docs/logs/v3-model-split-2026-10.md).
-/

namespace ZkFormal.NearV3.Candidates.SortEmpty

open ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl

def firstSegment : Expr:=.mul .isFirst (Dsl.not (c Sort.sf))
def firstFlag : Expr:=.mul .isFirst (Dsl.not (c Sort.ft))
def replaceFirst (e : Expr) : Expr:=
  if e=firstSegment then .mul .isFirst (sub (c Sort.act) (c Sort.sf)) else
  if e=firstFlag then .mul .isFirst (sub (c Sort.act) (c Sort.ft)) else e

def table : Table:={Sort.table with maxLog:=18,constraints:=Sort.constraints.map replaceFirst}

end ZkFormal.NearV3.Candidates.SortEmpty
