import ZkFormal.Air.Basic
import ZkFormal.Near.Tables.Acct
import ZkFormal.Near.Tables.Dsl
import ZkFormal.NearV3.Rcpt.Tables.Acct

/-!
# `ZkFormal.NearV3.Rcpt.Candidates.AccountEmptyDefs`

The definitions of `ZkFormal.NearV3.Rcpt.Candidates.AccountEmpty` that the deployed verifier model
(`NpUdrStarkV2.Model.verifier`) uses, moved verbatim (same names, statements and bodies).
`ZkFormal.NearV3.Rcpt.Candidates.AccountEmpty` imports this module, so its importers see the same names. Definitions only:
the model's import closure must not contain proof modules (judge native-lean build,
lane v3-model-split, docs/logs/v3-model-split-2026-10.md).
-/

set_option linter.unusedSimpArgs false

namespace ZkFormal.NearV3.Rcpt.Candidates.AccountEmpty

open ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl

def oldFirst : Expr := .mul .isFirst (Dsl.not (c Acct.af))
def newFirst : Expr := .mul .isFirst (sub (c Acct.act) (c Acct.af))
def replaceFirst (e : Expr) : Expr := if e=oldFirst then newFirst else e

/-- Permit an all-inactive account table. All segment and padding rules and all
bus interactions remain unchanged; an active first row still starts a segment. -/
def table : Air.Table :=
  {AcctV3.table with constraints:=Acct.constraints.map replaceFirst}

end ZkFormal.NearV3.Rcpt.Candidates.AccountEmpty
