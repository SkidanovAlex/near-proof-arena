import ZkFormal.Air.Basic
import ZkFormal.Near.Ids
import ZkFormal.Near.Tables.Dsl
import ZkFormal.NearV3.Rcpt.Ids
import ZkFormal.NearV3.Rcpt.Tables.Rcpt.ArithDefs
import ZkFormal.NearV3.Rcpt.Tables.Rcpt.Fields
import ZkFormal.NearV3.Rcpt.Tables.Rcpt.Layout

/-!
# `ZkFormal.NearV3.Rcpt.Tables.RcptDefs`

The definitions of `ZkFormal.NearV3.Rcpt.Tables.Rcpt` that the deployed verifier model
(`NpUdrStarkV2.Model.verifier`) uses, moved verbatim (same names, statements and bodies).
`ZkFormal.NearV3.Rcpt.Tables.Rcpt` imports this module, so its importers see the same names. Definitions only:
the model's import closure must not contain proof modules (judge native-lean build,
lane v3-model-split, docs/logs/v3-model-split-2026-10.md).
-/

namespace ZkFormal.NearV3.RcptV3

open ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl

def constraints : List Expr :=
  cStates ++ cEmit ++ cRegs ++ cChars ++ cKey ++ cSys ++ cRoute ++ cGas ++ cDep ++ cEnd

def bndMsg (u : Expr) : List Expr :=
  [.add (smul BND_STRIDE (c q)) (c iB), c loB, c hiB, c hnB, u]

def interactions : List Interaction :=
  (List.range 3).map (fun e => send B_BYTES (c (eG e)) [c (eId e), c (ePos e), c (eV e)]) ++
  [ recv B_DIGEST (c gDg) ([c dI, c dL] ++ (List.range 32).map fun i => c (reg i)),
    send B_KEYNIB (c gKA) [wE, c tA, c symA, c lastA],
    send B_KEYNIB (c gKB) [wE, c tB, c symB, k 0],
    recv B_FINAL (c gF) [.add (c r) (smul W_AK (c sT0)), k 0, c fkF, c kF],
    recv B_MEM (c sDEP) [c kslot, c tprev, c idx, c bef, c lk, c st],
    send B_MEM (c sDEP) [c kslot, .add (c r) (k 1), c idx, aftE, c lk, c st],
    send B_RIDS (c sRID) [c r, c idx, c b],
    send B_MPOS (c rf) [k 0, c r, mid K_LEAF (c r), k 68],
    send B_RCL (c le) [c j, c oEnd],
    send B_SREC (c gV) [c r, c idx, c b],
    recv B_SREC (c gS) [c r, c idx, c sx],
    recv B_AKC (c gAK) [c kF, c uak],
    send B_AKC (c gAK) [c kF, .add (c uak) (k 1)],
    recv B_BND (c gBd) (bndMsg (c uB)),
    send B_BND (c gBd) (bndMsg (.add (c uB) (k 1))) ]

/-- `≤ 1984` list headers × 12 + `≤ 4481` receipts (A1) × `≤ 474` rows `< 2^22`. -/
def maxLog : Nat := 22

def table : Table :=
  { width := width, constraints := constraints, interactions := interactions, maxLog := maxLog }

end ZkFormal.NearV3.RcptV3
