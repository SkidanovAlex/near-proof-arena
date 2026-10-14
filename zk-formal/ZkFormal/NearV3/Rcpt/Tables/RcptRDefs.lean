import ZkFormal.Air.Basic
import ZkFormal.Near.Tables.Dsl
import ZkFormal.NearV3.Rcpt.Tables.Rcpt.ArithDefs
import ZkFormal.NearV3.Rcpt.Tables.Rcpt.Fields
import ZkFormal.NearV3.Rcpt.Tables.Rcpt.Layout
import ZkFormal.NearV3.Rcpt.Tables.RcptDefs

/-!
# `ZkFormal.NearV3.Rcpt.Tables.RcptRDefs`

The definitions of `ZkFormal.NearV3.Rcpt.Tables.RcptR` that the deployed verifier model
(`NpUdrStarkV2.Model.verifier`) uses, moved verbatim (same names, statements and bodies).
`ZkFormal.NearV3.Rcpt.Tables.RcptR` imports this module, so its importers see the same names. Definitions only:
the model's import closure must not contain proof modules (judge native-lean build,
lane v3-model-split, docs/logs/v3-model-split-2026-10.md).
-/

namespace ZkFormal.NearV3.RcptV3

open ZkFormal.Air ZkFormal.Near ZkFormal.Near.Dsl

def gasConstraintsWithR (surplus : Expr) : List Expr :=
  let d (i : Nat) : Expr := c (dl i)
  [ .mul gp (sub (sub (c b) (c (reg 0))) (sub (.add (c c1) DE) (smul 256 (c (xb 8))))),
    .mul (.mul gp (c fs)) (c c1), mul3 gp (not (c fe)) (sub (n c1) (c (xb 8))),
    mul3 gp (c fe) (sub (c (xb 8)) (not (c ge))),
    -- effective burn price: `p` (`0` for system receipts); `gq = ge·(1 − sys)`
    .mul gp (sub (c pc) (.mul (not (c sys)) pE)),
    .mul rowE (sub (c gq) (.mul (c ge) (not (c sys)))),
    -- burnt = G·pc
    .mul gp (sub (.add (c burnt) (smul 256 (bitsX 9 11))) (.add (conv (G_LE.take 5) (c pc) d) (c c2))),
    .mul (.mul gp (c fs)) (c c2), mul3 gp (not (c fe)) (sub (n c2) (bitsX 9 11)),
    mul3 gp (c fe) (bitsX 9 11), mul3 gp (c fe) (ovf (c pc) d),
    -- refund amount = G·surplus
    .mul gp (sub (.add (c ramt) (smul 256 (bitsX 20 11)))
      (.add (conv (G_LE.take 5) surplus (fun i => d (4 + i))) (c c3))),
    .mul (.mul gp (c fs)) (c c3), mul3 gp (not (c fe)) (sub (n c3) (bitsX 20 11)),
    mul3 gp (c fe) (bitsX 20 11), mul3 gp (c fe) (ovf surplus (fun i => d (4 + i))),
    -- running tokens
    .mul gp (sub (.add (bitsX 31 8) (smul 256 (c (xb 39)))) (sum [c (tok 0), c burnt, c c4])),
    .mul (.mul gp (c fs)) (c c4), mul3 gp (not (c fe)) (sub (n c4) (c (xb 39))),
    mul3 gp (c fe) (c (xb 39)),
    -- refund flag: (non-system) surplus bytes vanish without a refund; a refund has a
    -- nonzero surplus
    .mul (mul3 gp (not (c hr)) (c gq)) DE,
    mul3 gp (c fs) (sub (c sumD) DE),
    mul3 gp (not (c fe)) (sub (n sumD) (.add (c sumD) DEn)),
    mul3 gp (c fe) (sub (.mul (c sumD) (c invA)) (c hr)) ] ++
  -- delay lines of pc and surplus
  (List.range 8).map (fun i => mul3 gp (c fs) (d i)) ++
  [ mul3 gp (not (c fe)) (sub (n (dl 0)) (c pc)), mul3 gp (not (c fe)) (sub (n (dl 4)) surplus) ] ++
  ([1, 2, 3, 5, 6, 7].map fun i => mul3 gp (not (c fe)) (sub (n (dl i)) (d (i - 1))))

/-- Refund surplus gated by the non-system comparison gate. -/
def systemSurplusR : Expr := .mul (c gq) DE

def depositConstraintsWithR (age : Expr) : List Expr :=
  let d (j : Nat) : Expr := c (dl j)
  [ .mul dp (sub (sum [c bef, c b, c c1]) (.add aftE (smul 256 (c (xb 8))))),
    .mul (.mul dp (c fs)) (c c1), mul3 dp (not (c fe)) (sub (n c1) (c (xb 8))),
    mul3 dp (c fe) (c (xb 8)),
    -- amount ≠ u128::MAX
    mul3 dp (c fs) (sub (c dsum) (sub (k 255) aftE)),
    mul3 dp (not (c fe)) (sub (n dsum) (.add (c dsum) (sub (k 255) (bitsXn 0 8)))),
    mul3 dp (c fe) (sub (.mul (c dsum) (c invB)) (k 1)),
    -- tot = aft + locked < 2^128
    .mul dp (sub (sum [aftE, c lk, c c2]) (.add (bitsX 9 8) (smul 256 (c (xb 17))))),
    .mul (.mul dp (c fs)) (c c2), mul3 dp (not (c fe)) (sub (n c2) (c (xb 17))),
    mul3 dp (c fe) (c (xb 17)),
    -- q = 10^19·storage
    .mul dp (sub (.add (conv S_LE (c st) d) (c c3)) (.add (bitsX 18 8) (smul 256 (bitsX 26 12)))),
    .mul (.mul dp (c fs)) (c c3), mul3 dp (not (c fe)) (sub (n c3) (bitsX 26 12)),
    mul3 dp (c fe) (bitsX 26 12),
    mul3 dp (not (c fe)) (sub (n (dl 0)) (c st)),
    -- tot − q with borrow; no final borrow when `big`
    .mul dp (sub (sub (bitsX 9 8) (bitsX 18 8)) (sub (.add (c c4) (bitsX 38 8)) (smul 256 (c (xb 46))))),
    .mul (.mul dp (c fs)) (c c4), mul3 dp (not (c fe)) (sub (n c4) (c (xb 46))),
    .mul (mul3 dp (c fe) (c big)) (c (xb 46)),
    -- otherwise storage ≤ 770
    .mul (c r1) (not dp), mul3 dp (c fs) (c r1), mul3 dp (not (c fe)) (sub (n r1) (c fs)),
    mul3 (not (c big)) (c r1) (sub (k 770) (sum [c (dl 0), smul 256 (c st), bitsX 47 10])),
    mul3 (not (c big)) (sub (sub dp (c fs)) (c r1)) (c st),
    -- the read is not from the future
    mul3 dp (c fs) (sub (sub (c r) (c tprev)) age) ] ++
  (List.range 7).map (fun j => mul3 dp (c fs) (d j)) ++
  (List.range 6).map (fun j => mul3 dp (not (c fe)) (sub (n (dl (j + 1))) (d j)))

/-- **The repaired receipt table.** -/
def tableR : Table :=
  { table with constraints :=
    cRegs ++ cEmit ++ cStates ++ cEnd ++ cChars ++ cSys ++ cRoute ++ cKey ++
      gasConstraintsWithR systemSurplusR ++ depositConstraintsWithR (bitsX 53 13) }

/-- Routing-index range check (user decision 2026-10-12, `docs/zk-formal/ROUTING-Q-CANDIDATE.md`):
on the first receiver row the boundary interval index `q` equals the seven existing boolean
scratch bits `xb12..18`, so `q < 128` and the packed lookup address `65·q + pos` cannot wrap
mod `P`.  Verbatim copy of `Assembly.RoutingQCandidate.qBound`. -/
def qBoundR : Expr := mul3 (c sV) (c fs) (sub (c q) (bitsX 12 7))

/-- **The installed receipt table** (`nearAirV3` table 16): `tableR` (both arithmetic repairs)
plus the routing-index range check `qBoundR`.  Same columns, interactions and `maxLog`;
882 constraints. -/
def tableQ : Table := { tableR with constraints := tableR.constraints ++ [qBoundR] }

end ZkFormal.NearV3.RcptV3
