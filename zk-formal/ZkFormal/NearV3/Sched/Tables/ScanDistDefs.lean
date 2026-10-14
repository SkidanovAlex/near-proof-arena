import ZkFormal.Air.Basic
import ZkFormal.Chacha.Table
import ZkFormal.NearV3.Sched.Ids
import ZkFormal.NearV3.Sched.Tables.Dist
import ZkFormal.NearV3.Sched.Tables.Scan

/-!
# `ZkFormal.NearV3.Sched.Tables.ScanDistDefs`

The definitions of `ZkFormal.NearV3.Sched.Tables.ScanDist` that the deployed verifier model
(`NpUdrStarkV2.Model.verifier`) uses, moved verbatim (same names, statements and bodies).
`ZkFormal.NearV3.Sched.Tables.ScanDist` imports this module, so its importers see the same names. Definitions only:
the model's import closure must not contain proof modules (judge native-lean build,
lane v3-model-split, docs/logs/v3-model-split-2026-10.md).
-/

namespace ZkFormal.NearV3.Sched.ScanDist

open ZkFormal.Air ZkFormal.Chacha.Table.E

open ZkFormal.Chacha.Table (boolC)

def width : Nat := Dist.width

def constraints : List Expr := Dist.constraints ++ Scan.own

/-- The merged public receive's tag: 1 on param rows, 2 on request rows, 3 on shard rows,
4 on cells. -/
def tagE : Expr :=
  .add (c Dist.kP) (.add (smul 2 (c Dist.kS)) (.add (smul 3 (c Dist.kSh)) (smul 4 (c Dist.kC))))

def interactions : List Interaction :=
  [ { bus := B_SPAR, mult := [.add (c Scan.kP) (.add (c Scan.fQ) (.add (c Dist.kSh) (c Dist.kC)))],
      send := false, msg := [c Dist.tau, tagE] ++ (List.range 9).map fun i => c (Dist.fw i) },
    { bus := B_SINC, mult := [c Scan.us0], send := true,
      msg := [c Scan.tau, Scan.eE, sub Scan.val0 (c Scan.cur), sub (sub (c Scan.m) (c Scan.j)) (k 1),
              c Scan.s, c Scan.r, c Scan.link] },
    { bus := B_SINC, mult := [c Scan.us1], send := true,
      msg := [c Scan.tau, .add Scan.eE (c Scan.b0), sub Scan.val1 (c Scan.cm),
              sub (sub (sub (c Scan.m) (c Scan.j)) (c Scan.b0)) (k 1), c Scan.s, c Scan.r, c Scan.link] },
    { bus := B_SPUSH, mult := [c Scan.re], send := true,
      msg := [c Scan.tau, c Scan.key, c Scan.zk0, c Scan.cid, smul 64 (c Scan.cid)] },
    { bus := B_SOP, mult := [.add (c Scan.re) (c Dist.kSh)], send := true,
      msg := [Scan.aL, .add (c Scan.cid) (c Scan.kS), c Scan.kS, c Scan.key,
              .add (c Scan.key) (c Scan.bvz), k 0, k 0, k 0] },
    { bus := B_SFIN, mult := [c Dist.kSh], send := false, msg := [Dist.addrE, c Dist.L2, k 0] },
    { bus := B_SCMP, mult := [c Dist.cg], send := true, msg := [c Dist.cx, c Dist.cy, c Dist.cb] },
    { bus := B_SDLX, mult := [c Dist.dlsg], send := true,
      msg := [c Dist.tau, c Dist.da, c Dist.db, c Dist.r, sub (c Dist.N2) (c Dist.al), c Dist.sL] },
    { bus := B_SDLX, mult := [c Dist.dlrg], send := false,
      msg := [c Dist.tau, c Dist.a, c Dist.b, c Dist.r, c Dist.N2, c Dist.L2] },
    { bus := B_SDG, mult := [c Dist.kC], send := true,
      msg := [c Dist.tau, Dist.linkE, c Dist.al, c Dist.gb,
              .add (c Dist.side) (smul 256 (c Dist.shd)), c Dist.lnk, c Dist.by0] } ]

def maxLog : Nat := 22

def table : Table :=
  { width := width, constraints := constraints, interactions := interactions, maxLog := maxLog }

end ZkFormal.NearV3.Sched.ScanDist
