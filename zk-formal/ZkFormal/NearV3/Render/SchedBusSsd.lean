import ZkFormal.NearV3.Render.PaddedSsd

/-!
# Scan/distribute table (12) traffic on the scheduler buses: per-row messages

`*M x`: the messages of a row with cells `x` on `SPAR` (recv), `SINC`, `SPUSH`, `SOP` (send), `SFIN`
(recv), `SDLX` (both), `SDG` (send); `row_*`: every row's traffic is that function of its cells;
`ssd_bus`: the table traffic of the honest trace is the concatenation over its rows.
-/
set_option linter.unusedSimpArgs false
namespace ZkFormal.NearV3.Render.SsdBus
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.NearV3.Candidates ZkFormal.NearV3.Assembly.CodecDigest

def sparM (x : Nat → Fp) : List (List Fp) :=
  List.replicate (if x Scan.kP + (x Scan.fQ + (x Dist.kSh + x Dist.kC)) = 1 then 1 else 0)
    ([x Dist.tau, x Dist.kP + (((2 : Nat) : Fp) * x Dist.kS + (((3 : Nat) : Fp) * x Dist.kSh +
      ((4 : Nat) : Fp) * x Dist.kC))] ++
      (List.range 9).map fun i => x (Dist.fw i))

theorem row_spar (tr : Trace Fp) (t r : Nat) (pub : List Fp) :
    rowTraffic ScanDist.table.interactions tr t r pub B_SPAR false = sparM (tr.cell t r) := by
  simp [ScanDist.table,ScanDist.interactions,rowTraffic,Interaction.multNat,Interaction.multNat.go,
    Interaction.msgVal,Expr.eval,Expr.evalWith,rowEnv,ZkFormal.Chacha.Table.E.c,
    ZkFormal.Chacha.Table.E.k,ZkFormal.Chacha.Table.E.smul,ZkFormal.Chacha.Table.E.sub,
    B_SPAR,B_SINC,B_SPUSH,B_SOP,B_SFIN,B_SCMP,B_SDLX,B_SDG, ScanDist.tagE, sparM, List.range_succ]

def sincM (x : Nat → Fp) : List (List Fp) :=
  List.replicate (if x Scan.us0 = 1 then 1 else 0)
    [x Scan.tau, ((64 : Nat) : Fp) * x Scan.cid + x Scan.j, x Scan.base + x Scan.Q0 + -x Scan.cur,
      x Scan.m + -x Scan.j + -((1 : Nat) : Fp), x Scan.s, x Scan.r, x Scan.link] ++
  List.replicate (if x Scan.us1 = 1 then 1 else 0)
    [x Scan.tau, ((64 : Nat) : Fp) * x Scan.cid + x Scan.j + x Scan.b0, x Scan.base + x Scan.Q1 + -x Scan.cm,
      x Scan.m + -x Scan.j + -x Scan.b0 + -((1 : Nat) : Fp), x Scan.s, x Scan.r, x Scan.link]

theorem row_sinc (tr : Trace Fp) (t r : Nat) (pub : List Fp) :
    rowTraffic ScanDist.table.interactions tr t r pub B_SINC true = sincM (tr.cell t r) := by
  simp [ScanDist.table,ScanDist.interactions,rowTraffic,Interaction.multNat,Interaction.multNat.go,
    Interaction.msgVal,Expr.eval,Expr.evalWith,rowEnv,ZkFormal.Chacha.Table.E.c,
    ZkFormal.Chacha.Table.E.k,ZkFormal.Chacha.Table.E.smul,ZkFormal.Chacha.Table.E.sub,
    B_SPAR,B_SINC,B_SPUSH,B_SOP,B_SFIN,B_SCMP,B_SDLX,B_SDG, ScanDist.tagE, Scan.eE, Scan.aL, Scan.val0,
    Scan.val1, Dist.addrE, Dist.linkE, sincM]

def spushM (x : Nat → Fp) : List (List Fp) :=
  List.replicate (if x Scan.re = 1 then 1 else 0)
    [x Scan.tau, x Scan.key, x Scan.zk0, x Scan.cid, ((64 : Nat) : Fp) * x Scan.cid]

theorem row_spush (tr : Trace Fp) (t r : Nat) (pub : List Fp) :
    rowTraffic ScanDist.table.interactions tr t r pub B_SPUSH true = spushM (tr.cell t r) := by
  simp [ScanDist.table,ScanDist.interactions,rowTraffic,Interaction.multNat,Interaction.multNat.go,
    Interaction.msgVal,Expr.eval,Expr.evalWith,rowEnv,ZkFormal.Chacha.Table.E.c,
    ZkFormal.Chacha.Table.E.k,ZkFormal.Chacha.Table.E.smul,ZkFormal.Chacha.Table.E.sub,
    B_SPAR,B_SINC,B_SPUSH,B_SOP,B_SFIN,B_SCMP,B_SDLX,B_SDG, ScanDist.tagE, Scan.eE, Scan.aL, Scan.val0,
    Scan.val1, Dist.addrE, Dist.linkE, spushM]

def sopM (x : Nat → Fp) : List (List Fp) :=
  List.replicate (if x Scan.re + x Dist.kSh = 1 then 1 else 0)
    [((16384 : Nat) : Fp) * x Scan.tau + x Scan.link, x Scan.cid + x Scan.kS, x Scan.kS, x Scan.key,
      x Scan.key + x Scan.bvz, ((0 : Nat) : Fp), ((0 : Nat) : Fp), ((0 : Nat) : Fp)]

theorem row_sop (tr : Trace Fp) (t r : Nat) (pub : List Fp) :
    rowTraffic ScanDist.table.interactions tr t r pub B_SOP true = sopM (tr.cell t r) := by
  simp [ScanDist.table,ScanDist.interactions,rowTraffic,Interaction.multNat,Interaction.multNat.go,
    Interaction.msgVal,Expr.eval,Expr.evalWith,rowEnv,ZkFormal.Chacha.Table.E.c,
    ZkFormal.Chacha.Table.E.k,ZkFormal.Chacha.Table.E.smul,ZkFormal.Chacha.Table.E.sub,
    B_SPAR,B_SINC,B_SPUSH,B_SOP,B_SFIN,B_SCMP,B_SDLX,B_SDG, ScanDist.tagE, Scan.eE, Scan.aL, Scan.val0,
    Scan.val1, Dist.addrE, Dist.linkE, sopM]

def sfinM (x : Nat → Fp) : List (List Fp) :=
  List.replicate (if x Dist.kSh = 1 then 1 else 0)
    [((16384 : Nat) : Fp) * x Dist.tau + (((4096 : Nat) : Fp) * (x Dist.side + ((1 : Nat) : Fp)) + x Dist.r), x Dist.L2, ((0 : Nat) : Fp)]

theorem row_sfin (tr : Trace Fp) (t r : Nat) (pub : List Fp) :
    rowTraffic ScanDist.table.interactions tr t r pub B_SFIN false = sfinM (tr.cell t r) := by
  simp [ScanDist.table,ScanDist.interactions,rowTraffic,Interaction.multNat,Interaction.multNat.go,
    Interaction.msgVal,Expr.eval,Expr.evalWith,rowEnv,ZkFormal.Chacha.Table.E.c,
    ZkFormal.Chacha.Table.E.k,ZkFormal.Chacha.Table.E.smul,ZkFormal.Chacha.Table.E.sub,
    B_SPAR,B_SINC,B_SPUSH,B_SOP,B_SFIN,B_SCMP,B_SDLX,B_SDG, ScanDist.tagE, Scan.eE, Scan.aL, Scan.val0,
    Scan.val1, Dist.addrE, Dist.linkE, sfinM]

def sdlxsM (x : Nat → Fp) : List (List Fp) :=
  List.replicate (if x Dist.dlsg = 1 then 1 else 0)
    [x Dist.tau, x Dist.da, x Dist.db, x Dist.r, x Dist.N2 + -x Dist.al, x Dist.sL]

theorem row_sdlxs (tr : Trace Fp) (t r : Nat) (pub : List Fp) :
    rowTraffic ScanDist.table.interactions tr t r pub B_SDLX true = sdlxsM (tr.cell t r) := by
  simp [ScanDist.table,ScanDist.interactions,rowTraffic,Interaction.multNat,Interaction.multNat.go,
    Interaction.msgVal,Expr.eval,Expr.evalWith,rowEnv,ZkFormal.Chacha.Table.E.c,
    ZkFormal.Chacha.Table.E.k,ZkFormal.Chacha.Table.E.smul,ZkFormal.Chacha.Table.E.sub,
    B_SPAR,B_SINC,B_SPUSH,B_SOP,B_SFIN,B_SCMP,B_SDLX,B_SDG, ScanDist.tagE, Scan.eE, Scan.aL, Scan.val0,
    Scan.val1, Dist.addrE, Dist.linkE, sdlxsM]

def sdlxrM (x : Nat → Fp) : List (List Fp) :=
  List.replicate (if x Dist.dlrg = 1 then 1 else 0)
    [x Dist.tau, x Dist.a, x Dist.b, x Dist.r, x Dist.N2, x Dist.L2]

theorem row_sdlxr (tr : Trace Fp) (t r : Nat) (pub : List Fp) :
    rowTraffic ScanDist.table.interactions tr t r pub B_SDLX false = sdlxrM (tr.cell t r) := by
  simp [ScanDist.table,ScanDist.interactions,rowTraffic,Interaction.multNat,Interaction.multNat.go,
    Interaction.msgVal,Expr.eval,Expr.evalWith,rowEnv,ZkFormal.Chacha.Table.E.c,
    ZkFormal.Chacha.Table.E.k,ZkFormal.Chacha.Table.E.smul,ZkFormal.Chacha.Table.E.sub,
    B_SPAR,B_SINC,B_SPUSH,B_SOP,B_SFIN,B_SCMP,B_SDLX,B_SDG, ScanDist.tagE, Scan.eE, Scan.aL, Scan.val0,
    Scan.val1, Dist.addrE, Dist.linkE, sdlxrM]

def sdgM (x : Nat → Fp) : List (List Fp) :=
  List.replicate (if x Dist.kC = 1 then 1 else 0)
    [x Dist.tau, x Dist.llo + ((256 : Nat) : Fp) * x Dist.lhi, x Dist.al, x Dist.gb,
      x Dist.side + ((256 : Nat) : Fp) * x Dist.shd, x Dist.lnk, x Dist.by0]

theorem row_sdg (tr : Trace Fp) (t r : Nat) (pub : List Fp) :
    rowTraffic ScanDist.table.interactions tr t r pub B_SDG true = sdgM (tr.cell t r) := by
  simp [ScanDist.table,ScanDist.interactions,rowTraffic,Interaction.multNat,Interaction.multNat.go,
    Interaction.msgVal,Expr.eval,Expr.evalWith,rowEnv,ZkFormal.Chacha.Table.E.c,
    ZkFormal.Chacha.Table.E.k,ZkFormal.Chacha.Table.E.smul,ZkFormal.Chacha.Table.E.sub,
    B_SPAR,B_SINC,B_SPUSH,B_SOP,B_SFIN,B_SCMP,B_SDLX,B_SDG, ScanDist.tagE, Scan.eE, Scan.aL, Scan.val0,
    Scan.val1, Dist.addrE, Dist.linkE, sdgM]

end ZkFormal.NearV3.Render.SsdBus
