import Lean

/-!
# `RcptTaint` — which declarations depend on the receipt table's local constraints?

Usage (from `zk-formal/`):

```
lake env lean --run scripts/RcptTaint.lean <out.tsv> <Root.Module>... -- <root.constant>...
```

Lane `v3-d1-phase2`, item V4 (plan `docs/zk-formal/V3-D1-PHASE2.md` §7).  Imports the root
modules (built `.olean`s), walks the kernel dependency graph from the root constants (as
`ClosureDeps.lean`) and marks a needed constant **tainted** when

* its type or value contains `TableLocal T` with `T` one of the receipt tables (`RcptV3.table`,
  `RcptV3.tableR`, `RcptV3.tableQ`, `RcptSkeleton.receiptArithmeticCandidate`,
  `ReceiptCandidateRouting.candidateTable`), or
* its type or value refers to a tainted constant (fixed point), or
* it is a constructor / recursor / projection of a tainted inductive.

Writes `name  module  tainted  kind` for every needed `ZkFormal` constant.  A tainted
constant must be re-proved for `nearAirV3D1`'s receipt table (`RcptD1.tableQD1`); an untainted
one is reused verbatim.  Reads `.olean`s only; proves and declares nothing.
-/

open Lean

def seedTables : List Name :=
  [`ZkFormal.NearV3.RcptV3.table, `ZkFormal.NearV3.RcptV3.tableR, `ZkFormal.NearV3.RcptV3.tableQ,
   `ZkFormal.NearV3.Assembly.RcptSkeleton.receiptArithmeticCandidate,
   `ZkFormal.NearV3.Assembly.ReceiptCandidateRouting.candidateTable]

/-- Does `e` contain `TableLocal T …` with `T` a seed table? -/
def hasSeed (e : Expr) : Bool :=
  (e.find? fun x =>
    x.isAppOf `ZkFormal.Near.TableLocal &&
      (match x.getAppArgs[0]? with
       | some t => match t.getAppFn.constName? with
         | some n => seedTables.contains n
         | none => false
       | none => false)).isSome

def candidateRoot (m : Name) : Bool :=
  let r := m.getRoot
  r == `ZkFormal || r == `ReexecV3D0 || r == `NpUdrStarkV2

partial def main (args : List String) : IO UInt32 := do
  match args with
  | out :: rest =>
    let (mods, consts) := rest.span (· != "--")
    let consts := consts.drop 1
    initSearchPath (← findSysroot)
    let env ← importModules (mods.toArray.map fun m => { module := m.toName }) {} (trustLevel := 1024)
    let names := env.header.moduleNames
    let modOf (c : Name) : Name := match env.getModuleIdxFor? c with
      | some i => names[i.toNat]!
      | none => .anonymous
    -- 1. dependency walk (restricted to project modules)
    let mut seen : NameSet := {}
    let mut todo : Array Name := consts.toArray.map (·.toName)
    while h : todo.size > 0 do
      let c := todo.back
      todo := todo.pop
      if seen.contains c then continue
      unless candidateRoot (modOf c) do continue
      seen := seen.insert c
      let some ci := env.find? c | continue
      for d in ci.getUsedConstantsAsSet do todo := todo.push d
      match ci with
      | .inductInfo v => for d in v.ctors ++ v.all do todo := todo.push d
                         todo := todo.push (mkRecName c)
      | .ctorInfo v => todo := todo.push v.induct
      | .recInfo v => for d in v.all do todo := todo.push d
      | _ => pure ()
      if let some s := getStructureInfo? env c then
        for p in s.fieldNames do todo := todo.push (c ++ p)
    -- 2. taint fixed point
    let all := seen.toArray
    let mut tainted : NameSet := {}
    for c in all do
      let some ci := env.find? c | continue
      if hasSeed ci.type || (ci.value?.map hasSeed).getD false then tainted := tainted.insert c
    let mut changed := true
    while changed do
      changed := false
      for c in all do
        if tainted.contains c then continue
        let some ci := env.find? c | continue
        let mut t := ci.getUsedConstantsAsSet.toList.any tainted.contains
        match ci with
        | .ctorInfo v => t := t || tainted.contains v.induct
        | .recInfo v => t := t || v.all.any tainted.contains
        | .inductInfo v => t := t || v.ctors.any tainted.contains
        | _ => pure ()
        if !t then
          -- a projection of a tainted structure
          match c with
          | .str p _ => if (getStructureInfo? env p).isSome && tainted.contains p then t := true
          | _ => pure ()
        if t then tainted := tainted.insert c; changed := true
    let mut lines : Array String := #[]
    for c in all do
      let some ci := env.find? c | continue
      let kind := match ci with
        | .thmInfo _ => "thm" | .defnInfo _ => "def" | .axiomInfo _ => "axiom"
        | .opaqueInfo _ => "opaque" | .inductInfo _ => "induct" | .ctorInfo _ => "ctor"
        | .recInfo _ => "rec" | .quotInfo _ => "quot"
      lines := lines.push s!"{c}\t{modOf c}\t{if tainted.contains c then 1 else 0}\t{kind}"
    IO.FS.writeFile out (String.intercalate "\n" (lines.qsort (· < ·)).toList ++ "\n")
    IO.println s!"{all.size} needed constants, {tainted.size} tainted"
    return 0
  | _ => IO.eprintln "usage: RcptTaint <out.tsv> <Module>... -- <const>..."; return 2
