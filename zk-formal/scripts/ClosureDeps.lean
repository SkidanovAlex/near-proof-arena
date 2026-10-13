import Lean

/-!
# `ClosureDeps` — which modules does a certificate actually use?

Usage (from `zk-formal/`):

```
lake env lean --run scripts/ClosureDeps.lean <outdir> <Root.Module>... -- <root.constant>...
```

Imports the given root modules (their `.olean`s must be built), then walks the kernel
dependency graph from the given root constants: every constant referenced from a constant's
type or value (`ConstantInfo.getUsedConstantsAsSet`), plus for inductives their constructors,
recursors and mutual block, for constructors / recursors their inductive, and for `structure`s
their projections.  This is exactly the set of declarations the kernel needs to re-check the
roots (instances, `match_`/`_proof_`/`eq_` auxiliaries and `decide` instances are ordinary
constants referenced from the terms).

Writes to `<outdir>`:

* `modules.tsv` — every module in the import closure of the root modules:
  `module  needed  inNeededClosure  nConsts  nNeededConsts  imports(comma-sep)`
  where `needed` = defines at least one needed constant and `inNeededClosure` = in the import
  closure of the needed modules (the closure that remains if imports are redirected but no
  declaration is moved);
* `cuts.tsv` — import edges `needed-closure module -> module outside it`, i.e. the places where
  an import has to be redirected / a declaration split out;
* `needed-consts.tsv` — `constant  module`.

It only reads `.olean`s; it proves nothing and declares nothing.
-/

open Lean

def candidateRoot (m : Name) : Bool :=
  let r := m.getRoot
  r == `ZkFormal || r == `ReexecV3D0 || r == `NpUdrStarkV2

partial def main (args : List String) : IO UInt32 := do
  match args with
  | outdir :: rest =>
    let (mods, consts) := rest.span (· != "--")
    let consts := consts.drop 1
    initSearchPath (← findSysroot)
    let env ← importModules (mods.toArray.map fun m => { module := m.toName }) {} (trustLevel := 1024)
    let names := env.header.moduleNames
    let idxOf : Std.HashMap Name Nat :=
      (names.foldl (init := (({} : Std.HashMap Name Nat), 0)) fun (m, i) n => (m.insert n i, i + 1)).1
    -- dependency walk
    let mut seen : NameSet := {}
    let mut todo : Array Name := consts.toArray.map (·.toName)
    for c in todo do
      if (env.find? c).isNone then
        IO.eprintln s!"unknown root constant {c}"; return 1
    while h : todo.size > 0 do
      let c := todo.back
      todo := todo.pop
      if seen.contains c then continue
      seen := seen.insert c
      let some ci := env.find? c | IO.eprintln s!"warning: missing constant {c}"; continue
      let mut nxt := ci.getUsedConstantsAsSet.toArray
      match ci with
      | .inductInfo v => nxt := nxt ++ v.ctors.toArray ++ v.all.toArray ++ v.all.toArray.map (· ++ `rec)
      | .ctorInfo v => nxt := nxt.push v.induct
      | .recInfo v => nxt := nxt ++ v.all.toArray
      | _ => pure ()
      if let some si := getStructureInfo? env c then
        nxt := nxt ++ si.fieldInfo.map (·.projFn)
      for n in nxt do
        unless seen.contains n do todo := todo.push n
    -- per module stats
    let nm := names.size
    let mut nConsts : Array Nat := Array.replicate nm 0
    let mut nNeed : Array Nat := Array.replicate nm 0
    for i in [0:nm] do
      nConsts := nConsts.set! i env.header.moduleData[i]!.constNames.size
    let mut rows : Array String := #[]
    for c in seen.toArray do
      match env.getModuleIdxFor? c with
      | some i => nNeed := nNeed.modify i.toNat (· + 1); rows := rows.push s!"{c}\t{names[i.toNat]!}"
      | none => rows := rows.push s!"{c}\t<current>"
    IO.FS.createDirAll outdir
    IO.FS.writeFile (outdir ++ "/needed-consts.tsv") (String.intercalate "\n" (rows.qsort (· < ·)).toList ++ "\n")
    let imps (i : Nat) : Array Name := env.header.moduleData[i]!.imports.map (·.module)
    -- import closure of the needed modules
    let mut inC : Array Bool := Array.replicate nm false
    let mut stack : Array Nat := #[]
    for i in [0:nm] do
      if nNeed[i]! > 0 then stack := stack.push i
    -- root modules themselves are always in the closure
    for m in mods do
      if let some i := idxOf[m.toName]? then stack := stack.push i
    while h : stack.size > 0 do
      let i := stack.back
      stack := stack.pop
      if inC[i]! then continue
      inC := inC.set! i true
      for j in imps i do
        if let some k := idxOf[j]? then stack := stack.push k
    let mut lines : Array String := #["module\tneeded\tinNeededClosure\tnConsts\tnNeededConsts\timports"]
    let mut cuts : Array String := #["from\tto"]
    for i in [0:nm] do
      let n := names[i]!
      lines := lines.push s!"{n}\t{decide (nNeed[i]! > 0)}\t{inC[i]!}\t{nConsts[i]!}\t{nNeed[i]!}\t{String.intercalate "," ((imps i).toList.map toString)}"
      if inC[i]! then
        for j in imps i do
          if let some k := idxOf[j]? then
            if !inC[k]! then cuts := cuts.push s!"{n}\t{j}"
    -- per module: the modules defining constants referenced by ANY constant of the module
    -- (`refs.tsv`, third column: only from its needed constants): the imports a module needs for its kernel terms if nothing is split.
    let mut refLines : Array String := #[]
    for i in [0:nm] do
      if candidateRoot names[i]! then
        let mut rs : Std.HashSet Nat := {}
        for ci in env.header.moduleData[i]!.constants do
          for n in ci.getUsedConstantsAsSet.toArray do
            if let some k := env.getModuleIdxFor? n then
              if k.toNat != i then rs := rs.insert k.toNat
        -- the same restricted to the module's needed constants
        let mut rn : Std.HashSet Nat := {}
        for ci in env.header.moduleData[i]!.constants do
          if seen.contains ci.name then
            for n in ci.getUsedConstantsAsSet.toArray do
              if let some k := env.getModuleIdxFor? n then
                if k.toNat != i then rn := rn.insert k.toNat
        let rl := (rs.toArray.qsort (· < ·)).toList.map fun k => toString names[k]!
        let rnl := (rn.toArray.qsort (· < ·)).toList.map fun k => toString names[k]!
        refLines := refLines.push s!"{names[i]!}\t{String.intercalate "," rl}\t{String.intercalate "," rnl}"
    IO.FS.writeFile (outdir ++ "/refs.tsv") (String.intercalate "\n" refLines.toList ++ "\n")
    IO.FS.writeFile (outdir ++ "/modules.tsv") (String.intercalate "\n" lines.toList ++ "\n")
    IO.FS.writeFile (outdir ++ "/cuts.tsv") (String.intercalate "\n" cuts.toList ++ "\n")
    let cand := (List.range nm).filter fun i => candidateRoot names[i]!
    let cnt (p : Nat → Bool) := (cand.filter p).length
    IO.println s!"constants needed: {seen.size}"
    IO.println s!"modules in closure: {nm} (candidate roots: {cand.length})"
    IO.println s!"candidate modules defining a needed constant: {cnt (nNeed[·]! > 0)}"
    IO.println s!"candidate modules in import closure of those: {cnt (inC[·]!)}"
    IO.println s!"cut edges: {cuts.size - 1}"
    return 0
  | _ => IO.eprintln "usage: ClosureDeps <outdir> <Module>... -- <const>..."; return 2
