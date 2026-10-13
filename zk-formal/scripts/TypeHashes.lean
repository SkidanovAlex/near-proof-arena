import Lean

/-!
# `TypeHashes` — fingerprint every declaration's statement

```
lake env lean --run scripts/TypeHashes.lean <out.tsv> <Module>...
```

Imports the given modules and writes `name  module  typeHash  kind` for every constant defined in a
`ZkFormal` / `ReexecV3D0` module (the hash is `Expr.hash` of the elaborated type, which is
structural: equal types hash equal, so a statement changed by an import restructuring shows up as
a differing line).  Used by the certificate-pruning lane to check that moving imports changed no
statement.  Reads `.olean`s only.
-/

open Lean

def main (args : List String) : IO UInt32 := do
  match args with
  | out :: mods =>
    initSearchPath (← findSysroot)
    let env ← importModules (mods.toArray.map fun m => { module := m.toName }) {} (trustLevel := 1024)
    let names := env.header.moduleNames
    let mut lines : Array String := #[]
    for i in [0:names.size] do
      let m := names[i]!
      let r := m.getRoot
      unless r == `ZkFormal || r == `ReexecV3D0 do continue
      for ci in env.header.moduleData[i]!.constants do
        let kind := match ci with
          | .thmInfo _ => "thm" | .defnInfo _ => "def" | .axiomInfo _ => "axiom"
          | .opaqueInfo _ => "opaque" | .inductInfo _ => "induct" | .ctorInfo _ => "ctor"
          | .recInfo _ => "rec" | .quotInfo _ => "quot"
        lines := lines.push s!"{ci.name}\t{m}\t{ci.type.hash}\t{kind}"
    IO.FS.writeFile out (String.intercalate "\n" (lines.qsort (· < ·)).toList ++ "\n")
    IO.println s!"{lines.size} constants"
    return 0
  | _ => IO.eprintln "usage: TypeHashes <out.tsv> <Module>..."; return 2
