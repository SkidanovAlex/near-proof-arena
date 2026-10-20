import NearCompression.SHA384TranscriptDraw
import Lean
open NearCompression Lean

def main (args : List String) : IO Unit := do
  let j ← match Json.parse (← IO.FS.readFile args[0]!) with
    | .ok x=>pure x | .error e=>throw (IO.userError e)
  let rows ← match j.getArr? with |.ok x=>pure x|.error e=>throw (IO.userError e)
  let mut out : Array Json := #[]
  for row in rows do
    let get (α : Type) [FromJson α] (key : String) : IO α :=
      match row.getObjValAs? α key with |.ok x=>pure x|.error e=>throw (IO.userError e)
    let seed ← get (List Nat) "seed"
    let label ← get (List Nat) "label"
    let count ← get Nat "count"
    let coefficients ← get Nat "coefficients"
    let maxBlocks ← get Nat "max_blocks"
    let mode ← get Bool "actual_hash"
    let oracle ← get (List ((List Nat × List (List Nat)) × List Nat)) "oracle"
    unless seed.all (·<256) && label.all (·<256) && oracle.all (fun e=>
        e.1.1.all (·<256) && e.1.2.all (fun p=>p.all (·<256)) && e.2.all (·<256)) do
      throw (IO.userError "noncanonical byte")
    let hash : SHA384HashFunction := if mode then sha384ModelHash else fun tag parts=>
      ((oracle.find? (fun e=>e.1.1==tag.map UInt8.toNat && e.1.2==parts.map (List.map UInt8.toNat))).map Prod.snd).getD [] |>.map UInt8.ofNat
    let initial := seed.map UInt8.ofNat
    let result := sha384TranscriptDraw hash initial (label.map UInt8.ofNat) count coefficients maxBlocks
    let value := match result with
      |none=>Json.mkObj [("accepted",toJson false),("seed",toJson seed)]
      |some r=>Json.mkObj [("accepted",toJson true),("seed",toJson (r.nextSeed.map UInt8.toNat)),
        ("values",toJson r.values),("blocks",toJson r.blocks),("rejected",toJson r.rejected)]
    out:=out.push value
  IO.FS.writeFile args[1]! (toJson out).compress
