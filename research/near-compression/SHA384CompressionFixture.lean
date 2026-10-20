import NearCompression.SHA512CombinedWitness
import NearCompression.SHA512Public
import ZkFormal.V2.Export
import Lean

/-! Single-block compression witness with SHA-384 IV. This executable fixture
does not claim a verified SHA-384 padding/truncation or recursive verifier. -/
open NearCompression ZkFormal.Air ZkFormal.Algebra NearSpecV3.SHA512 Lean
set_option maxRecDepth 65536

private def iv : List Nat := [0xcbbb9d5dc1059ed8,0x629a292a367cd507,
  0x9159015a3070dd17,0x152fecd8f70e5939,0x67332667ffc00b31,
  0x8eb44a8768581511,0xdb0c2e0d64f98fa7,0x47b5481dbefa4fa4]
private def limbs (words : List Nat) : List Fp :=
  words.flatMap fun w => (List.range 4).map fun i => Fp.ofNat (w/65536^i%65536)
private def values (v : Vars) : List Nat := [v.a,v.b,v.c,v.d,v.e,v.f,v.g,v.h]

def main (args : List String) : IO Unit := do
  let out := System.FilePath.mk (args.headD "/tmp/near-sha384-compression")
  IO.FS.createDirAll out
  let label := args[1]?.getD "empty"
  unless label == "empty" || label == "abc" do
    throw (IO.userError "supported fixture labels: empty, abc")
  -- Fixed one-block vectors; not a general message-padding implementation.
  let block := if label == "abc" then
      [7017280570803617792] ++ List.replicate 14 0 ++ [24]
    else 9223372036854775808 :: List.replicate 15 0
  let mut state := ofList iv
  let mut window := block
  let mut rows : Array (Array Fp) := #[]
  for r in List.range 128 do
    let key := K.getD r 0
    let core := ((List.range 5152).map (sha512CombinedWitnessRow state window key)).toArray
    let output := values (sha512CombinedOutput (fun c => core[c]?.getD 0))
    let phase := ((List.range 128).map fun c => if c=r then (1:Fp) else 0).toArray
    let ff := ((List.range 1664).map fun c => instructionAdd64Witness
      (UInt64.ofNat (iv.getD (c/208) 0)) (UInt64.ofNat (output.getD (c/208) 0)) (c%208)).toArray
    rows := rows.push (core ++ phase ++ ff)
    state := round state key (window.headD 0)
    window := nextWindow window
  let cell := fun r c => (rows[r]?.getD #[])[c]?.getD 0
  let result := sha512FeedForwardOutput (cell 79)
  let pub := limbs (iv ++ block ++ result)
  let tr : Trace Fp := ⟨fun _ => 7,fun _ r c => cell r c⟩
  unless (List.range 128).all (fun r => sha512PublicTable.constraints.all
      (fun e => decide (e.eval tr 0 r pub=0))) do
    throw (IO.userError "formal SHA compression AIR rejected witness")
  unless result == compress iv (sha512PublicBlock pub) do
    throw (IO.userError "source compression mismatch")
  let air : ZkFormal.V2.AirP := {
    tables := [sha512PublicTable]
    numBuses := 0
    numPub := 128
    maxPub := 128
    pubSegs := [] }
  IO.FS.writeFile (out/"spec.json") ("{\"air\":" ++ air.exportJson ++
    ",\"public\":" ++ (toJson (pub.map Fp.toNat)).compress ++ ",\"log_rows\":[7]}")
  IO.FS.writeFile (out/"source-00-rows.json")
    (Json.mkObj [("rows",toJson (rows.map (fun row => row.map Fp.toNat)))]).compress
  IO.FS.writeFile (out/"fixture.json") (Json.mkObj [
    ("message_hex",toJson (if label == "abc" then "616263" else "")),
    ("iv",toJson iv),("block_words",toJson block),
    ("output_words",toJson result),("rows",toJson 128),("width",toJson 6944),
    ("constraints",toJson sha512PublicTable.constraints.length),
    ("formal_air_evaluation",toJson true),("source_compression_matches",toJson true)]).compress
  IO.println "PASS: SHA384-IV compression fixture and formal AIR evaluation; external digest check required"
