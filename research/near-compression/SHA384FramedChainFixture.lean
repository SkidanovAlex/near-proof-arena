import NearCompression.SHA384Chain
import NearCompression.SHA512CombinedWitness
import NearCompression.SHA512Chain
import ZkFormal.V2.Export
import Lean

/-! Full-message SHA384 adaptation of the existing compression/chain semantics.
Padding and state links are explicit verifier-side checks, not a recursive AIR.
Each exported block is an actual canonical sha512PublicTable trace. -/
open NearCompression ZkFormal.Air ZkFormal.Algebra NearSpecV3.SHA512 Lean
set_option maxRecDepth 65536



private def limbs (ws : List Nat) : List Fp :=
  ws.flatMap fun w => (List.range 4).map fun i => Fp.ofNat (w/65536^i%65536)
private def values (v : Vars) : List Nat := [v.a,v.b,v.c,v.d,v.e,v.f,v.g,v.h]

def main (args : List String) : IO Unit := do
  let input := System.FilePath.mk (args.headD "/tmp/near-sha384-framed-hash/message.bin")
  let out := System.FilePath.mk (args[1]?.getD "/tmp/near-sha384-framed-hash/chain")
  let message := (← IO.FS.readBinFile input).data.toList
  let padded := pad (message.map UInt8.toNat)
  unless padded.length%128==0 do throw (IO.userError "padding alignment")
  IO.FS.createDirAll out
  let air : ZkFormal.V2.AirP := {
    tables := [sha512PublicTable]
    numBuses := 0
    numPub := 128
    maxPub := 128
    pubSegs := [] }
  let mut initial := sha384ChainIV
  let mut items : List SHA512ChainItem := []
  let mut reports : Array Json := #[]
  for bi in List.range (padded.length/128) do
    let blockBytes := (padded.drop (128*bi)).take 128
    let block := words blockBytes
    let mut state := ofList initial
    let mut window := block
    let mut rows : Array (Array Fp) := #[]
    for r in List.range 128 do
      let key := K.getD r 0
      let core := ((List.range 5152).map (sha512CombinedWitnessRow state window key)).toArray
      let output := values (sha512CombinedOutput (fun c => core[c]?.getD 0))
      let phase := ((List.range 128).map fun c => if c=r then (1:Fp) else 0).toArray
      let ff := ((List.range 1664).map fun c => instructionAdd64Witness
        (UInt64.ofNat (initial.getD (c/208) 0)) (UInt64.ofNat (output.getD (c/208) 0)) (c%208)).toArray
      rows := rows.push (core ++ phase ++ ff)
      state := round state key (window.headD 0)
      window := nextWindow window
    let cell := fun r c => (rows[r]?.getD #[])[c]?.getD 0
    let result := sha512FeedForwardOutput (cell 79)
    let pub := limbs (initial ++ block ++ result)
    let tr : Trace Fp := ⟨fun _ => 7,fun _ r c => cell r c⟩
    unless (List.range 128).all (fun r => sha512PublicTable.constraints.all
        (fun e => decide (e.eval tr 0 r pub=0))) do
      throw (IO.userError s!"formal SHA compression AIR rejected block {bi}")
    unless result==compress initial blockBytes do throw (IO.userError "compression source mismatch")
    let dir := out/s!"block-{bi}"
    IO.FS.createDirAll dir
    IO.FS.writeFile (dir/"spec.json") ("{\"air\":" ++ air.exportJson ++
      ",\"public\":" ++ (toJson (pub.map Fp.toNat)).compress ++ ",\"log_rows\":[7]}")
    IO.FS.writeFile (dir/"source-00-rows.json")
      (Json.mkObj [("rows",toJson (rows.map (fun row => row.map Fp.toNat)))]).compress
    reports := reports.push (Json.mkObj [("block_index",toJson bi),("initial_words",toJson initial),
      ("block_bytes",toJson blockBytes),("block_words",toJson block),("output_words",toJson result),
      ("formal_air_evaluation",toJson true),("source_compression_matches",toJson true)])
    items := items ++ [⟨pub,tr⟩]
    initial := result
    IO.println s!"checked canonical compression block {bi+1}/{padded.length/128}"
  unless sha512ChainBoundaryCheck sha384ChainIV padded initial items do
    throw (IO.userError "full padded message chain boundary rejected")
  unless initial==blocks items.length sha384ChainIV padded do
    throw (IO.userError "whole message source mismatch")
  let digest := (digestBytes initial).take 48
  unless digest==sha384ChainDigest message do throw (IO.userError "SHA384 digest source mismatch")
  IO.FS.writeFile (out/"chain.json") (Json.mkObj [
    ("message_bytes",toJson (message.map UInt8.toNat)),("padded_bytes",toJson padded),
    ("iv",toJson sha384ChainIV),("final_words",toJson initial),
    ("digest_bytes",toJson (digest.map UInt8.toNat)),("blocks",Json.arr reports),
    ("chain_boundary_check",toJson true),("block_count",toJson items.length),
    ("rows_per_block",toJson 128),("width",toJson 6944),
    ("constraints_per_row",toJson sha512PublicTable.constraints.length)]).compress
  IO.println "PASS: full framed message SHA384 chain; external hashlib check required"
