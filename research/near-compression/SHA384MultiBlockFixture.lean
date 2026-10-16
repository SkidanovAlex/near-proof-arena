import NearCompression.SHA384Message
import Lean
open NearCompression ZkFormal.Algebra Lean

def main (args : List String) : IO Unit := do
  let input := System.FilePath.mk (args.headD "/tmp/near-sha384-framed-hash/message.bin")
  let output := System.FilePath.mk (args[1]?.getD "/tmp/near-sha384-multiblock/spec.json")
  let message := (← IO.FS.readBinFile input).data.toList
  let pub := (sha384MessagePublic message (sha384ChainDigest message)).map Fp.toNat
  let air := sha384MultiBlockAir message.length
  IO.FS.writeFile output ("{\"air\":" ++ air.exportJson ++ ",\"public\":" ++
    (toJson pub).compress ++ ",\"log_rows\":" ++
    (toJson (List.replicate air.tables.length 7)).compress ++ "}")
  IO.println s!"exported {air.tables.length} tables; {pub.length} public bytes; private bus-linked states"
