import NearCompression.SHA384EndpointPublic
import Lean
open NearCompression ZkFormal.Algebra Lean

def main (args : List String) : IO Unit := do
  let input := System.FilePath.mk (args.headD "/tmp/near-sha384-framed-hash/message.bin")
  let output := System.FilePath.mk (args[1]?.getD "/tmp/near-sha384-endpoint/spec.json")
  let message := (← IO.FS.readBinFile input).data.toList
  let pub := (sha384EndpointPublic message (sha384ChainDigest message)).map Fp.toNat
  let air := sha384EndpointAir message.length
  let count := sha384PaddedLength message.length/128
  let mut endpointLog := 1
  while 2^endpointLog<count do endpointLog := endpointLog+1
  IO.FS.writeFile output ("{\"air\":" ++ air.exportJson ++ ",\"public\":" ++
    (toJson pub).compress ++ ",\"log_rows\":" ++
    (toJson (List.replicate count 7 ++ [endpointLog])).compress ++ "}")
  IO.println s!"exported {count} core tables plus {2^endpointLog} endpoint rows; {pub.length} public values"
