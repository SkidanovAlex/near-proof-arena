import NearCompression.CheckedMemoryHost
import NearSpecV3.SHA512
open NearSpec NearSpecV3 NearSpecV3.Wasm NearCompression

def hash512 (bs : Bytes) : ByteArray := ⟨(NearSpecV3.sha512 bs).toArray⟩
def initial (prepaid : Nat) : St := {
  pages := #[zeroPage], globals := #[], table := #[], tableMax := 0,
  elems := #[], datas := #[], stackRem := 262144, gas := Gas.init prepaid }
def ensure (ok : Bool) (label : String) : IO Unit :=
  unless ok do throw (IO.userError label)
def gasFields (g : Gas) :=
  (g.burnt, g.promises, g.prepaid, g.limit, g.g, g.host, g.action, g.special, g.sendCompute)
def sameView : EStateM.Result String (Gas × BlockDescriptor) Unit →
    EStateM.Result String (Gas × BlockDescriptor) Unit → Bool
  | .ok _ a, .ok _ b => gasFields a.1 == gasFields b.1 && decide (a.2 = b.2)
  | .error e a, .error f b => e == f && gasFields a.1 == gasFields b.1 && decide (a.2 = b.2)
  | _, _ => false

def runCase (name stage : String) (prepaid address length : Nat) : IO Unit := do
  let s := initial prepaid
  let data : ByteArray := ⟨Array.replicate length 17⟩
  let base := payBase s.gas C.writeMemoryBase
  let per := payPer base.1 C.writeMemoryByte data.size
  let observedStage := if base.2.isSome then "base" else if per.2.isSome then "byte"
    else if address + length > memBytes s then "bounds" else "success"
  ensure (observedStage == stage) s!"wrong failure stage: {name}"
  let ws := if stage == "success" then cachedWriteBytesWitness hash512 s 4096 16 4 address data
    else [⟨999, ByteArray.empty, [], [(999, 255)]⟩]
  let d := describeSubpageMemory hash512 s 4096 16 4
  let checked := checkMemoryHostWrite hash512 C.writeMemoryBase C.writeMemoryByte s.gas d address data ws
  let actual := (writeMemH address data).run s
  match checked with
  | none => throw (IO.userError s!"checker rejected honest host result: {name}")
  | some output => ensure (sameView output (memoryHostView hash512 4096 16 4 actual)) s!"host mismatch: {name}"
  let (error, final) := match actual with
    | .ok _ t => ("ok", t)
    | .error e t => (e, t)
  if stage != "success" then
    ensure (final.pages == s.pages) "failure wrote memory"
  else
    let direct := data.data.foldl (fun (acc : Nat × ByteArray) byte =>
      (acc.1 + 1, acc.2.set! acc.1 byte)) (address, zeroPage)
    ensure (final.pages == #[direct.2]) "successful host memory mismatch"
  IO.println s!"case={name} stage={stage} burnt={final.gas.burnt} host={final.gas.host} error={error}"

def main : IO Unit := do
  runCase "success_cross_block" "success" 1000000000000000 4090 32
  runCase "base_failure" "base" 0 0 32
  runCase "byte_failure" "byte" C.writeMemoryBase.gas 0 32
  runCase "bounds_failure" "bounds" 1000000000000000 65530 32
  runCase "gas_before_bounds" "base" 0 65530 32
  runCase "byte_before_bounds" "byte" C.writeMemoryBase.gas 65530 32
  runCase "empty_at_end" "success" 1000000000000000 65536 0
  runCase "empty_past_end" "bounds" 1000000000000000 65537 0
