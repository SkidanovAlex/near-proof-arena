import ZkFormal.V3.Fast.Prep
import ZkFormal.NearV3.Assembly.HintCodec
import ZkFormal.NearV3.Public.Prepared
import NearSpecV3.ChallengeD0a
import Lean.Data.Json

/-!
`np-lean-prep-v3 <case_dir> [<outdir>]` — part 3 of `np-udr-stark-v2`: the Lean
side of the `prepD0` / `Hint` byte-codec differential.

Reads `case_dir/claim.bin` and `case_dir/witness.bin`; requires
`checkD0a B0 cb wb = .ok ()` (the deployed D0a relation, = `RelD0a B0`), then
computes

* `h := NearSpecV3.hintOf cb wb`  (the proof-carried hint),
* `p := NearSpecV3.prepD0 cb h`   (the prepared statement),

and writes a JSON object to stdout (or to `<outdir>/prep.json`):

```
{ "hint": <hex of ZkFormal.NearV3.Assembly.Hint.encode h>,
  "prep": <hex of NearSpecV3.Prep.encode p>,
  "refunds_enc": <hex of encodeReceipts (decodeBody h.body)>,
  "prep_json": <the Prep structure with Lean field names> }
```

The Rust `Prep` codec (`../source/src/v3/prep.rs`) re-encodes `prep_json` and the
bytes must equal `prep`; the `Hint` codec decodes+re-encodes `hint`; and the
refund body codec round-trips against `refunds_enc`.

The JSON uses explicit `Nat`/`Bool`/`List`/`Option`/product encodings
(`Lean.Data.Json`'s `ToJson` instances) — no `UInt8`, whose `ToJson` instance the
core library does not provide; byte strings are arrays of naturals.
-/

open Lean ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3

/-! ## JSON helpers -/

def jn (n : Nat) : Json := toJson n
def jbytes (b : Bytes) : Json := Json.arr (b.map (fun x => jn x.toNat)).toArray
def joptBytes : Option Bytes → Json
  | none => Json.null
  | some b => jbytes b

def jsonHdr (h : PrepHdr) : Json := Json.mkObj
  [ ("K", jn h.K), ("n", jn h.n), ("own", jn h.own), ("ownIdx", jn h.ownIdx)
  , ("numShards", jn h.numShards), ("height", jn h.height), ("gasPrice", jn h.gasPrice)
  , ("gasLimit", jn h.gasLimit), ("prevStateRoot", jbytes h.prevStateRoot)
  , ("postStateRoot", jbytes h.postStateRoot), ("outcomeRoot", jbytes h.outcomeRoot)
  , ("balanceBurnt", jn h.balanceBurnt) ]

def jsonSrcList (s : SrcList) : Json := Json.mkObj
  [ ("key", jbytes s.key), ("fromShard", jn s.fromShard), ("root", jbytes s.root) ]

def jsonParams (p : Scheduler.Params) : Json := Json.mkObj
  [ ("base", jn p.base), ("maxShardBandwidth", jn p.maxShardBandwidth)
  , ("maxSingleGrant", jn p.maxSingleGrant), ("maxReceiptSize", jn p.maxReceiptSize)
  , ("maxAllowance", jn p.maxAllowance) ]

def jsonBR (b : Scheduler.BandwidthRequest) : Json := Json.mkObj
  [ ("toShard", jn b.toShard), ("bitmap", jbytes b.bitmap) ]

def jsonSchedPub (p : Scheduler.SchedPub) : Json := Json.mkObj
  [ ("ids", Json.arr (p.ids.map jn).toArray)
  , ("params", jsonParams p.params)
  , ("allowed", Json.arr (p.allowed.toList.map (fun b => toJson b)).toArray)
  , ("raw", Json.arr (p.raw.map (fun (s, brs) =>
      Json.arr #[jn s, Json.arr (brs.map jsonBR).toArray])).toArray)
  , ("values", Json.arr (p.values.map jn).toArray)
  , ("seed", jbytes p.seed)
  , ("allShardsHash", jbytes p.allShardsHash) ]

def jsonPrep (p : Prep) : Json := Json.mkObj
  [ ("hdr", jsonHdr p.hdr)
  , ("lists", Json.arr (p.lists.map jsonSrcList).toArray)
  , ("bnds", Json.arr (p.bnds.map (fun (lo, hi) =>
      Json.arr #[joptBytes lo, joptBytes hi])).toArray)
  , ("sched", Json.arr (p.sched.map jsonSchedPub).toArray)
  , ("body", jbytes p.body)
  , ("fwd", Json.arr (p.fwd.map (fun (s, t) => Json.arr #[jn s, jn t])).toArray) ]

/-! ## Hex -/

def hexChar (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

def toHex (b : Bytes) : String :=
  String.ofList (b.flatMap (fun x =>
    [hexChar (x.toNat / 16), hexChar (x.toNat % 16)]))

/-! ## Main -/

def runCase (outDir : Option String) (dir : String) : IO UInt32 := do
  let cb := (← IO.FS.readBinFile (dir ++ "/claim.bin")).toList
  let wb := (← IO.FS.readBinFile (dir ++ "/witness.bin")).toList
  match checkD0a B0 cb wb with
  | .error e =>
    IO.eprintln s!"np-lean-prep-v3: {dir}: checkD0a failed: {e}"; return 2
  | .ok () =>
    let h := hintOf cb wb
    match prepD0 cb h with
    | .error e =>
      IO.eprintln s!"np-lean-prep-v3: {dir}: prepD0 failed: {e}"; return 2
    | .ok p =>
      let refundsEnc := match decodeBody h.body with
        | .ok rs => encodeReceipts rs
        | .error _ => []
      let j := Json.mkObj
        [ ("hint", toJson (toHex (Hint.encode h)))
        , ("prep", toJson (toHex (Prep.encode p)))
        , ("public", toJson (toHex (ZkFormal.NearV3.Public.preparedBytes p 0)))
        , ("refunds_enc", toJson (toHex refundsEnc))
        , ("prep_json", jsonPrep p) ]
      let s := Json.compress j
      match outDir with
      | none => IO.println s
      | some od =>
        IO.FS.createDirAll od
        IO.FS.writeFile (od ++ "/prep.json") s
      return 0

/-! ## `--any`: the total differential (accepted and rejected cases)

`np-lean-prep-v3 --any <claim.bin> <witness.bin> [<hint.bin>]` does **not** require
`checkD0a`: it prints `{ "check": "ok" | <error>, "hint": <hex of Hint.encode (hintOf cb wb)>,
"prep": <hex of Prep.encode p> | null, "prep_err": null | <error> }` where `p := prepD0 cb h`
and `h` is `hintOf cb wb`, or the hint decoded from `<hint.bin>` (`Hint.decode`) when given.
The Rust prover's `npudr v3prepare` must produce the same hint bytes and the same
accept/reject verdict and prepared bytes; every claim `checkD0a B0` rejects must be rejected. -/

def runAny (cbPath wbPath : String) (hintPath : Option String) : IO UInt32 := do
  let cb := (← IO.FS.readBinFile cbPath).toList
  let wb := (← IO.FS.readBinFile wbPath).toList
  let check : Json := match checkD0a B0 cb wb with
    | .ok () => toJson "ok"
    | .error e => toJson e
  let hOf := hintOf cb wb
  let mut h := hOf
  if let some hp := hintPath then
    let hb := (← IO.FS.readBinFile hp).toList
    match Hint.decode hb with
    | some h' => h := h'
    | none => IO.eprintln s!"np-lean-prep-v3: {hp}: Hint.decode failed"; return 2
  let (prep, err) : Json × Json := match prepD0 cb h with
    | .ok p => (toJson (toHex (Prep.encode p)), Json.null)
    | .error e => (Json.null, toJson e)
  IO.println (Json.compress (Json.mkObj
    [ ("check", check), ("hint", toJson (toHex (Hint.encode hOf))), ("prep", prep)
    , ("prep_err", err) ]))
  return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--any", cb, wb] => runAny cb wb none
  | ["--any", cb, wb, hb] => runAny cb wb (some hb)
  | [dir] => runCase none dir
  | [dir, outDir] => runCase (some outDir) dir
  | _ => IO.eprintln "usage: np-lean-prep-v3 <case_dir> [<outdir>] | --any <claim.bin> <witness.bin> [<hint.bin>]"; return 2
