import ZkFormal.NearV3.Render.HonestRcptQ
import Lean.Data.Json

/-!
`np-lean-render-v3-rcpt <seed> <nlists> <view.json> <prefix.bin>` — the Lean honest
receipt rows of `nearAirV3` table 16 (`RcptV3.tableQ`) on a seeded native case, for the
byte differential against the Rust `src/v3/rcpt.rs`.

The installed honest render is `rcptTraceAlignedQ pub x = pinTrace (patchTrace (counterPatch
(rcptTraceNative pub x) 0 (physicalBoundaryRank …)) 0) 0` (`Render/HonestRcptQ.lean`,
`Render/HonestBalanceBnd.lean`, `Render/PaddedRcptR.lean`), always at height `2^22`.
`rcptTraceNative` is `booleanReceiptTrace own ctx lists 22 …` over the native inputs of a
`RcptInput`.  This executable evaluates **exactly that composition** of the zk-formal
definitions, with two documented substitutions (it cannot run a real chunk):

* the deposit ledger `depositPlanAccount x.steps` (which runs `schedStep` on a state trie) is
  replaced by a seeded per-receipt account function `accounts` (the account each receipt reads);
* the walk `k : WalkD0` is a default walk whose only read fields, `k.L` (layout) and
  `k.H.shardId`, are set to a seeded layout and own shard.

The free parameters of `RcptInput` are those of the accepted render
(`Assembly/RenderV3RcptAccepted.lean`): `constants`, `digests`, `headerFallback` zero / empty,
`fallback` = the access-key use rank on `uAK` (seeded here) and `0` elsewhere.

Output:
* `<view.json>`: the Rust `RcptIn` JSON — the honest list view
  `(nativeBlocks lists).map (ListBlock.view (rcptTraceNative pub x) 0)` (`nativeRcptLists`)
  with each receipt's native routing interval (`iv: {lo, hi}`: `nativeRoutingInterval k`)
  and the prepared values `own`, `height`, `bgp`;
* `<prefix.bin>`: u32 LE `log = 22, width, n`, then rows `0 … n−1` of the final trace
  row-major, `n` = planned rows + 8.  Rows `≥` the planned rows are checked to be zero in the
  native trace before the counter patch (`plannedTrace_padding`); rows `≥ n` are padding.

Evaluating all `2^22` rows is infeasible (each cell walks the plan), so only the prefix is
dumped; the Rust side checks the remaining rows itself.
-/

open Lean ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3
open NearSpec NearSpecV3
open ZkFormal.NearV3.Assembly.RcptSkeleton
open ZkFormal.NearV3.Assembly.RoutingQCandidate
open ZkFormal.NearV3.Assembly.RoutingBoundedLayout

deriving instance Inhabited for NearSpec.PublicKey
deriving instance Inhabited for NearSpec.Receipt
deriving instance Inhabited for NearSpecV3.Congestion
deriving instance Inhabited for NearSpecV3.ChunkInner
deriving instance Inhabited for NearSpecV3.Claim
deriving instance Inhabited for NearSpecV3.Layout
deriving instance Inhabited for NearSpecV3.WalkD0

namespace RcptConf

def W : Nat := RcptV3.width

/-! ## Seeded generator -/

abbrev Gen := StateM Nat

def next : Gen Nat := do
  let s ← get
  let s' := (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64
  set s'
  return s' / 2 ^ 16

def below (n : Nat) : Gen Nat := do return (← next) % (max n 1)

def coin : Gen Bool := do return (← below 2) == 0

def big (bits : Nat) : Gen Nat := do
  let mut x := 0
  for _ in [0:(bits + 47) / 48] do
    x := x * 2 ^ 48 + (← next) % 2 ^ 48
  return x % 2 ^ bits

def bytesG (n : Nat) : Gen Bytes := do
  let mut out : Bytes := []
  for _ in [0:n] do
    out := out ++ [(← below 256).toUInt8]
  return out

def str (s : String) : Bytes := s.toUTF8.toList

def alnum : List UInt8 := str "abcdefghijklmnopqrstuvwxyz0123456789"

/-- A random valid named account id of length `2 … 12`, sometimes with one separator. -/
def nameG : Gen Bytes := do
  let len := 2 + (← below 11)
  let mut out : Bytes := []
  for _ in [0:len] do
    out := out ++ [alnum.getD (← below 36) 97]
  if len ≥ 4 ∧ (← below 3) == 0 then
    let k := 1 + (← below (len - 2))
    out := out.set k ((str "._-").getD (← below 3) 46)
  return if AccountId.valid out && AccountId.isNamed out then out else str "zz"

def boundaries : List Bytes := [str "carol", str "mike", str "tom"]

def layout : Layout := ⟨boundaries, [3, 7, 3, 9], [(3, 0), (7, 1), (9, 3)]⟩

/-- A receiver routed to `own` (rejection sampling, boundary prefixes included). -/
def receiverG (own : Nat) (used : List Bytes) : Gen Bytes := do
  if ¬used.isEmpty ∧ (← below 3) == 0 then
    return used.getD (← below used.length) (str "zz")
  for _ in [0:200] do
    let n ← nameG
    let cand ← match ← below 4 with
      | 0 => do
        let b := boundaries.getD (← below 3) []
        let suffix ← if ← coin then pure [] else nameG
        pure ((b ++ suffix).take 64)
      | _ => pure n
    if AccountId.valid cand && AccountId.isNamed cand && (selectInterval layout own cand).isSome then
      return cand
  return match own with
    | 7 => str "carol"
    | 9 => str "tom"
    | _ => str "aa"

structure Native where
  r : Receipt
  acct : Account
  aid : Nat
  access : Option Nat
  aku : Nat

def signerG (sys : Bool) (p v : Bytes) : Gen Bytes := do
  if sys then
    let m ← below 3
    if m == 0 then return v
    if m == 1 then
      -- same length, one byte different (`dd`)
      let k ← below v.length
      let ch := alnum.getD (← below 36) 97
      let t := v.set k ch
      return (if AccountId.valid t then t else v)
    nameG
  else
    if ← coin then return p
    nameG

def receiptG (own bgp : Nat) (used : List Bytes) : Gen Native := do
  let sys := (← below 4) == 0
  let v ← receiverG own used
  let p ← if sys then pure AccountId.system else nameG
  let s ← signerG sys p v
  let tag ← below 2
  let pk ← bytesG (32 + 32 * tag)
  let rid ← bytesG 32
  let gp ← match ← below 7 with
    | 0 => pure 0
    | 1 => pure bgp
    | 2 => do pure (bgp + 1 + (← below 1000))
    | 3 => do pure ((← big 64) % (bgp + 1))
    | 4 => big 64
    | 5 => if sys then pure (2 ^ 128 - 1) else big 80
    | _ => do pure (bgp + (← big 40))
  let dep ← match ← below 4 with
    | 0 => pure 0
    | 1 => big 64
    | 2 => big 100
    | _ => big 20
  let acct ← if ← coin then do
      let st ← below 3000
      let amt := (← big 100) + 10 ^ 19 * st
      pure (⟨amt, ← big 64, [], st⟩ : Account)
    else do
      let st ← below 771
      pure (⟨← big 40, ← big 30, [], st⟩ : Account)
  let aid ← below P
  let access ← if ← coin then pure (some (← below P)) else pure none
  let aku ← below 5
  return ⟨⟨p, v, rid, s, ⟨tag, pk⟩, gp, dep⟩, acct, aid, access, aku⟩

structure Case where
  own : Nat
  height : Nat
  bgp : Nat
  lists : List (List Native)

def caseG (nl : Nat) : Gen Case := do
  let own := [3, 7, 9].getD (← below 3) 3
  let height ← big 64
  let bgp ← match ← below 3 with
    | 0 => pure 0
    | 1 => below (2 ^ 20)
    | _ => big 60
  let mut lists : List (List Native) := []
  let mut used : List Bytes := []
  for _ in [0:max nl 1] do
    let m ← below 4
    let mut xs : List Native := []
    for _ in [0:m] do
      let x ← receiptG own bgp used
      used := used ++ [x.r.receiverId]
      xs := xs ++ [x]
    lists := lists ++ [xs]
  return ⟨own, height, bgp, lists⟩

/-! ## The honest render -/

def Case.ctx (c : Case) : ApplyCtx := ⟨c.height, [], c.bgp, 0, layout, c.own, [], []⟩

def Case.walk (c : Case) : WalkD0 :=
  { (default : WalkD0) with L := layout, H := { (default : ChunkInner) with shardId := c.own } }

def Case.flat (c : Case) : List Native := c.lists.flatten

def Case.inputs (c : Case) : List (List Input) :=
  c.lists.map (List.map fun x => ⟨x.r, nativeRefund c.ctx x.r⟩)

def Case.at (c : Case) (p : ReceiptPlan) : Native :=
  c.flat.getD p.receiptIndex ⟨default, ⟨0, 0, [], 0⟩, 0, none, 0⟩
def Case.accounts (c : Case) (p : ReceiptPlan) : Account := (c.at p).acct
def Case.accountId (c : Case) (p : ReceiptPlan) : Nat := (c.at p).aid
def Case.accessId (c : Case) (p : ReceiptPlan) : Option Nat := (c.at p).access

/-- The receipt fallback: only `uAK`, the access-key use rank (the accepted render's
`NativeAccessKeyRanks.rankAux` shape, seeded values), everything else `0`. -/
def Case.fallback (c : Case) (p : ReceiptPlan) (_ : Coord) (col : Nat) : Fp :=
  if col = RcptV3.uak then Fp.ofNat (c.at p).aku else 0

def put (pub : List Fp) (at_ : Nat) (bs : Bytes) : List Fp :=
  (List.range pub.length).map fun i =>
    if at_ ≤ i ∧ i < at_ + bs.length then Fp.ofNat ((bs.getD (i - at_) 0).toNat) else pub.getD i 0

/-- The prepared public values the rows read (`RcptOk.gasPub`, `finalPub`, `owner`). -/
def Case.pub (c : Case) : List Fp :=
  let rs := c.flat.map (·.r)
  let n := rs.length
  let burnt := (rs.map (nativeBurn c.ctx)).sum
  let blen := 8 + (c.inputs.flatten.map refundLength).sum
  let p0 : List Fp := List.replicate 202 0
  let p1 := put p0 PH_N (u32 n)
  let p2 := put p1 PH_OWN (u64 c.own)
  let p3 := put p2 PH_HEIGHT (u64 c.height)
  let p4 := put p3 PH_GP (u128 c.bgp)
  let p5 := put p4 PH_BURNT (u128 burnt)
  put p5 PH_BLEN (u32 blen)

/-- `rcptTraceNative pub x` with zero free parameters (see the module doc). -/
def Case.native (c : Case) : Trace Fp :=
  let lists := c.inputs
  booleanReceiptTrace c.own c.ctx lists 22
    (completeReceiptConstants c.ctx c.walk c.accountId
      (depositConstants c.accounts (depositAgeConstants (depositPlanPrevious lists) (fun _ _ => 0))))
    c.pub (nativeDigests c.ctx (fun _ _ => []))
    (completeReceiptAux c.ctx c.walk lists c.accountId c.accessId
      (depositFinalAux (depositPlanPrevious lists) c.accounts c.fallback))
    (completeReceiptHeaders (depositHeaderAux (fun _ _ _ => 0)))

def materialize (tr : Trace Fp) (n : Nat) : Array Fp := Id.run do
  let mut a : Array Fp := Array.mkEmpty (n * W)
  for r in [0:n] do
    for col in [0:W] do
      a := a.push (tr.cell 0 r col)
  return a

def ofArray (a : Array Fp) (n : Nat) : Trace Fp :=
  ⟨fun _ => 22, fun _ r col => if r < n ∧ col < W then a.getD (r * W + col) 0 else 0⟩

/-! ## JSON (the Rust `RcptIn` mirror) -/

def jn (xs : List Nat) : Json := Json.arr (xs.map toJson).toArray
def jb (xs : Bytes) : Json := jn (xs.map UInt8.toNat)
def jbs (xs : List Bool) : Json := Json.arr (xs.map toJson).toArray

def rcptJson (e : RcptE) (iv : Option Bytes × Option Bytes) : Json :=
  Json.mkObj [
    ("p", jn e.p), ("v", jn e.v), ("s", jn e.s), ("rid", jn e.rid), ("kt", toJson e.kt),
    ("pk", jn e.pk), ("gp", jn e.gp), ("dep", jn e.dep), ("hr", toJson e.hr), ("ge", toJson e.ge),
    ("kslot", toJson e.kslot), ("tprev", toJson e.tprev), ("bef", jn e.bef), ("lk", jn e.lk),
    ("st", jn e.st), ("aft", jn e.aft), ("burnt", jn e.burnt), ("ramt", jn e.ramt),
    ("rfid", jn e.rfid), ("peoh", jn e.peoh), ("sys", toJson e.sys), ("ee", toJson e.ee),
    ("gv", jbs e.gv), ("gs", jbs e.gs), ("sx", jn e.sx), ("akf", toJson e.akf),
    ("akk", toJson e.akk), ("aku", toJson e.aku), ("q", toJson e.q),
    ("rlk", Json.arr (e.rlk.map fun (pos, lo, hi, hn, u) =>
      Json.mkObj [("pos", toJson pos), ("lo", toJson lo), ("hi", toJson hi), ("hn", toJson hn),
        ("u", toJson u)]).toArray),
    ("iv", Json.mkObj [("lo", match iv.1 with | some b => jb b | none => Json.null),
      ("hi", match iv.2 with | some b => jb b | none => Json.null)])]

def u32b (b : ByteArray) (x : Nat) : ByteArray :=
  b.push (x % 256).toUInt8 |>.push (x / 256 % 256).toUInt8
    |>.push (x / 65536 % 256).toUInt8 |>.push (x / 16777216 % 256).toUInt8

end RcptConf

open RcptConf in
def main (args : List String) : IO UInt32 := do
  match args with
  | [seedS, nlS, viewF, binF] =>
    let seed := seedS.toNat!
    let nl := nlS.toNat!
    let c := (caseG nl).run' (seed * 2654435761 + 12345) |>.run
    let lists := c.inputs
    let rows := (plannedRows lists).length
    let n := rows + 8
    let tN := c.native
    let a := materialize tN n
    -- padding rows of the native trace are zero
    for r in [rows:n] do
      for col in [0:W] do
        if (a.getD (r * W + col) 0).toNat != 0 then
          IO.eprintln s!"native padding row {r} col {col} is nonzero"
          return 1
    let tM := ofArray a n
    let tQ := patchTrace (counterPatch tM 0 (physicalBoundaryRank tM 0)) 0
    let mut b := u32b (u32b (u32b ByteArray.empty 22) W) n
    for r in [0:n] do
      for col in [0:W] do
        b := u32b b (tQ.cell 0 r col).toNat
    IO.FS.writeBinFile binF b
    -- the honest list view (`nativeRcptLists`, read on the native rows) + intervals
    let views := (nativeBlocks lists).map (RcptV3Proof.ListBlock.view tM 0)
    let ivs := c.flat.map fun x =>
      (boundedIntervals c.walk.L c.walk.H.shardId).getD (nativeRoutingIndex c.walk x.r) (none, none)
    let mut k := 0
    let mut ls : Array Json := #[]
    for v in views do
      let mut rs : Array Json := #[]
      for e in v.rs do
        rs := rs.push (rcptJson e (ivs.getD k (none, none)))
        k := k + 1
      ls := ls.push (Json.mkObj [("n0", toJson v.n0), ("n1", toJson v.n1), ("rs", Json.arr rs)])
    let j := Json.mkObj [("lists", Json.arr ls), ("own", toJson c.own),
      ("height", toJson c.height), ("bgp", toJson c.bgp)]
    IO.FS.writeFile viewF j.compress
    IO.println s!"rcpt seed {seed}: {c.flat.length} receipts in {c.lists.length} lists, {rows} planned rows, dumped {n}"
    return 0
  | _ =>
    IO.eprintln "usage: np-lean-render-v3-rcpt <seed> <nlists> <view.json> <prefix.bin>"
    return 2
