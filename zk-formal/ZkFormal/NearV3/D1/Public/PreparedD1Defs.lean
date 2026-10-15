import ZkFormal.NearV3.Public.PreparedDefs
import ZkFormal.NearV3.D1.Ids

/-!
# `ZkFormal.NearV3.D1.Public.PreparedD1Defs` — the prepared statement of `nearAirV3D1`

Lane `v3-d1-tables`.  Definitions only (verifier-model import rule).

The D1 prepared statement is the D0a one (same 202-byte header layout, the nine D0a segments
at the same descriptor offsets `202 + 8·i`) with
* the header's `n` (`PH_N`) = **all** outcome leaves `M0 + n` (`mrkV3` reads it), the tag
  `near-arena-prep-d1a-v0` (same length as D0a's, so every static offset is unchanged), the
  body `B` = the whole Reed–Solomon body `u32 |newTxs| ‖ newTxs ‖ encodeReceipts (fwd ++
  local refunds ++ refunds)`;
* six more segments (descriptors `9 … 14`): the body prefix `8 … O0 − 1` **sent** back on
  `BYTES` (it cancels the D0a body segment's receive there: only the incoming receipts'
  refunds, from `O0` on, are `rcptV3D1`'s), `TXP`, `SIG`, `PKEY`, `PLEAF`, `PRID`; `PKEY`
  carries the candidates' walks, then the unread-key walks (`uwalks`, lane v3-d1-a7b);
* the 28-byte extension `u32 M0 ‖ u32 T0 ‖ u32 O0 ‖ u128 TOK0` at `E0 = 322`, after the 15
  descriptors and before the payloads.
-/

namespace ZkFormal.NearV3.D1.Public

open ZkFormal.V2 NearSpec NearSpecV3 ZkFormal.NearV3.Public ZkFormal.NearV3.D1

/-! ## The AIR-facing prepared data -/

/-- One `txV3` op (`TXP` lanes are its bytes, `SIG` its `valid` bit). -/
structure TxOp where
  /-- `0` debit (transaction), `1` credit (local receipt) -/
  kind : Nat
  strict : Nat
  ok : Nat
  tov : Nat
  stage : Nat
  cok : Nat
  valid : Nat
  /-- `t.nonce` (`u64`) -/
  nonce : Nat
  /-- `min(height·10⁶, 2⁶⁴ − 1)` (`u64`) -/
  bound : Nat
  /-- `totalCost` (debit) or the deposit (credit), `u128` -/
  amount : Nat
  deriving Repr, DecidableEq, Inhabited

/-- A transaction walk: walk id and the trie key (account `[0] ‖ signer` or access key). -/
structure KeyWalk where
  w : Nat
  key : Bytes
  deriving Repr, DecidableEq, Inhabited

/-- The D1 prepared statement: the D0a-shaped part plus the D1 public data. -/
structure PrepD1 where
  base : Prep
  m0 : Nat
  t0 : Nat
  o0 : Nat
  tok0 : Nat
  ops : List TxOp
  /-- the candidates' and credits' walks (`walkV3`, `KEYNIB`) -/
  walks : List KeyWalk
  /-- outcome leaf digests `0 … M0 − 1` -/
  leaves : List Bytes
  /-- local receipt ids -/
  rids : List Bytes
  /-- the unread-key walks (`walkU`, `UKEYNIB`; ids `≥ W_UNR`): every `txKeys` entry, plan §5
  R-5 → (B) -/
  uwalks : List KeyWalk := []

/-! ## Payloads -/

def byteAt (x i : Nat) : Nat := (x / 256 ^ i) % 256

def opLane (o : TxOp) (i : Nat) : List Nat :=
  [o.kind, o.strict, o.ok, o.tov, o.stage, o.cok, byteAt o.nonce i, byteAt o.bound i, byteAt o.amount i]

def txpPayload (ops : List TxOp) : Payload :=
  ops.flatMap fun o => (List.range LANES).map fun i => (opLane o i).map UInt8.ofNat

def sigPayload (ops : List TxOp) : Payload := ops.map fun o => [UInt8.ofNat o.valid]

/-- `(w₀, w₁, w₂, t, sym, last)`: the key's nibbles (high first), then `END`. -/
def walkRecs (k : KeyWalk) : List (List Nat) :=
  let w := [byteAt k.w 0, byteAt k.w 1, byteAt k.w 2]
  let nibs := k.key.flatMap fun b => [b.toNat / 16, b.toNat % 16]
  (nibs.zipIdx.map fun (s, t) => w ++ [t, s, 0]) ++ [w ++ [nibs.length, ZkFormal.Near.SYM_END, 1]]

def keyPayload (ws : List KeyWalk) : Payload := ws.flatMap fun k => (walkRecs k).map (·.map UInt8.ofNat)

def leafPayload (ls : List Bytes) : Payload := ls

def ridPayload (ids : List Bytes) : Payload := ids.flatMap fun d => d.map fun b => [b]

/-- Body positions `8 … O0 − 1` (sent; they cancel the D0a body segment's receive there). -/
def prefixPayload (body : Bytes) (o0 : Nat) : Payload := ((body.take o0).drop 8).map fun b => [b]

/-! ## Segments -/

def bodyPrefixPlan : PubSeg :=
  { bus := 0, send := true, width := 1, countAt := 0, start := 0, msgPrefix := [2], indexBase := some 8 }
def txpPlan : PubSeg :=
  { bus := B_TXP, send := true, width := 9, countAt := 0, start := 0, indexBase := some 0 }
def sigPlan : PubSeg :=
  { bus := B_SIG, send := true, width := 1, countAt := 0, start := 0, indexBase := some 0 }
def keyPlan : PubSeg := plainPlan B_PKEY true 6
def leafPlan : PubSeg :=
  { bus := B_PLEAF, send := true, width := 32, countAt := 0, start := 0, indexBase := some 0 }
def ridPlan : PubSeg :=
  { bus := B_PRID, send := true, width := 1, countAt := 0, start := 0, indexBase := some 0 }

/-- The 15 descriptors: D0a's nine, then the D1 six. -/
def plansD1 : List PubSeg := plans ++ [bodyPrefixPlan, txpPlan, sigPlan, keyPlan, leafPlan, ridPlan]

def preparedSegmentsD1 : List PubSeg :=
  (List.range plansD1.length).map (fun i => descriptor (plansD1.getD i sourcePlan) 202 i)

/-! ## Bytes -/

/-- `"near-arena-prep-d1a-v0"` (22 bytes, as D0a's tag: the header offsets are unchanged). -/
def prepTagD1 : Bytes := "near-arena-prep-d1a-v0".toUTF8.toList

def headerBytesD1 (p : PrepD1) (witnessOverhead : Nat) : ByteString :=
  borshBytes prepTagD1 ++ p.base.hdr.encode ++ u32 p.base.body.length ++ u32 witnessOverhead

def extBytes (p : PrepD1) : ByteString := u32 p.m0 ++ u32 p.t0 ++ u32 p.o0 ++ u128 p.tok0

def preparedBlocksD1 (p : PrepD1) : List Payload :=
  preparedBlocks p.base ++
  [prefixPayload p.base.body p.o0, txpPayload p.ops, sigPayload p.ops,
   keyPayload (p.walks ++ p.uwalks), leafPayload p.leaves, ridPayload p.rids]

/-- `header ‖ metadata ‖ extension ‖ payloads` (`Packing.encode` with the extension between
the metadata and the payloads; the payload offsets in the metadata account for it). -/
def encodeD1 (header ext : ByteString) (blocks : List Payload) : ByteString :=
  header ++ metadata (header.length + 8 * blocks.length + ext.length) blocks ++ ext ++ dataBytes blocks

def preparedBytesD1 (p : PrepD1) (witnessOverhead : Nat) : ByteString :=
  encodeD1 (headerBytesD1 p witnessOverhead) (extBytes p) (preparedBlocksD1 p)

end ZkFormal.NearV3.D1.Public
