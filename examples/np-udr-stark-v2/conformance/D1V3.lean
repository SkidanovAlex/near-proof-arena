import ZkFormal.V3.Fast.Prep
import ZkFormal.NearV3.D1.PrepD1

/-!
`np-lean-d1-v3` — the Lean side of the D1 differentials (lane v3-d1-tables).

* `np-lean-d1-v3 prep <case_dir> <hint.bin> <out.bin>`: the verifier's native preparation
  `ZkFormal.NearV3.D1.preparedTapeD1 claim hint` (`prepD1` then `preparedBytesD1 · 0`) on the
  Rust prover's hint; writes the public tape (compare with `npudr v3d1prove`'s
  `prepared.bin`).  Exit 1 if `prepD1` rejects.
* `np-lean-d1-v3 entries <case_dir>`: the `txV3` ops and `akmV3` segments read off an
  instrumented replay of `processTxs` (RuntimeD1.lean: the spec's own `readKey`,
  `decodeSigner`, `decodeAccessKey`, `txCost`, `verifyAndCharge`, `PTrie.set`) and of the
  local receipts (`TransferV1.applyReceipt`), as JSON `{tx, akm}` with the Rust entry field
  names (compare with `npudr v3d1prove --dump`'s `tx.json` / `akm.json`).  Value ids are
  ordinals in `checkD1`'s main pre trie `tMain` (over `mainKeys ++ txKeys`: lane v3-d1-a7b, the
  AIR's pre trie).  Also `unread` (plan §5 R-5 → (B)): for every `txKeys` entry the terminal
  of its `walkU` walk on `tMain` (`val vid`, `absent`, or `stub n I z` where a child or value
  is not revealed), the stub windows with their use counts and hashes, the `nmemV3` mode of
  each stub hash among the store digests of `tMain` (`0` between, `1` below all, `2` above
  all), and the `uvalV3` values (`txKeys` entries no reader reads whose value `tMain`
  reveals) — compare with `unread.json`.
-/

open NearSpec NearSpec.TransferV1 NearSpecV3 ZkFormal.NearV3.D1

/-! ## Value ordinals (`Assembly.ValueIndex.valueIndex`, copied: that module imports proofs) -/

mutual
def vIdx : PTrie → List Nat → Option Nat
  | .hash _, _ => none
  | .leaf k s _, key => if k == key then (match s with | .val _ => some 0 | .ref _ _ => none) else none
  | .ext k c _, key => if isPrefix k key then vIdx c (key.drop k.length) else none
  | .branch v _ _, [] => match v with | some (.val _) => some 0 | _ => none
  | .branch v cs _, n::key => (kIdx cs n key).map ((NearSpecV3.optSlotVal v).length + ·)
def kIdx : Kids → Nat → List Nat → Option Nat
  | .nil, _, _ => none
  | .none _, 0, _ => none
  | .some c _, 0, key => vIdx c key
  | .none cs, n+1, key => kIdx cs n key
  | .some c cs, n+1, key => (kIdx cs n key).map ((NearSpecV3.valsOf c).length + ·)
end

/-! ## Instrumented `processTxs` -/

structure OpRec where
  kind : Nat := 0
  strict : Nat := 0
  ok : Nat := 0
  tov : Nat := 0
  stage : Nat := 0
  cok : Nat := 0
  valid : Nat := 0
  nonce : Nat := 0
  bound : Nat := 0
  amount : Nat := 0
  akey : List Nat := []
  kkey : List Nat := []
  tpA : Nat := 0
  amt : Nat := 0
  lk : Nat := 0
  st : Nat := 0
  tpK : Nat := 0
  kn : Nat := 0
  fa : Nat := 0

structure RS where
  trie : PTrie
  seen : List Bytes := []
  ops : List OpRec := []
  acctT : List (List Nat × Nat) := []
  akT : List (List Nat × Nat) := []
  reads : List (List Nat) := []
  akKeys : List (List Nat) := []
  locals : List Receipt := []
  tokens : Nat := 0

def lk? (l : List (List Nat × Nat)) (k : List Nat) : Nat := ((l.find? (·.1 == k)).map (·.2)).getD 0
def put (l : List (List Nat × Nat)) (k : List Nat) (v : Nat) : List (List Nat × Nat) :=
  (k, v) :: l.filter (·.1 != k)

def stepTx (ctx : ApplyCtx) (s : RS) (t : Tx) (flag : Bool) : Except String RS := do
  let h := t.hash
  if s.seen.contains h then return s
  let s := { s with seen := h :: s.seen }
  if !flag then return s
  let time := s.ops.length + 1
  let cost := txCost t ctx.gasPrice
  let op0 : OpRec := {}
  let mut op : OpRec := { op0 with
    strict := (if t.strict then 1 else 0)
    valid := (if t.valid then 1 else 0)
    cok := (if cost.isSome then 1 else 0)
    nonce := t.nonce
    bound := min (ctx.height * TxParams.nonceRangeMultiplier) (Params.two64 - 1)
    amount := (cost.map (·.totalCost)).getD 0 }
  let mut s := s
  match t.valid, cost with
  | true, some c =>
    let akey := accountKeyPath t.signerId
    match ← readKey s.trie akey "signer account" with
    | none => pure ()
    | some araw =>
      let a ← decodeSigner araw
      op := { op with stage := 1, akey, tpA := lk? s.acctT akey, amt := a.amount, lk := a.locked,
                      st := a.storageUsage }
      s := { s with acctT := put s.acctT akey time, reads := s.reads ++ [akey] }
      let kkey := keyAccessKey t.signerId t.pkKey
      match ← readKey s.trie kkey "access key" with
      | none => pure ()
      | some kraw =>
        let some k := decodeAccessKey kraw | throw "invalid: StorageInconsistentState (access key)"
        op := { op with stage := 2, kkey, tpK := lk? s.akT kkey, kn := k.nonce,
                        fa := (if k.perm == .fullAccess then 1 else 0) }
        s := { s with akT := put s.akT kkey time, reads := s.reads ++ [kkey],
                      akKeys := (if s.akKeys.contains kkey then s.akKeys else s.akKeys ++ [kkey]) }
        match verifyAndCharge a k t c ctx.height with
        | none => pure ()
        | some newAmount =>
          op := { op with ok := 1 }
          let rid := receiptIdFrom h ctx.height 0
          let r : Receipt := { predecessorId := t.signerId, receiverId := t.receiverId, receiptId := rid,
                               signerId := t.signerId, signerPk := t.pkKey, gasPrice := c.receiptGasPrice,
                               deposit := t.deposit }
          if t.receiverId == t.signerId then s := { s with locals := s.locals ++ [r] }
          if s.tokens + c.burntAmount ≥ Params.two128 then
            op := { op with tov := 1 }
          else
            let t1 ← match s.trie.set akey (Account.encode { a with amount := newAmount }) with
              | some x => pure x | none => throw "signer account path"
            let t2 ← match t1.set kkey (encodeFullAccessKey t.nonce) with
              | some x => pure x | none => throw "access key path"
            s := { s with trie := t2, tokens := s.tokens + c.burntAmount }
  | _, _ => pure ()
  pure { s with ops := s.ops ++ [op] }

def stepTxs (ctx : ApplyCtx) : RS → List (Tx × Bool) → Except String RS
  | s, [] => .ok s
  | s, (t, f) :: rest => do stepTxs ctx (← stepTx ctx s t f) rest

def stepLocals (ctx : ApplyCtx) : RS × Acc → List Receipt → Except String (RS × Acc)
  | p, [] => .ok p
  | (s, acc), r :: rs => do
    let akey := accountKeyPath r.receiverId
    let some raw := acc.trie.get akey | throw "local account"
    let some a := Account.decode raw | throw "local account decode"
    let time := s.ops.length + 1
    let op : OpRec := { kind := 1, stage := 1, cok := 1, valid := 1, amount := r.deposit, akey,
                        tpA := lk? s.acctT akey, amt := a.amount, lk := a.locked, st := a.storageUsage }
    let some acc' := applyReceipt ⟨ctx.height, ctx.gasPrice⟩ acc r | throw "local receipt fails"
    stepLocals ctx ({ s with ops := s.ops ++ [op], acctT := put s.acctT akey time }, acc') rs

/-! ## Unread-key walks (`walkU`, lane v3-d1-a7b) -/

/-- The terminal of an unread walk on the AIR's pre trie (`n`: occurrence index in pre-order,
`vid`: value ordinal, as the node / value records). -/
inductive UTerm where
  | val (vid : Nat)
  | absent
  | stub (n i z : Nat) (h : Bytes)

def tsizeT (t : PTrie) : Nat := (NearSpecV3.occs t).length
def valsLenT (t : PTrie) : Nat := (NearSpecV3.valsOf t).length

mutual
def uterm : Nat → Nat → PTrie → List Nat → UTerm
  | _, _, .hash _, _ => .absent
  | n, v, .leaf k s _, key =>
    if k == key then
      match s with
      | .val _ => .val v
      | .ref _ h => .stub n k.length 16 h
    else .absent
  | n, v, .ext k c _, key =>
    if isPrefix k key then
      match c with
      | .hash h => .stub n k.length 19 h
      | .leaf a b m => uterm (n + 1) v (.leaf a b m) (key.drop k.length)
      | .ext a b m => uterm (n + 1) v (.ext a b m) (key.drop k.length)
      | .branch a b m => uterm (n + 1) v (.branch a b m) (key.drop k.length)
    else .absent
  | n, v, .branch val _ _, [] =>
    match val with
    | none => .absent
    | some (.val _) => .val v
    | some (.ref _ h) => .stub n 0 16 h
  | n, v, .branch val cs _, x :: xs =>
    ukids n x (n + 1) (v + (NearSpecV3.optSlotVal val).length) cs x xs
def ukids (parent sym : Nat) : Nat → Nat → Kids → Nat → List Nat → UTerm
  | _, _, .nil, _, _ => .absent
  | _, _, .none _, 0, _ => .absent
  | _, _, .some (.hash h) _, 0, _ => .stub parent 0 sym h
  | n, v, .some (.leaf a b m) _, 0, key => uterm n v (.leaf a b m) key
  | n, v, .some (.ext a b m) _, 0, key => uterm n v (.ext a b m) key
  | n, v, .some (.branch a b m) _, 0, key => uterm n v (.branch a b m) key
  | n, v, .none r, j + 1, key => ukids parent sym n v r j key
  | n, v, .some c r, j + 1, key => ukids parent sym (n + tsizeT c) (v + valsLenT c) r j key
end

def ltLE (a b : Bytes) : Bool := decide (a.reverse.map (·.toNat) < b.reverse.map (·.toNat))

def jsonNat (n : Nat) : String := toString n
def jsonArr (l : List String) : String := "[" ++ ", ".intercalate l ++ "]"
def jsonBytes (b : Bytes) : String := jsonArr (b.map fun x => toString x.toNat)

def entries (cb wb : Bytes) : Except String String := do
  let k ← walkD0 cb
  let w ← decodeWD1 wb
  let B2 ← match k.blks[k.b2i]? with | some b => pure b | none => throw "walk"
  let prevB2 ← match k.blks[k.b2i + 1]? with | some b => pure b | none => throw "walk"
  let receipts := appliedReceiptsD1 k w
  let ctx := blockCtx k.L k.H.shardId k.slotB2.gasLimit B2 prevB2.hdr.nextGasPrice
  let root := k.slotB2.prevStateRoot
  let t0 := partialTrie w.main.values root [keyBufferedIdx]
  let bshards ← match t0.find keyBufferedIdx with
    | some v => bufferedShards v | none => throw "missing"
  let tMain := partialTrie w.main.values root (mainKeys receipts bshards ++ txKeys w.txs)
  let s ← stepTxs ctx { trie := tMain } (w.txs.zip (k.c.txValid.map (· != 0)))
  let (s, acc) ← stepLocals ctx (s, ⟨s.trie, [], [], 0, s.tokens⟩) s.locals
  -- the AIR's pre trie is `checkD1`'s `tMain` (every `txKeys` entry walked, lane v3-d1-a7b)
  let tAir := tMain
  let vid (key : List Nat) : Nat := (vIdx tAir key).getD 0
  let txj := s.ops.map fun o =>
    "{" ++ ", ".intercalate
      [s!"\"kind\": {o.kind}", s!"\"strict\": {o.strict}", s!"\"ok\": {o.ok}", s!"\"tov\": {o.tov}",
       s!"\"stage\": {o.stage}", s!"\"cok\": {o.cok}", s!"\"valid\": {o.valid}",
       s!"\"nonce\": {o.nonce}", s!"\"bound\": {o.bound}", s!"\"amount\": {o.amount}",
       s!"\"vid_a\": {if o.stage ≥ 1 then vid o.akey else 0}", s!"\"tp_a\": {o.tpA}",
       s!"\"amt\": {o.amt}", s!"\"lk\": {o.lk}", s!"\"st\": {o.st}",
       s!"\"vid_k\": {if o.stage == 2 then vid o.kkey else 0}", s!"\"tp_k\": {o.tpK}",
       s!"\"kn\": {o.kn}", s!"\"fa\": {o.fa}"] ++ "}"
  let akmj := s.akKeys.map fun key =>
    let bytes := (tAir.get key).getD []
    let post := (acc.trie.get key).getD []
    let u := (receipts.filter fun r => r.predecessorId == AccountId.system && r.signerId == r.receiverId &&
      keyAccessKey r.receiverId r.signerPk == key).length
    "{" ++ ", ".intercalate
      [s!"\"vid\": {vid key}", s!"\"bytes\": {jsonBytes bytes}", s!"\"tlast\": {lk? s.akT key}",
       s!"\"post\": {jsonBytes (post.take 8)}", s!"\"U\": {u}"] ++ "}"
  -- unread-key walks: every `txKeys` entry
  let ukeys := txKeys w.txs
  let terms := ukeys.map (uterm 0 0 tMain)
  let termj := terms.map fun
    | .val v => s!"[\"val\", {v}]"
    | .absent => "[\"absent\"]"
    | .stub n i z _ => s!"[\"stub\", {n}, {i}, {z}]"
  let stubs : List (Nat × Nat × Nat × Bytes) := terms.filterMap fun
    | .stub n i z h => some (n, i, z, h) | _ => none
  let distinct := stubs.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []
  let stubj := distinct.map fun (n, i, z, h) =>
    jsonArr [toString n, toString i, toString z, toString (stubs.count (n, i, z, h)), jsonBytes h]
  let digs := ((NearSpecV3.occs tMain).map fun o => sha256 (NearSpecV3.nodeEnc o)) ++
    (NearSpecV3.valsOf tMain).map sha256
  let nmemj := distinct.map fun (_, _, _, h) =>
    let below := digs.any fun d => ltLE d h
    let above := digs.any fun d => ltLE h d
    jsonArr [jsonBytes h, toString (if below && above then 0 else if above then 1 else 2)]
  let airKeys := mainKeys receipts bshards ++ s.reads
  let uvk := (ukeys.filter fun key => !airKeys.contains key &&
    (match tMain.find key with | some (some _) => true | _ => false)).foldl
    (fun acc x => if acc.contains x then acc else acc ++ [x]) []
  let uvalj := uvk.map fun key => jsonArr [toString (vid key), jsonBytes ((tMain.get key).getD [])]
  let unreadj := "{\"terms\": " ++ jsonArr termj ++ ", \"stubs\": " ++ jsonArr stubj ++
    ", \"nmem\": " ++ jsonArr nmemj ++ ", \"uval\": " ++ jsonArr uvalj ++ "}"
  pure ("{\"tx\": " ++ jsonArr txj ++ ", \"akm\": " ++ jsonArr akmj ++ ", \"unread\": " ++
    unreadj ++ "}")

def readB (p : String) : IO Bytes := do return (← IO.FS.readBinFile p).toList

def main (args : List String) : IO UInt32 := do
  match args with
  | ["prep", dir, hint, out] =>
    let cb ← readB s!"{dir}/claim.bin"
    let hb ← readB hint
    match preparedTapeD1 cb hb with
    | .ok b => IO.FS.writeBinFile out (ByteArray.mk b.toArray); return 0
    | .error e => IO.eprintln s!"prepD1: {e}"; return 1
  | ["entries", dir] =>
    let cb ← readB s!"{dir}/claim.bin"
    let wb ← readB s!"{dir}/witness.bin"
    match entries cb wb with
    | .ok s => IO.println s; return 0
    | .error e => IO.eprintln s!"entries: {e}"; return 1
  | _ => IO.eprintln "usage: np-lean-d1-v3 prep <case_dir> <hint.bin> <out.bin> | entries <case_dir>"; return 2
