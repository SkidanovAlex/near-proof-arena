import NearSpecV3.ChallengeD0a

/-!
`nearspec-v3-check-d0a CASE_DIR...` — the compiled amended relation `NearSpecV3.checkD0a`
(`.ok ()` ⇔ `RelD0a`, `relD0a_iff`) on `claim.bin` / `witness.bin` of each case directory;
one JSON line per case: `{"case", "verdict": "accept" | "reject" | "out_of_domain", "reason"}`.
Plain spec code (no candidate fast paths), so it is the reference side of the difftest.
-/

open NearSpec NearSpecV3

/-- Legacy: `triesD0` with every post trie rebuilt from the witness store and the written blobs
along the same keys (`rebuildPost`), as A7 read it from 2026-10-11 until the user switched A7
to the native post trie (2026-10-12). Not part of `RelD0a`; reported for comparison only. -/
def triesD0Rebuilt (cb wb : List UInt8) : Except String (List (PTrie × PTrie)) := do
  let k ← walkD0 cb
  let w ← decodeW wb
  let B2 ← match k.blks[k.b2i]? with | some b => pure b | none => throw "walk"
  let prevB2 ← match k.blks[k.b2i + 1]? with | some b => pure b | none => throw "walk"
  let receipts := appliedReceipts k w
  let ctxB2 := blockCtx k.L k.H.shardId k.slotB2.gasLimit B2 prevB2.hdr.nextGasPrice
  let t0 := partialTrie w.main.values k.slotB2.prevStateRoot [keyBufferedIdx]
  let bshards ← match t0.find keyBufferedIdx with
    | some v => bufferedShards v | none => throw "missing"
  let keys := mainKeys receipts bshards
  let tMain := partialTrie w.main.values k.slotB2.prevStateRoot keys
  let out ← applyNewChunk prims ctxB2 tMain receipts
  let mut acc : List (PTrie × PTrie) := [(tMain, rebuildPost w.main.values out.trie keys)]
  let mut root := out.trie.hashOf
  for (M, T) in k.implicitBlks.zip w.implicit do
    let ctxM := blockCtx k.L k.H.shardId k.slotB2.gasLimit M M.hdr.nextGasPrice
    let ks := [keyDelayedIdx, keyBwState]
    let tM := partialTrie T.values root ks
    let tM' ← applyMissingChunk prims ctxM tM
    acc := acc ++ [(tM, rebuildPost T.values tM' ks)]
    root := tM'.hashOf
  pure acc

/-- The A7 measure of 2026-10-11 (post term = the unfolded *rebuilt* post trie), reported as
`unfold_rebuilt`. -/
def unfoldBytesRebuilt (cb w : List UInt8) : Nat :=
  match triesD0Rebuilt cb w with
  | .ok l => (l.map fun (pre, post) => unfoldedBytesT pre + unfoldedBytesT post).sum
  | .error _ => 0

/-- The A7 measure before 2026-10-11 (post term `diffT` against the rebuilt post trie), reported
as `unfold_diff` so the difftest can compare it with the oracle's stored `unfold_bytes`. -/
def unfoldBytesDiff (cb w : List UInt8) : Nat :=
  match triesD0Rebuilt cb w with
  | .ok l => (l.map fun (pre, post) => unfoldedBytesT pre + diffT pre post).sum
  | .error _ => 0

def esc (s : String) : String := s.replace "\\" "\\\\" |>.replace "\"" "\\\""

/-- Usage: `nearspec-v3-check-d0a [--bound B] [--words-bound W] [--depth-bound D] CASE_DIR...`
(defaults `B0`, `W0`, `Dp0`). Each line also reports `unfold` = `unfoldBytes` (A7: pre tries +
native post tries), `chacha_words` = `chachaWords` (A9), `max_path_depth` = `maxPathDepth`
(A10), and the legacy A7 measures `unfold_rebuilt` (2026-10-11: rebuilt post tries) and
`unfold_diff` (before 2026-10-11). -/
def parseFlags (B W D : Nat) : List String → Nat × Nat × Nat × List String
  | "--bound" :: b :: rest => parseFlags b.toNat! W D rest
  | "--words-bound" :: b :: rest => parseFlags B b.toNat! D rest
  | "--depth-bound" :: b :: rest => parseFlags B W b.toNat! rest
  | rest => (B, W, D, rest)

def main (args : List String) : IO UInt32 := do
  let (B, W, D, args) := parseFlags B0 W0 Dp0 args
  for dir in args do
    let cb ← IO.FS.readBinFile (dir ++ "/claim.bin")
    let wb ← IO.FS.readBinFile (dir ++ "/witness.bin")
    let u := unfoldBytes cb.toList wb.toList
    let k := chachaWords cb.toList wb.toList
    let p := maxPathDepth cb.toList wb.toList
    let ur := unfoldBytesRebuilt cb.toList wb.toList
    let ud := unfoldBytesDiff cb.toList wb.toList
    let (v, reason) := match checkD0a B cb.toList wb.toList W D with
      | .ok () => ("accept", "")
      | .error e => (if e.startsWith "out of domain" then "out_of_domain" else "reject", e)
    IO.println s!"\{\"case\": \"{esc dir}\", \"verdict\": \"{v}\", \"reason\": \"{esc reason}\", \"unfold\": {u}, \"unfold_rebuilt\": {ur}, \"unfold_diff\": {ud}, \"chacha_words\": {k}, \"max_path_depth\": {p}}"
  return 0
