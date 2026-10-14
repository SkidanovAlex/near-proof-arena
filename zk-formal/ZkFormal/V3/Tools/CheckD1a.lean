import NearSpecV3.ChallengeD1a

/-!
`nearspec-v3-check-d1a CASE_DIR...` — the compiled bounded D1 relation `NearSpecV3.checkD1a`
(`.ok ()` ⇔ `RelD1a`, `relD1a_iff`) on `claim.bin` / `witness.bin` of each case directory;
one JSON line per case: `{"case", "verdict": "accept" | "reject" | "out_of_domain", "reason",
"unfold", "chacha_words", "max_path_depth", "tx_count"}`. Plain spec code (no candidate fast
paths), so it is the reference side of the D1a difftest (`oracle/tools/difftest_v3_d1a.py`).

Usage: `nearspec-v3-check-d1a [--bound B] [--words-bound W] [--depth-bound D] [--tx-bound N]
CASE_DIR...` (defaults `B0`, `W0`, `Dp0`, `NT0`). `unfold` = `unfoldBytesD1` (A7ᴰ¹),
`chacha_words` = `chachaWordsD1` (A9ᴰ¹), `max_path_depth` = `maxPathDepthD1` (A10ᴰ¹),
`tx_count` = `txCountD1` (T1); the measures are reported for every case (0 where the run or the
decoding fails).
-/

open NearSpec NearSpecV3

def esc (s : String) : String := s.replace "\\" "\\\\" |>.replace "\"" "\\\""

def parseFlags (B W D N : Nat) : List String → Nat × Nat × Nat × Nat × List String
  | "--bound" :: b :: rest => parseFlags b.toNat! W D N rest
  | "--words-bound" :: b :: rest => parseFlags B b.toNat! D N rest
  | "--depth-bound" :: b :: rest => parseFlags B W b.toNat! N rest
  | "--tx-bound" :: b :: rest => parseFlags B W D b.toNat! rest
  | rest => (B, W, D, N, rest)

def main (args : List String) : IO UInt32 := do
  let (B, W, D, N, args) := parseFlags B0 W0 Dp0 NT0 args
  for dir in args do
    let cb ← IO.FS.readBinFile (dir ++ "/claim.bin")
    let wb ← IO.FS.readBinFile (dir ++ "/witness.bin")
    let (v, reason) := match checkD1a B cb.toList wb.toList W D N with
      | .ok () => ("accept", "")
      | .error e => (if e.startsWith "out of domain" then "out_of_domain" else "reject", e)
    -- the measures re-run the D1 transition; skip them where checkD1 already failed
    let measured := v == "accept" || (v == "out_of_domain" && (checkD1 cb.toList wb.toList).toBool)
    let u := if measured then unfoldBytesD1 cb.toList wb.toList else 0
    let k := if measured then chachaWordsD1 cb.toList wb.toList else 0
    let p := maxPathDepthD1 cb.toList wb.toList
    let n := txCountD1 wb.toList
    IO.println s!"\{\"case\": \"{esc dir}\", \"verdict\": \"{v}\", \"reason\": \"{esc reason}\", \"in_rel_d1\": {measured}, \"unfold\": {u}, \"chacha_words\": {k}, \"max_path_depth\": {p}, \"tx_count\": {n}}"
  return 0
