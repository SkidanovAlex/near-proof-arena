import NearSpecV3.Ed25519
import FpChip

/-!
`fpchip-difftest` — differential test for the `p = 2^255 − 19` multiplication chip.

Modes (each prints one JSON object per line):

* `fpchip-difftest vectors <seed> <count>`: generate `a, b, r = a*b % p` using
  Lean's own `Nat` arithmetic (i.e. `NearSpecV3.Ed25519.F.mul`), including the
  edge vectors `0, 1, p−1, p−2, p/2, 2^254, 2^255−20, 2^255−1`, then run
  `FpChip.Row.gen` / `FpChip.Row.check` on each pair.  Emits
  `{"a":..,"b":..,"want":..,"got":..,"ok":..}`.
* `fpchip-difftest air <a> <b>`: emit the AIR (columns, constraints as
  `wasm-base-lean`'s JSON dialect, degree) and the witness cells for `a·b`.
  A separate Rust interpreter (or `difftest.py`) can re-evaluate the AIR and
  compare against the Lean-side `Row.check`.
-/
open NearCompression.PqEd25519

def jNat (n : Nat) : String := toString n

def vec (f : Nat → Nat) (n : Nat) : String :=
  "[" ++ ",".intercalate ((List.range n).map (fun i => jNat (f i))) ++ "]"

def cellVec (w : FpChip.Row) : String :=
  "[" ++ ",".intercalate ((List.range FpChip.Col.total).map (fun i => jNat (FpChip.Row.env w i))) ++ "]"

/-- `a ^ b mod m` by square and multiply (for a reproducible xorshift-like generator). -/
def splitmix64 (x : Nat) : Nat :=
  let x := (x + 0x9E3779B97F4A7C15) % 2 ^ 64
  let z := (x * ((x * 0xBF58476D1CE4E5B9) % 2 ^ 64)) % 2 ^ 64
  let z := (z ^^^ (z >>> 30)) % 2 ^ 64
  let z := (z * 0x94D049BB133111EB) % 2 ^ 64
  (z ^^^ (z >>> 27)) % 2 ^ 64

structure Rng where
  s : Nat

def Rng.next (g : Rng) : Nat × Rng :=
  let s := (g.s + 0x9E3779B97F4A7C15) % 2 ^ 64
  let z := s
  let z := ((z ^^^ (z >>> 30)) * 0xBF58476D1CE4E5B9) % 2 ^ 64
  let z := ((z ^^^ (z >>> 27)) * 0x94D049BB133111EB) % 2 ^ 64
  (z ^^^ (z >>> 31), { s := s })

def Rng.below (g : Rng) (m : Nat) : Nat × Rng :=
  let (x, g) := g.next
  (x % m, g)

/-- Canonical edge vectors: every entry is `< p`, so the chip's domain hypothesis
holds.  (`2^255 − 1` is deliberately absent: it is `≥ p` and must be rejected,
tested separately by `emitNonCanonical`.) -/
def edgeVectors : List Nat :=
  [0, 1, 2, FpChip.p - 1, FpChip.p - 2, FpChip.p / 2, 2 ^ 254, 2 ^ 255 - 20,
   FpChip.B - 1, FpChip.B, FpChip.B ^ 14, FpChip.p - FpChip.B - 1]

def emitPair (a b : Nat) : IO Unit := do
  let want := a * b % FpChip.p
  let w := FpChip.Row.gen a b
  let got := w.r
  let ok := FpChip.FpMul.check a b && w.r == want
  IO.println s!"\{\"a\":{a},\"b\":{b},\"want\":{want},\"got\":{got},\"ok\":{ok},\"cells\":{FpChip.Col.total}}"

/-- Non-canonical inputs (`≥ p`) must make the range check fail even though the
generator still produces a row; `rejected = true` is the expected outcome. -/
def emitNonCanonical (a b : Nat) : IO Unit := do
  IO.println s!"\{\"a\":{a},\"b\":{b},\"rejected\":{!FpChip.FpMul.check a b},\"kind\":\"noncanonical\"}"

def emitAir (a b : Nat) : IO Unit := do
  let w := FpChip.Row.gen a b
  let cs := "[" ++ ",".intercalate (FpChip.constraints.map FpChip.Expr.toJson) ++ "]"
  IO.println s!"\{\"cells\":{FpChip.Col.total},\"degree\":{FpChip.constraints.foldl (fun m e => max m e.degree) 0},\"nconstraints\":{FpChip.constraints.length},\"constraints\":{cs}}"
  IO.println s!"\{\"a\":{a},\"b\":{b},\"q\":{w.q},\"r\":{w.r},\"row\":{cellVec w}}"

def main (args : List String) : IO UInt32 := do
  match args with
  | ["vectors", seed, count] =>
    let seed := seed.toNat!
    let count := count.toNat!
    for a in edgeVectors do
      for b in edgeVectors do emitPair a b
    for x in [FpChip.p, FpChip.p + 1, 2 ^ 255 - 1] do
      emitNonCanonical x x
      emitNonCanonical x 1
      emitNonCanonical 1 x
    let mut g : Rng := { s := seed }
    for _ in List.range count do
      let (a, g1) := g.below FpChip.p; g := g1
      let (b, g2) := g.below FpChip.p; g := g2
      emitPair a b
    pure 0
  | ["air", a, b] =>
    emitAir a.toNat! b.toNat!
    pure 0
  | _ =>
    IO.eprintln "usage: fpchip-difftest vectors <seed> <count> | air <a> <b>"
    pure 1
