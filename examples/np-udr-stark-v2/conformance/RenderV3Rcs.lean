import ZkFormal.NearV3.Render.PaddedSrcpDD
import ZkFormal.NearV3.Render.PaddedAcctE
import ZkFormal.NearV3.Render.PaddedMrk
import ZkFormal.NearV3.Render.PaddedSort
import Lean.Data.Json

/-!
`np-lean-render-v3-rcs <table> <entries.json> <out.bin>` — the Lean honest renders of the
`nearAirV3` receipt-side tables 20 (`srcp`), 17 (`acct`), 23 (`mrk`) and 24 (`sort`), dumped
in the `np-render-v3-table` format (u32 LE `log, width`, then `2^log · width` cells row-major,
`(tr.cell t r c).toNat`).  Compared byte for byte with `npudr v3render` (../source) by
`run-v2.d/rcs.sh`.

* `srcp`: `srcpDDTrace bs rep` (`Render/PaddedSrcpDD.lean`).  Input: a JSON list of `SrcpB`
  (Lean field names, `SrcpItem` path items) whose objects also carry the per-block repetition
  bit `rep` (absent = `false`); `rep i` is the bit of block `i` (`AcceptedV3.ddRep =
  sourceRepeated p.lists`, indexed by block position).
* `acct`: `acctTraceAlignedE as` (`Render/PaddedAcctE.lean`), through its executable twin
  `acctE` (`acctE_eq`: the classical `if as = []` replaced by `as.isEmpty`).
* `mrk`: `mrkTraceV3` (`Render/PaddedMrk.lean`) = `arrTrace (outcomeTrace os pub) T_MRK 60`,
  `outcomeTrace os pub = MerkleRender.honestTrace os.length (levelTable …) pub`.  The
  differential feeds the level table directly: input `{ n, levels }` (`levels : List (List
  MNode)`, absent for `n = 0`), public vector = the `PH_N` bytes of `n`.  The dump reads the
  cells through `mrkCell` (`mrkCell_eq`: equal to `(honestTrace n lv pub).cell`), which hoists
  the row records and the count inverse out of the `2^19 · 60` cell loop; on its `60` columns
  `arrTrace` has the same cells (`arrTrace_cells`).
* `sort`: `SortV3.sortTraceV3 rs` (`Render/PaddedSort.lean`) on the sorted ids `S =
  NativeSortIds.sorted rs`: `sortV3S S` (`[]` ↦ the all-zero log-1 trace, else
  `sortTraceAligned S`).  Input: the JSON list of `[index, [32 id bytes]]` pairs.
-/

open Lean ZkFormal.Air ZkFormal.Algebra

deriving instance FromJson for ZkFormal.NearV3.SrcpItem
deriving instance FromJson for ZkFormal.NearV3.SrcpB
deriving instance FromJson for ZkFormal.Near.AcctV
deriving instance FromJson for ZkFormal.Near.Render.MNode

namespace ZkFormal.NearV3.Render
open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Size
open ZkFormal.NearV3.Candidates ZkFormal.NearV3.Rcpt.Candidates

/-- Executable twin of the (classical) `acctTraceAlignedE`. -/
def acctE (as : List AcctV) : Trace Fp :=
  if as.isEmpty then AccountEmpty.emptyTrace else acctTraceAligned as

theorem acctE_eq (as : List AcctV) : acctE as = acctTraceAlignedE as := by
  cases as <;> simp [acctE, acctTraceAlignedE]

/-- `sortTraceV3` on the sorted ids. -/
def sortV3S (S : List (Nat × List Nat)) : Trace Fp :=
  if S.isEmpty then rowsTrace 1 (mkTab 2 Sort.width (fun _ _ => 0)) else sortTraceAligned S

theorem sortV3S_eq (rs : List NearSpec.Receipt) :
    sortV3S (NativeSortIds.sorted rs) = SortV3.sortTraceV3 rs := by
  by_cases h : rs = []
  · subst h; rfl
  · have hl : (NativeSortIds.sorted rs).isEmpty = false := by
      rw [List.isEmpty_eq_false_iff, ← List.length_pos_iff, NativeSortIds.length]
      exact List.length_pos_iff.mpr h
    simp only [sortV3S, SortV3.sortTraceV3, hl, if_neg h, Bool.false_eq_true, if_false]

/-- The honest public vector of the `mrk` differential: `PH_N` the bytes of `n`. -/
def mrkPub (n : Nat) : List Fp :=
  (List.range (PH_N + 4)).map fun k => if PH_N ≤ k then Fp.ofNat (n / 256 ^ (k - PH_N) % 256) else 0

/-- The table-23 cells with the record list, its length and the count inverse hoisted. -/
def mrkCell (n : Nat) (lv : List (List MNode)) (rs : List (Nat × Nat × Bool × Nat)) (rsLen : Nat)
    (inv : Fp) (q col : Nat) : Fp :=
  if col = MerkleEmpty.emptyCol then 0
  else if col = MerkleEmpty.inverseCol then inv
  else if q = 0 ∨ q - 1 < rsLen then Fp.ofNat (MrkGen.cell n lv rs q col) else 0

theorem mrkCell_eq (n : Nat) (lv : List (List MNode)) (pub : List Fp) (hn : n ≠ 0) (q col : Nat) :
    mrkCell n lv (MrkGen.recs n) (MrkGen.recs n).length
      (MerkleEmpty.countE.eval (MerkleRender.trace n lv) ZkFormal.Near.T_MRK 0 pub)⁻¹ q col =
    (MerkleRender.honestTrace n lv pub).cell ZkFormal.Near.T_MRK q col := by
  simp only [mrkCell, MerkleRender.honestTrace, if_neg hn, MerkleEmpty.liftTrace, if_true]
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · rename_i h
        have hc : MrkGen.cell n lv (MrkGen.recs n) q col = 0 := by
          unfold MrkGen.cell
          rw [if_neg (by omega), if_neg (by omega)]
        show 0 = Fp.ofNat (MrkGen.cell n lv (MrkGen.recs n) q col)
        rw [hc]; rfl

end ZkFormal.NearV3.Render

open ZkFormal.NearV3.Render

/-- `srcp` input: the per-block repetition bit (the `SrcpB` fields are parsed separately). -/
structure RepIn where
  rep : Option Bool
  deriving FromJson

structure MrkIn where
  n : Nat
  levels : Option (List (List ZkFormal.Near.Render.MNode))
  deriving FromJson

def u32 (b : ByteArray) (x : Nat) : ByteArray :=
  b.push (x % 256).toUInt8 |>.push (x / 256 % 256).toUInt8
    |>.push (x / 65536 % 256).toUInt8 |>.push (x / 16777216 % 256).toUInt8

/-- Dump `2^log` rows of `width` cells `f r c`. -/
def dumpF (log width : Nat) (f : Nat → Nat → Fp) : ByteArray := Id.run do
  let mut b := ByteArray.emptyWithCapacity (8 + 4 * width * 2 ^ log)
  b := u32 (u32 b log) width
  for r in [0:2 ^ log] do
    for c in [0:width] do
      b := u32 b (f r c).toNat
  return b

def dump (tr : Trace Fp) (t width : Nat) : ByteArray := dumpF (tr.log t) width (tr.cell t)

def parse (α : Type) [FromJson α] (s : String) : Except String α := do
  fromJson? (← Json.parse s)

def render (table s : String) : Except String ByteArray :=
  match table with
  | "srcp" => do
    let bs ← parse (List ZkFormal.NearV3.SrcpB) s
    let reps ← parse (List RepIn) s
    let rep : Nat → Bool := fun i => ((reps.getD i ⟨none⟩).rep).getD false
    return dump (srcpDDTrace bs rep) 20 ZkFormal.NearV3.SrcpDD.width
  | "acct" => do
    let as ← parse (List ZkFormal.Near.AcctV) s
    return dump (acctE as) 17 ZkFormal.NearV3.AcctV3.width
  | "mrk" => do
    let m ← parse MrkIn s
    let lv := m.levels.getD []
    let pub := mrkPub m.n
    if m.n = 0 then
      return dump (ZkFormal.NearV3.Candidates.MerkleRender.honestTrace 0 lv pub)
        ZkFormal.Near.T_MRK ZkFormal.NearV3.Candidates.MerkleEmpty.table.width
    let rs := ZkFormal.Near.Render.MrkGen.recs m.n
    let inv := (ZkFormal.NearV3.Candidates.MerkleEmpty.countE.eval
      (ZkFormal.NearV3.Candidates.MerkleRender.trace m.n lv) ZkFormal.Near.T_MRK 0 pub)⁻¹
    let log := (ZkFormal.NearV3.Candidates.MerkleRender.honestTrace m.n lv pub).log
      ZkFormal.Near.T_MRK
    return dumpF log ZkFormal.NearV3.Candidates.MerkleEmpty.table.width
      (mrkCell m.n lv rs rs.length inv)
  | "sort" => do
    let S ← parse (List (Nat × List Nat)) s
    return dump (sortV3S S) 24 ZkFormal.Near.Sort.width
  | t => throw s!"unknown table {t}"

def main (args : List String) : IO UInt32 := do
  match args with
  | [table, inp, out] =>
    match render table (← IO.FS.readFile inp) with
    | .ok b => IO.FS.writeBinFile out b; return 0
    | .error e => IO.eprintln s!"np-lean-render-v3-rcs: {e}"; return 2
  | _ => IO.eprintln "usage: np-lean-render-v3-rcs <srcp|acct|mrk|sort> <entries.json> <out.bin>"; return 2
