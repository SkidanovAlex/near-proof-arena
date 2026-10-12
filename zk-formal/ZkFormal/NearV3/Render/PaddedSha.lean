import ZkFormal.NearV3.Render.Padded
import ZkFormal.NearV3.Candidates.ShaHeight.Traffic
import ZkFormal.NearV3.Assembly.ShaBinRender
import ZkFormal.NearV3.Assembly.NearAir

/-!
# Aligned SHA-256 generator (`nearAirV3` tables 0 and 1)

`shaTraceAligned msgs` is the array-backed honest SHA table of L5 (`Sha.Gen`) at
the rounded height `padLog22 (logOf rows)`.  It equals the function-backed
`ShaHeight.fixedTrace msgs log`, whose local legality at any explicit clock and
traffic invariance under padding are proved in `Candidates/ShaHeight`.  The
traffic is `shaBinTraffic msgs` — the traffic the two SHA instances of
`nearAirV3` carry on `B_BYTES`/`B_DIGEST` (`Assembly/ShaBinRender.lean`).

`Sha.MsgsOk` is the honest-input condition of L5 (bytes `< 256`, lengths
`< 2^25`, at most `2^22` rows); the SHA cap of `nearAirV3` is `22 ≡ 1 (mod 3)`.
-/
namespace ZkFormal.NearV3.Render
open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Air ZkFormal.Algebra ZkFormal.Size

/-- An `mkTab` row array reads `0` outside its rows. -/
theorem mkTab_get_row_ge {H W : Nat} {f : Nat → Nat → Nat} {q col : Nat} (hq : H ≤ q) :
    ((mkTab H W f).getD q #[]).getD col 0 = 0 := by
  simp [mkTab, Array.getD_eq_getD_getElem?, Nat.not_lt.mpr hq]

/-- An `mkTab` row array reads `0` outside its columns. -/
theorem mkTab_get_col_ge {H W : Nat} {f : Nat → Nat → Nat} {q col : Nat} (hc : W ≤ col) :
    ((mkTab H W f).getD q #[]).getD col 0 = 0 := by
  by_cases hq : q < H
  · simp [mkTab, Array.getD_eq_getD_getElem?, hq, Nat.not_lt.mpr hc]
  · exact mkTab_get_row_ge (Nat.le_of_not_lt hq)

/-- The array-backed trace of `mkTab (2^log) W f` equals the function-backed trace of
`f`, provided `f` vanishes outside the table. -/
theorem rowsTrace_mkTab_eq (log W : Nat) (f : Nat → Nat → Nat)
    (hr : ∀ r c, 2 ^ log ≤ r → f r c = 0) (hc : ∀ r c, W ≤ c → f r c = 0) :
    rowsTrace log (mkTab (2 ^ log) W f) = ⟨fun _ => log, fun _ r c => Fp.ofNat (f r c)⟩ := by
  unfold rowsTrace
  congr
  funext t r c
  by_cases h1 : r < 2 ^ log
  · by_cases h2 : c < W
    · rw [mkTab_get h1 h2]
    · rw [mkTab_get_col_ge (Nat.le_of_not_lt h2), hc r c (Nat.le_of_not_lt h2)]
  · rw [mkTab_get_row_ge (Nat.le_of_not_lt h1), hr r c (Nat.le_of_not_lt h1)]

namespace PaddedSha
open ZkFormal.Sha ZkFormal.Sha.Gen ZkFormal.Sha.Layout

theorem rowCell_col_ge (row : Gen.Row) (c : Nat) (hc : Layout.width ≤ c) : rowCell row c = 0 := by
  simp only [Layout.width] at hc
  cases row <;> simp only [rowCell, startCell, roundCell, digestCell] <;>
    repeat (rw [if_neg (by (try simp only [colS, colId, colD, colNd, colFprev, colLast, colP80,
      colSeen, colPn, colDmult]); omega)])

theorem honestCell_col_ge (msgs : List Sha.Gen.Msg) (r c : Nat) (hc : Layout.width ≤ c) :
    honestCell msgs r c = 0 := rowCell_col_ge _ c hc

theorem honestCell_row_ge (msgs : List Sha.Gen.Msg) (r c : Nat) (hr : (honestRows msgs).length ≤ r) :
    honestCell msgs r c = 0 := by
  unfold honestCell
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hr]
  rfl

end PaddedSha

/-- Rows of the honest SHA table. -/
abbrev shaRows (msgs : List Sha.Gen.Msg) : Nat := (Sha.Gen.honestRows msgs).length

/-- The aligned, array-backed honest SHA table. -/
def shaTraceAligned (msgs : List Sha.Gen.Msg) : Trace Fp :=
  let log := padLog22 (logOf (shaRows msgs))
  rowsTrace log (mkTab (2 ^ log) Sha.Layout.width (Sha.Gen.honestCell msgs))

theorem shaTraceAligned_eq (msgs : List Sha.Gen.Msg) (hok : Sha.MsgsOk msgs) :
    shaTraceAligned msgs =
      ZkFormal.NearV3.Candidates.ShaHeight.fixedTrace msgs (padLog22 (logOf (shaRows msgs))) := by
  have hh := padded_log_fits (shaRows msgs) hok.rows
  unfold shaTraceAligned
  rw [rowsTrace_mkTab_eq]
  · rfl
  · intro r c hr
    exact PaddedSha.honestCell_row_ge msgs r c (Nat.le_trans hh.1 hr)
  · intro r c hc
    exact PaddedSha.honestCell_col_ge msgs r c hc

open ZkFormal.NearV3.Assembly in
/-- **SHA aligned completeness** (tables 0 and 1 of `nearAirV3`, `shaTable`).  The
same `shaBinTraffic msgs` as the unpadded L5 trace is emitted. -/
theorem sha_aligned_complete (msgs : List Sha.Gen.Msg) (hok : Sha.MsgsOk msgs) (t : Nat)
    (pub : List Fp) :
    TableLocal shaTable (shaTraceAligned msgs) t pub ∧
    TableTraffic shaTable.interactions (shaTraceAligned msgs) t pub (shaBinTraffic msgs) ∧
    (shaTraceAligned msgs).log t % 3 = 1 := by
  have hh := padded_log_fits (shaRows msgs) hok.rows
  rw [shaTraceAligned_eq msgs hok]
  refine ⟨ZkFormal.NearV3.Candidates.ShaHeight.fixed_local msgs hok _ t pub B_BYTES B_DIGEST
      ⟨hh.2.1, hh.2.2.1⟩ hh.1, ?_, hh.2.2.2⟩
  have hold : TableTraffic (Sha.Table.interactions B_BYTES B_DIGEST) (Sha.honestTrace msgs) t pub
      (shaBinTraffic msgs) := shaBin_traffic [msgs] 0 pub hok
  intro b m
  rw [show shaTable.interactions = Sha.Table.interactions B_BYTES B_DIGEST from rfl,
    ZkFormal.NearV3.Candidates.ShaHeight.fixed_count msgs _ t pub B_BYTES B_DIGEST b true m hh.1,
    ZkFormal.NearV3.Candidates.ShaHeight.fixed_count msgs _ t pub B_BYTES B_DIGEST b false m hh.1]
  exact hold b m

end ZkFormal.NearV3.Render
