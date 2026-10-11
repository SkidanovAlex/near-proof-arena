import ZkFormal.NearV3.Render.PaddedCongr
import ZkFormal.NearV3.Candidates.MerkleRender.NativeTraffic
import ZkFormal.NearV3.Assembly.LinkV3

/-!
# Aligned outcome-Merkle generator (`nearAirV3` table 23, `MerklePublic.table`, cap 19)

`mrkTraceAligned os` is the array-backed physical Merkle renderer of
`Candidates/MerkleRender` over the native outcome digests (`levelTable (outcomePreimages os)`),
at height `2^19` (`19 ≡ 1 (mod 3)`, the table's cap; every count `≤ 4481` fits).  Its traffic is
the soundness-side `mrkTraffic` of the generated view, read through the v3 public alias
(`MerklePublic.aliasPublic`).

The honest-input condition is `1 ≤ |os| ≤ 4481` (A1/receipt bound) plus the prepared public
count bytes.  **The empty case `os = []` is not covered:** `nearAirV3` uses
`MerklePublic.table`, whose root row requires a nonempty tree (the empty-tree variant
`MerkleEmpty.table`, width 60, is not the table in `nearAirV3`).
-/
namespace ZkFormal.NearV3.Render
open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Air ZkFormal.Algebra ZkFormal.Size
open ZkFormal.NearV3.Candidates ZkFormal.NearV3.Candidates.MerkleRender
open ZkFormal.NearV3.Rcpt.Candidates

theorem mrk_cell_ge (n : Nat) (lv : List (List MNode)) (rs : List (Nat × Nat × Bool × Nat))
    (q col : Nat) (hc : Mrk.width ≤ col) : MrkGen.cell n lv rs q col = 0 := by
  simp only [Mrk.width] at hc
  unfold MrkGen.cell
  split
  · unfold MrkGen.rootCell
    repeat rw [if_neg (by (try simp only [Mrk.rt, Mrk.gM, Mrk.mj, Mrk.cId, Mrk.cLen]); omega)]
  · split
    · generalize rs.getD (q - 1) default = r
      obtain ⟨j, i, h, p⟩ := r
      unfold MrkGen.nodeCell
      dsimp only
      repeat rw [if_neg (by (try simp only [Mrk.q, Mrk.j, Mrk.i, Mrk.sp, Mrk.s, Mrk.odd, Mrk.lil,
        Mrk.top, Mrk.inv, Mrk.mj]); omega)]
      cases h <;> simp only [Bool.false_eq_true, if_true, if_false] <;>
        repeat rw [if_neg (by (try simp only [Mrk.sg, Mrk.pw, Mrk.wn, Mrk.wf, Mrk.wl, Mrk.sf, Mrk.sl,
          Mrk.cId, Mrk.cLen, Mrk.mi, Mrk.gM, Mrk.gO, Mrk.oId, Mrk.oLen, Mrk.reg, Mrk.pr]); omega)]
    · rfl

/-- The levels of the native outcome tree. -/
def mrkLevels (os : List NearSpec.Outcome) : List (List MNode) := levelTable (outcomePreimages os)

def mrkTraceAligned (os : List NearSpec.Outcome) : Trace Fp :=
  rowsTrace 19 (mkTab (2 ^ 19) Mrk.width (MrkGen.cell os.length (mrkLevels os) (MrkGen.recs os.length)))

/-- The `mrkV3` traffic (soundness-side `mrkTraffic` of the generated view, v3 public alias). -/
def mrkTrafficV3 (os : List NearSpec.Outcome) (pub : List Fp) : Traffic :=
  ZkFormal.Near.mrkTraffic (MerklePublic.aliasPublic pub) (generatedView os.length (mrkLevels os))

/-- **`mrkV3` aligned completeness** at height `2^19` for nonempty outcome lists. -/
theorem mrk_aligned_complete (os : List NearSpec.Outcome) (pub : List Fp)
    (hn1 : 1 ≤ os.length) (hn : os.length ≤ 4481)
    (hp : ∀ i < 4, pub.getD (PH_N + i) 0 = Fp.ofNat (os.length / 256 ^ i % 256)) :
    TableLocal MerklePublic.table (mrkTraceAligned os) T_MRK pub ∧
    TableTraffic MerklePublic.table.interactions (mrkTraceAligned os) T_MRK pub (mrkTrafficV3 os pub) ∧
    (mrkTraceAligned os).log T_MRK % 3 = 1 := by
  have hl : (trace os.length (mrkLevels os)).log T_MRK = (mrkTraceAligned os).log T_MRK := rfl
  have hcell : ∀ r, r < (trace os.length (mrkLevels os)).height T_MRK → ∀ c,
      (trace os.length (mrkLevels os)).cell T_MRK r c = (mrkTraceAligned os).cell T_MRK r c := by
    intro r hr c
    have hr' : r < 2 ^ 19 := hr
    unfold mrkTraceAligned
    rw [rowsTrace_cells 19 _ _ (fun r c h => mrk_cell_ge _ _ _ r c h) T_MRK r hr' c]
    rfl
  refine ⟨tableLocal_congr_rows hl hcell (remapped_local _ _ pub hn1 hn hp),
    tableTraffic_congr_rows hl hcell ?_, show 19 % 3 = 1 from rfl⟩
  have hlen : (outcomePreimages os).length = os.length := by simp [outcomePreimages]
  have hd := concrete_digests (outcomePreimages os) (by rwa [hlen])
  rw [hlen] at hd
  have ht := traffic19 os.length (mrkLevels os) (MerklePublic.aliasPublic pub) hn1 hn hd
  intro b m
  rw [MerklePublic.count_alias, MerklePublic.count_alias]
  exact ht b m


/-! ## The repaired `nearAirV3` Merkle table (`MerkleEmpty.table`, empty outcomes allowed) -/

/-- The aligned `mrkV3` trace: the array copy of the physical outcome renderer (`MerkleEmpty`
empty trace of height `2` for no outcomes, else the lifted Merkle table at `2^19`). -/
def mrkTraceV3 (os : List NearSpec.Outcome) (pub : List Fp) : Trace Fp :=
  arrTrace (outcomeTrace os pub) T_MRK 60

theorem outcomeTrace_cell_ge (os : List NearSpec.Outcome) (pub : List Fp) (r c : Nat)
    (hc : 60 ≤ c) : (outcomeTrace os pub).cell T_MRK r c = 0 := by
  unfold outcomeTrace MerkleRender.honestTrace
  split
  · show (if c = MerkleEmpty.emptyCol then 1 else 0 : Fp) = 0
    rw [if_neg (by simp only [MerkleEmpty.emptyCol]; omega)]
  · simp only [MerkleEmpty.liftTrace, if_true, MerkleEmpty.emptyCol, MerkleEmpty.inverseCol,
      show c ≠ 58 by omega, show c ≠ 59 by omega, if_false]
    show Fp.ofNat (MrkGen.cell _ _ _ r c) = 0
    rw [mrk_cell_ge _ _ _ r c (by simp only [Mrk.width]; omega)]
    rfl

/-- **`mrkV3` aligned completeness for `nearAirV3`'s repaired table**: any outcome list up to
the receipt bound (including none), with the prepared public count and root bytes. -/
theorem mrk_v3_aligned_complete (os : List NearSpec.Outcome) (pub : List Fp)
    (hn : os.length ≤ 4481)
    (hp : ∀ i < 4, pub.getD (PH_N + i) 0 = Fp.ofNat (os.length / 256 ^ i % 256))
    (ho : ∀ i < 32, pub.getD (PH_OUT + i) 0 = Fp.ofNat (((NearSpec.outcomeRoot os).getD i 0).toNat)) :
    TableLocal MerkleEmpty.table (mrkTraceV3 os pub) T_MRK pub ∧
    TableTraffic MerkleEmpty.table.interactions (mrkTraceV3 os pub) T_MRK pub
      (ZkFormal.NearV3.Assembly.mrkTrafficE pub (decide (os = [])) (generatedView os.length (mrkLevels os))) ∧
    (mrkTraceV3 os pub).log T_MRK % 3 = 1 := by
  have hT := arrTrace_transfer (tr := outcomeTrace os pub) (t := T_MRK) (W := 60) (pub := pub)
    (fun r _ c hc => outcomeTrace_cell_ge os pub r c hc)
  have hL := outcome_local os pub hn hp ho
  by_cases he : os = []
  · subst he
    have hc0 : MerkleEmpty.countE.eval (outcomeTrace [] pub) T_MRK 0 pub = 0 := by
      have := MerkleEmpty.count_zero T_MRK 0 pub (fun i hi => by rw [hp i hi, List.length_nil, Nat.zero_div, Nat.zero_mod]; rfl)
      exact this
    obtain ⟨-, hz⟩ := MerkleEmpty.empty_view hL hc0
    refine ⟨hT.1 hL, hT.2 (fun b m => ?_), rfl⟩
    simp only [ZkFormal.NearV3.Assembly.mrkTrafficE, decide_true, ite_true, List.map_nil,
      List.count_nil]
    exact ⟨hz b true m, hz b false m⟩
  · have hn1 : 1 ≤ os.length := List.length_pos_iff.mpr he
    refine ⟨hT.1 hL, hT.2 ?_, ?_⟩
    · have ht := outcome_nonempty_traffic os pub hn1 hn
      simp only [ZkFormal.NearV3.Assembly.mrkTrafficE, he, decide_false,
        Bool.false_eq_true, ite_false]
      exact ht
    · show (outcomeTrace os pub).log T_MRK % 3 = 1
      have h0 : os.length ≠ 0 := by omega
      simp only [outcomeTrace, MerkleRender.honestTrace, if_neg h0]
      change (19 : Nat) % 3 = 1
      rfl

end ZkFormal.NearV3.Render
