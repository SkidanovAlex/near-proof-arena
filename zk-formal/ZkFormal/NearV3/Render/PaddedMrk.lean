import ZkFormal.NearV3.Render.PaddedCongr
import ZkFormal.NearV3.Candidates.MerkleRender.NativeTraffic

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

end ZkFormal.NearV3.Render
