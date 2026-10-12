import ZkFormal.NearV3.Render.CodecGen
import ZkFormal.NearV3.Render.RowTraffic
import ZkFormal.NearV3.Assembly.RenderV3Bundle

/-!
# Table 11 (frozen `Sched.Codec.table`): aligned completeness for honest instance blocks

`codec_blocks_complete`: for instance blocks with `Blk.Ok` and fewer than `2^22` rows, the codec
trace `codecTrace (allDescs Bs)` has `TableLocal Sched.Codec.table`, the exact traffic
`rowsTraffic Codec.table.interactions (codecCell Bs) 22 t pub` (all interactions read the current row
only) and log `22 ≡ 1 mod 3`.  `codecRenderV3`: the `TableRenderV3` instance for table 11.
-/
namespace ZkFormal.NearV3.Render.Cdc
open ZkFormal.Air ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.Near

/-- The honest codec cells. -/
def codecCell (Bs : List Blk) (r c : Nat) : Nat :=
  Complete.natCell ((allDescs Bs).map Desc.row).toArray codecPad r c

set_option maxRecDepth 32768 in
theorem codec_interactions_current :
    Codec.interactions.all (fun i => i.exprs.all ZkFormal.NearV3.Candidates.ShaHeight.currentOnly) = true := by
  decide +kernel

theorem codec_currentOnly : CurrentOnly Codec.table.interactions := by
  intro i hi e he
  exact List.all_eq_true.mp (List.all_eq_true.mp codec_interactions_current i hi) e he

/-- **Codec (table 11) aligned completeness for honest instance blocks.** -/
theorem codec_blocks_complete (Bs : List Blk) (hok : ∀ B ∈ Bs, B.Ok)
    (hcap : (allDescs Bs).length < 2 ^ 22) (t : Nat) (pub : List Fp) :
    TableLocal Codec.table (codecTrace (allDescs Bs)) t pub ∧
    TableTraffic Codec.table.interactions (codecTrace (allDescs Bs)) t pub
      (rowsTraffic Codec.table.interactions (codecCell Bs) 22 t pub) ∧
    (codecTrace (allDescs Bs)).log t % 3 = 1 :=
  ⟨allDescs_local Bs hok hcap t pub,
   rowFn_traffic _ codec_currentOnly (codecCell Bs) _ t 22 pub rfl (fun _ _ _ => rfl),
   show 22 % 3 = 1 from rfl⟩

end ZkFormal.NearV3.Render.Cdc

namespace ZkFormal.NearV3.Render
open ZkFormal.Algebra ZkFormal.NearV3.Assembly ZkFormal.NearV3.Sched

/-- Table 11: the frozen codec over concatenated honest instance blocks. -/
def codecRenderV3 (pub : List Fp) (Bs : List Cdc.Blk) (hok : ∀ B ∈ Bs, B.Ok)
    (hcap : (Cdc.allDescs Bs).length < 2 ^ 22) : TableRenderV3 pub 11 (by decide) where
  tr := Cdc.codecTrace (Cdc.allDescs Bs)
  tf := rowsTraffic Codec.table.interactions (Cdc.codecCell Bs) 22 11 pub
  loc := (Cdc.codec_blocks_complete Bs hok hcap 11 pub).1
  traffic := (Cdc.codec_blocks_complete Bs hok hcap 11 pub).2.1
  aligned := (Cdc.codec_blocks_complete Bs hok hcap 11 pub).2.2

end ZkFormal.NearV3.Render
