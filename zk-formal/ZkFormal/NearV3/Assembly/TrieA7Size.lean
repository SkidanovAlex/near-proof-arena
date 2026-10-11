import ZkFormal.NearV3.Assembly.TrieA7Bal

/-!
# ZkFormal.NearV3.Assembly.TrieA7Size — the A7 receives of `sizeA7`

`sizeA7` (table 21) receives `SIZE (t + 3, y)` on its active rows `t = 0, 1, 2`, with `y` the
A7 total chosen for the row (`yN`).  `size_a7_recvs`: on the honest trace these receives are
exactly `[3, yN 0], [4, yN 1], [5, yN 2]` (mod `P`), and the appended interaction sends nothing.
With `node_size_sends`, `val_size_sends`, `ups_size_sends` this fixes `yN 0/1/2` to
`nodeA7Total ns S`, `valA7Total es SV`, `upsA7Total Js` for the A7 tags of the `SIZE` balance.
-/

namespace ZkFormal.NearV3.Assembly.TrieA7

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.Render
  ZkFormal.NearV3.UnfoldA7

theorem size_a7_recvs (pub : List Fp) (v : ZkFormal.NearV3.SizeV) (yN : Nat → Nat) :
    (traceTraffic UnfoldA7.Size.interactions (sizeA7Trace pub v T_SIZE yN) T_SIZE pub).recvs B_SIZE =
      [[3, yN 0 % P], [4, yN 1 % P], [5, yN 2 % P]] := by
  have hH : (sizeA7Trace pub v T_SIZE yN).height T_SIZE = 16 := rfl
  have cB : ∀ q x, q < 16 → x < 31 → (sizeA7Trace pub v T_SIZE yN).cell T_SIZE q x =
      Fp.ofNat (ZkFormal.NearV3.Render.SizeGen.cell pub v q x) := by
    intro q x hq hx
    simp only [sizeA7Trace]; rw [cell_withCols_lt hx]
    exact rowsTrace_mkTab sizeCapV3 _ _ _ q x (by show q < 2 ^ 4; omega) hx
  have cY : ∀ q, (sizeA7Trace pub v T_SIZE yN).cell T_SIZE q Size.y = ((yN q : Nat) : Fp) := by
    intro q; simp only [sizeA7Trace]; rw [cell_withCols_ge (by decide)]; simp [sizeCols, Size.y]
  simp only [traceTraffic, hH]
  rw [show List.range 16 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] from rfl]
  have o1 : Fp.ofNat 1 = (1 : Fp) := by decide
  have z : (Fp.ofNat 0 = 1) = False := by decide
  simp [o1, z, rowTraffic, UnfoldA7.Size.interactions, Dsl.recv, Interaction.multNat, Interaction.multNat.go,
    Interaction.msgVal, cY, cB _ 0 _ (show 0 < 31 by decide), cB _ 1 _ (show 1 < 31 by decide),
    ZkFormal.NearV3.Render.SizeGen.cell, ZkFormal.NearV3.SizeV3.act, ZkFormal.NearV3.SizeV3.t, toNat_natCast]
  decide

end ZkFormal.NearV3.Assembly.TrieA7
