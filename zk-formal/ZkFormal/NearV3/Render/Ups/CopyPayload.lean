import ZkFormal.NearV3.Render.Ups.CopyFields

namespace ZkFormal.NearV3.Render.UpsGen

def bitmapDelta (patch : Bool) (ts ix : Nat) : Int :=
  if patch then (if ix=0 then ind (ts=1) else 128*ind (ts≠1)) else 0

theorem FieldPayloadEdit.byte {patch : Bool} {x ts ix : Nat} {src dst : List Nat}
    (h : FieldPayloadEdit patch x src dst) (hx : x=if ts=1 then 0 else 15)
    (hi : patch=true → ix<2) :
    (dst.getD ix 0 : Int)=(src.getD ix 0 : Int)+bitmapDelta patch ts ix := by
  cases h with
  | preserve x bytes => simp [bitmapDelta]
  | insert x old hxb ho hc =>
    have hi' := hi rfl
    -- `getD` of the literal lists first: `simp`'s `getElem?_pos` route makes lean4lean's kernel
    -- reduce `(old + 32768) % 256` (free `old`) one `succ` at a time and run out of fuel
    -- (docs/logs/v3-recheck-2026-10.md).
    rcases (show ix=0 ∨ ix=1 by omega) with rfl | rfl <;>
      by_cases ht : ts=1 <;> simp only [List.getD_cons_zero, List.getD_cons_succ] <;>
      simp [hx,ht,bitmapDelta,ind] at hc ⊢ <;> omega

end ZkFormal.NearV3.Render.UpsGen
