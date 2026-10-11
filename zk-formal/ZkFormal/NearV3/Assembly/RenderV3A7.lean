import ZkFormal.NearV3.Assembly.RenderV3Bundle
import ZkFormal.NearV3.Render.UnfoldA7Aligned

/-!
# ZkFormal.NearV3.Assembly.RenderV3A7 — `TableRenderV3` of the four A7 tables

The bundle components (`RenderV3Bundle.lean`) of `nodeA7` (index 2), `valA7` (4), `upsA7` (7)
and `sizeA7` (21), from the aligned renders of `Render/UnfoldA7Aligned.lean`.  The replaced
records (`sel`) and the received A7 totals (`yN`) are parameters: the bundle's `Balanced`
fixes them (the records `upsA7` sends `RPL`/`RPLV` for, and the three `SIZE` totals).
-/

namespace ZkFormal.NearV3.Assembly

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.UnfoldA7 ZkFormal.NearV3.Render

variable (pub : List Fp)

theorem tables_node : nearAirV3.tables[T_NODE]'(by decide) = nodeA7 := rfl
theorem tables_val : nearAirV3.tables[T_VAL]'(by decide) = valA7 := rfl
theorem tables_ups : nearAirV3.tables[T_UPS]'(by decide) = upsA7 := rfl
theorem tables_size : nearAirV3.tables[T_SIZE]'(by decide) = sizeA7 := rfl

/-- `nodeA7` render component. -/
def nodeRenderV3 (vs : List NodeS3) (hok : NodeOk vs) (sel : Nat → Bool) :
    TableRenderV3 pub T_NODE (by decide) :=
  let h := nodeA7_aligned_complete vs hok T_NODE pub sel
  ⟨nodeA7Trace vs T_NODE sel, _, h.1, h.2.1, h.2.2⟩

/-- `valA7` render component. -/
def valRenderV3 (es : List ValE) (hok : ValOk es) (sel : Nat → Bool) :
    TableRenderV3 pub T_VAL (by decide) :=
  let h := valA7_aligned_complete es hok T_VAL pub sel
  ⟨valA7Trace es T_VAL sel, _, h.1, h.2.1, h.2.2⟩

/-- `upsA7` render component. -/
def upsRenderV3 (insts : List UpsInst) (hok : UpsRenderOk insts) :
    TableRenderV3 pub T_UPS (by decide) :=
  let h := upsA7_aligned_complete insts hok T_UPS pub
  ⟨upsA7Trace insts T_UPS, _, h.1, h.2.1, h.2.2⟩

/-- `sizeA7` render component, given the A7 totals' running sum `≤ B0` on the last active row. -/
def sizeRenderV3 (v : ZkFormal.NearV3.SizeV) (ok : SizeOk pub v) (yN : Nat → Nat)
    (hB : ∀ r, r < (sizeTraceAligned pub v).height T_SIZE →
      (sizeTraceAligned pub v).cell T_SIZE r ZkFormal.NearV3.SizeV3.la = 1 → sizeU yN r ≤ B0) :
    TableRenderV3 pub T_SIZE (by decide) :=
  let h := sizeA7_aligned_complete pub v ok T_SIZE yN hB
  ⟨sizeA7Trace pub v T_SIZE yN, _, h.1, h.2.1, h.2.2⟩

end ZkFormal.NearV3.Assembly
