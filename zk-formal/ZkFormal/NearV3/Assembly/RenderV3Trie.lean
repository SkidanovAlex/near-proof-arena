import ZkFormal.NearV3.Assembly.RenderV3Bundle
import ZkFormal.NearV3.Render.PaddedTrie
import ZkFormal.NearV3.Render.PaddedSha
import ZkFormal.NearV3.Render.PaddedUps
import ZkFormal.NearV3.Rcpt.Candidates.NativeLookupPhysical

/-!
# ZkFormal.NearV3.Assembly.RenderV3Trie — `TableRenderV3` of the trie tables

The bundle components (`RenderV3Bundle.lean`) of the eight trie-side tables of `nearAirV3`
(indices 0–7), from the honest entry lists and their explicit honest-input conditions:

| t | table | entries | condition | traffic |
|---|---|---|---|---|
| 0, 1 | `shaTable` | `msgs : List Sha.Gen.Msg` (one bin each) | `Sha.MsgsOk` | `shaBinTraffic msgs` |
| 2 | `NodeV3.tableU` | `vs : List NodeS3` | `NodeOk` | `nodeTraffic3 vs` |
| 3 | `HeadV3.table` (cap 13) | `hs : List HeadE` | `HeadOk` | `headTraffic hs` |
| 4 | `ValV3.table` | `es : List ValE` | `ValOk` | `valTraffic es` |
| 5 | `WalkV3.table` (cap 22) | `ws : List WalkR` | `Walk22Render.WalkOk` (rows `≤ 2^22`) | `walkTraffic3 ws` |
| 6 | `Uniq.table` | `L : List UEnt` | `UOk` | `uniqTraffic (uniqEntries L)` |
| 7 | `UpsV3.table` | `insts : List UpsInst` | `UpsRenderOk` | `upsTraffic (viewOf …)` |

Each component's `tf` is *definitionally* the traffic function in the last column (the
`*_tf` lemmas), so the bus balance of a bundle built from these components is a statement
about the entry lists only.  The walk table is rendered at the fixed height `2^22`
(`nativeWalkTrace`, `22 ≡ 1 mod 3`), which is the cap of the native walk inventory
(`native_all_walk_ok`: rows `≤ 2^22`); the other tables at `padLog22 (logOf rows)`.

The A7 extensions of tables 2, 4, 7 (`UnfoldA7.nodeA7/valA7/upsA7`, lane `v3-link`) wrap
these base renders (`Trace.withCols`); on the AIR of this branch the base tables are the
entries of `nearAirV3`.
-/

namespace ZkFormal.NearV3.Assembly

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Render

variable (pub : List Fp)

theorem tables_sha (t : Nat) (ht : t < 2) :
    nearAirV3.tables[t]'(by have : nearAirV3.tables.length = 25 := rfl; omega) = shaTable := by
  rcases (show t = 0 ∨ t = 1 by omega) with rfl | rfl <;> rfl
theorem tables_node_base : nearAirV3.tables[T_NODE]'(by decide) = NodeV3.tableU := rfl
theorem tables_head : nearAirV3.tables[T_HEAD]'(by decide) = { HeadV3.table with maxLog := 13 } := rfl
theorem tables_val_base : nearAirV3.tables[T_VAL]'(by decide) = ValV3.table := rfl
theorem tables_walk : nearAirV3.tables[T_WALK]'(by decide) = { WalkV3.table with maxLog := 22 } := rfl
theorem tables_uniq : nearAirV3.tables[T_UNIQ]'(by decide) = Uniq.table := rfl
theorem tables_ups_base : nearAirV3.tables[T_UPS]'(by decide) = UpsV3.table := rfl

/-- SHA bin render (table `0` or `1`). -/
def shaRenderV3 (t : Nat) (ht : t < 2) (msgs : List Sha.Gen.Msg) (hok : Sha.MsgsOk msgs) :
    TableRenderV3 pub t (by have : nearAirV3.tables.length = 25 := rfl; omega) :=
  let h := sha_aligned_complete msgs hok t pub
  ⟨shaTraceAligned msgs, shaBinTraffic msgs, (tables_sha t ht) ▸ h.1,
    (tables_sha t ht) ▸ h.2.1, h.2.2⟩

/-- `nodeV3` render (table `2`). -/
def nodeRenderTrie (vs : List NodeS3) (hok : NodeOk vs) : TableRenderV3 pub T_NODE (by decide) :=
  let h := node_aligned_complete vs hok T_NODE pub
  ⟨nodeTraceAligned vs, nodeTraffic3 vs, h.1, h.2.1, h.2.2⟩

/-- `headV3` render (table `3`, cap 13). -/
def headRenderTrie (hs : List HeadE) (hok : HeadOk hs) : TableRenderV3 pub T_HEAD (by decide) :=
  let h := head_aligned_complete hs hok T_HEAD pub
  ⟨headTraceAligned hs, headTraffic hs, h.1, h.2.1, h.2.2⟩

/-- `valV3` render (table `4`). -/
def valRenderTrie (es : List ValE) (hok : ValOk es) : TableRenderV3 pub T_VAL (by decide) :=
  let h := val_aligned_complete es hok T_VAL pub
  ⟨valTraceAligned es, valTraffic es, h.1, h.2.1, h.2.2⟩

open ZkFormal.NearV3.Rcpt.Candidates.NodePostUpdate in
/-- `walkV3` render (table `5`, cap 22) at the fixed height `2^22`. -/
def walkRenderTrie (ws : List WalkR) (hok : ZkFormal.NearV3.Candidates.Walk22Render.WalkOk ws) :
    TableRenderV3 pub T_WALK (by decide) :=
  ⟨nativeWalkTrace ws, walkTraffic3 ws,
    ZkFormal.NearV3.Candidates.Walk22Render.walk_render_local_at _ hok _ T_WALK pub 22
      ⟨by change 1 ≤ 22; decide, by change 22 ≤ 22; decide⟩ hok.cap (by intros; rfl),
    ZkFormal.NearV3.Candidates.Walk22Render.walk_render_traffic_at _ hok _ T_WALK pub hok.cap
      (by intros; rfl),
    by change 22 % 3 = 1; decide⟩

/-- `uniqV3` render (table `6`). -/
def uniqRenderTrie (L : List UEnt) (hok : UOk L) : TableRenderV3 pub T_UNIQ (by decide) :=
  let h := uniq_aligned_complete L hok T_UNIQ pub
  ⟨uniqTraceAligned L, uniqTraffic (uniqEntries L), h.1, h.2.1, h.2.2⟩

/-- `upsV3` render (table `7`). -/
def upsRenderTrie (insts : List UpsInst) (hok : UpsRenderOk insts) : TableRenderV3 pub T_UPS (by decide) :=
  let h := ups_aligned_complete insts hok T_UPS pub
  ⟨upsTraceAligned insts,
    upsTraffic (UpsRows.viewOf (upsTraceAligned insts) T_UPS (UpsGen.segsOf insts)), h.1, h.2.1, h.2.2⟩

/-! The traffic of each component is the entry lists' traffic function. -/

theorem shaRenderV3_tf (t : Nat) (ht : t < 2) (msgs : List Sha.Gen.Msg) (hok : Sha.MsgsOk msgs) :
    (shaRenderV3 pub t ht msgs hok).tf = shaBinTraffic msgs := rfl
theorem nodeRenderTrie_tf (vs : List NodeS3) (hok : NodeOk vs) :
    (nodeRenderTrie pub vs hok).tf = nodeTraffic3 vs := rfl
theorem headRenderTrie_tf (hs : List HeadE) (hok : HeadOk hs) :
    (headRenderTrie pub hs hok).tf = headTraffic hs := rfl
theorem valRenderTrie_tf (es : List ValE) (hok : ValOk es) :
    (valRenderTrie pub es hok).tf = valTraffic es := rfl
theorem walkRenderTrie_tf (ws : List WalkR) (hok : ZkFormal.NearV3.Candidates.Walk22Render.WalkOk ws) :
    (walkRenderTrie pub ws hok).tf = walkTraffic3 ws := rfl
theorem uniqRenderTrie_tf (L : List UEnt) (hok : UOk L) :
    (uniqRenderTrie pub L hok).tf = uniqTraffic (uniqEntries L) := rfl

end ZkFormal.NearV3.Assembly
