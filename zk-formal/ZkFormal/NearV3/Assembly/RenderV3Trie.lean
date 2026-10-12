import ZkFormal.NearV3.Assembly.RenderV3A7
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
| 2 | `nodeA7` | `vs : List NodeS3`, `sel` | `NodeOk` | `nodeTraffic3 vs` ⊕ A7 |
| 3 | `HeadV3.table` (cap 13) | `hs : List HeadE` | `HeadOk` | `headTraffic hs` |
| 4 | `valA7` | `es : List ValE`, `sel` | `ValOk` | `valTraffic es` ⊕ A7 |
| 5 | `WalkV3.table` (cap 22) | `ws : List WalkR` | `Walk22Render.WalkOk` (rows `≤ 2^22`) | `walkTraffic3 ws` |
| 6 | `Uniq.table` | `L : List UEnt` | `UOk` | `uniqTraffic (uniqEntries L)` |
| 7 | `upsA7` | `insts : List UpsInst` | `UpsRenderOk` | `upsTraffic (viewOf …)` ⊕ A7 |

Each component's `tf` is *definitionally* the traffic function in the last column (the
`*_tf` lemmas), so the bus balance of a bundle built from these components is a statement
about the entry lists only.  The walk table is rendered at the fixed height `2^22`
(`nativeWalkTrace`, `22 ≡ 1 mod 3`), which is the cap of the native walk inventory
(`native_all_walk_ok`: rows `≤ 2^22`); the other tables at `padLog22 (logOf rows)`.

Tables 2, 4, 7 are the A7 extensions `nodeA7`/`valA7`/`upsA7` (`Tables/UnfoldA7.lean`); their
components are the link lane's `nodeRenderV3`/`valRenderV3`/`upsRenderV3` (`RenderV3A7.lean`),
whose traffic is `Traffic.append base (traceTraffic js …)` with `js` the appended interactions
(buses `RPL`, `RPLV`, `SIZE` only).  `ExtOf tf base` records that a component's traffic agrees
with `base` on every other bus (`nodeRenderV3_ext`, `valRenderV3_ext`, `upsRenderV3_ext`); the
trie bus balances are stated through it.
-/

namespace ZkFormal.NearV3.Assembly

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Render

variable (pub : List Fp)

theorem tables_sha (t : Nat) (ht : t < 2) :
    nearAirV3.tables[t]'(by have : nearAirV3.tables.length = 25 := rfl; omega) = shaTable := by
  rcases (show t = 0 ∨ t = 1 by omega) with rfl | rfl <;> rfl
theorem tables_head : nearAirV3.tables[T_HEAD]'(by decide) = { HeadV3.table with maxLog := 13 } := rfl
theorem tables_walk : nearAirV3.tables[T_WALK]'(by decide) = { WalkV3.table with maxLog := 22 } := rfl
theorem tables_uniq : nearAirV3.tables[T_UNIQ]'(by decide) = Uniq.table := rfl

/-- SHA bin render (table `0` or `1`). -/
def shaRenderV3 (t : Nat) (ht : t < 2) (msgs : List Sha.Gen.Msg) (hok : Sha.MsgsOk msgs) :
    TableRenderV3 pub t (by have : nearAirV3.tables.length = 25 := rfl; omega) :=
  let h := sha_aligned_complete msgs hok t pub
  ⟨shaTraceAligned msgs, shaBinTraffic msgs, (tables_sha t ht) ▸ h.1,
    (tables_sha t ht) ▸ h.2.1, h.2.2⟩

/-- `headV3` render (table `3`, cap 13). -/
def headRenderTrie (hs : List HeadE) (hok : HeadOk hs) : TableRenderV3 pub T_HEAD (by decide) :=
  let h := head_aligned_complete hs hok T_HEAD pub
  ⟨headTraceAligned hs, headTraffic hs, h.1, h.2.1, h.2.2⟩

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

/-! The traffic of each component is the entry lists' traffic function. -/

theorem shaRenderV3_tf (t : Nat) (ht : t < 2) (msgs : List Sha.Gen.Msg) (hok : Sha.MsgsOk msgs) :
    (shaRenderV3 pub t ht msgs hok).tf = shaBinTraffic msgs := rfl
theorem headRenderTrie_tf (hs : List HeadE) (hok : HeadOk hs) :
    (headRenderTrie pub hs hok).tf = headTraffic hs := rfl
theorem walkRenderTrie_tf (ws : List WalkR) (hok : ZkFormal.NearV3.Candidates.Walk22Render.WalkOk ws) :
    (walkRenderTrie pub ws hok).tf = walkTraffic3 ws := rfl
theorem uniqRenderTrie_tf (L : List UEnt) (hok : UOk L) :
    (uniqRenderTrie pub L hok).tf = uniqTraffic (uniqEntries L) := rfl


/-! ## The A7 components agree with the base traffic off `RPL`, `RPLV`, `SIZE` -/

open ZkFormal.NearV3.UnfoldA7 in
/-- `tf` agrees with `base` on every bus other than the A7 buses `RPL`, `RPLV`, `SIZE`. -/
def ExtOf (tf base : Traffic) : Prop :=
  ∀ b, b ≠ B_RPL → b ≠ B_RPLV → b ≠ B_SIZE → tf.sends b = base.sends b ∧ tf.recvs b = base.recvs b

theorem ExtOf.refl (tf : Traffic) : ExtOf tf tf := fun _ _ _ _ => ⟨rfl, rfl⟩

open ZkFormal.NearV3.UnfoldA7 in
theorem ExtOf.sel {tf base : Traffic} (h : ExtOf tf base) (b : Nat) (h1 : b ≠ B_RPL) (h2 : b ≠ B_RPLV)
    (h3 : b ≠ B_SIZE) (s : Bool) : sel s tf b = sel s base b := by
  cases s
  · exact (h b h1 h2 h3).2
  · exact (h b h1 h2 h3).1

theorem rowTraffic_off (is : List Interaction) (tr : Trace Fp) (t r : Nat) (pub : List Fp) (b : Nat)
    (s : Bool) (h : ∀ i ∈ is, i.bus ≠ b) : rowTraffic is tr t r pub b s = [] := by
  simp only [rowTraffic, List.flatMap_eq_nil_iff]
  intro i hi
  simp [h i hi]

open ZkFormal.NearV3.UnfoldA7 in
theorem extOf_append (base : Traffic) (js : List Interaction) (tr : Trace Fp) (t : Nat) (pub : List Fp)
    (hjs : (js.all fun i => i.bus == B_RPL || i.bus == B_RPLV || i.bus == B_SIZE) = true) :
    ExtOf (Traffic.append base (traceTraffic js tr t pub)) base := by
  intro b h1 h2 h3
  have hoff : ∀ s r, rowTraffic js tr t r pub b s = [] := by
    intro s r
    apply rowTraffic_off
    intro i hi hb
    have := List.all_eq_true.mp hjs i hi
    subst hb
    simp_all
  simp [Traffic.append, traceTraffic, hoff]

open ZkFormal.NearV3.UnfoldA7 in
theorem nodeRenderV3_ext (vs : List NodeS3) (hok : NodeOk vs) (sel : Nat → Bool) :
    ExtOf (nodeRenderV3 pub vs hok sel).tf (nodeTraffic3 vs) :=
  extOf_append _ _ _ _ _ (by decide +kernel)

open ZkFormal.NearV3.UnfoldA7 in
theorem valRenderV3_ext (es : List ValE) (hok : ValOk es) (sel : Nat → Bool) :
    ExtOf (valRenderV3 pub es hok sel).tf (valTraffic es) :=
  extOf_append _ _ _ _ _ (by decide +kernel)

open ZkFormal.NearV3.UnfoldA7 in
theorem upsRenderV3_ext (insts : List UpsInst) (hok : UpsRenderOk insts) :
    ExtOf (upsRenderV3 pub insts hok).tf
      (upsTraffic (UpsRows.viewOf (upsTraceAligned insts) T_UPS (UpsGen.segsOf insts))) :=
  extOf_append _ _ _ _ _ (by decide +kernel)

namespace RenderBundleV3

variable {pub : List Fp} (R : RenderBundleV3 pub)

open ZkFormal.NearV3.UnfoldA7 in
/-- A component whose traffic is an A7 extension of `base` agrees with `base` on bus `b`. -/
theorem tf_ext (t : Nat) (ht : t < nearAirV3.tables.length) {base : Traffic} (h : ExtOf (R ⟨t, ht⟩).tf base)
    (b : Nat) (h1 : b ≠ B_RPL) (h2 : b ≠ B_RPLV) (h3 : b ≠ B_SIZE) :
    (R.tf t).sends b = base.sends b ∧ (R.tf t).recvs b = base.recvs b := by
  have e : R.tf t = (R ⟨t, ht⟩).tf := by simp only [tf, ht, ↓reduceDIte]
  rw [e]; exact h b h1 h2 h3

open ZkFormal.NearV3.UnfoldA7 in
theorem tf_ext_sel (t : Nat) (ht : t < nearAirV3.tables.length) {base : Traffic} (h : ExtOf (R ⟨t, ht⟩).tf base)
    (b : Nat) (h1 : b ≠ B_RPL) (h2 : b ≠ B_RPLV) (h3 : b ≠ B_SIZE) (s : Bool) :
    sel s (R.tf t) b = sel s base b := by
  have := R.tf_ext t ht h b h1 h2 h3
  cases s
  · exact this.2
  · exact this.1

end RenderBundleV3

end ZkFormal.NearV3.Assembly
