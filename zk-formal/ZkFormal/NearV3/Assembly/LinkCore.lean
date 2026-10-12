import ZkFormal.NearV3.Rcpt.Link.OutRoot3
import ZkFormal.NearV3.Assembly.LinkStore
import ZkFormal.NearV3.Assembly.LinkRidBytes
import ZkFormal.NearV3.Assembly.LinkFields

/-!
# ZkFormal.NearV3.Assembly.LinkCore — `LinkCoreV3Stmt` from the remaining view fields

The reconstructed views are `xOf r d = ⟨r.nodes, r.values, xHeads (r.ups.map upsE), r.lists, d⟩`
for a source dictionary `d`.  Closed here, for every `d`:

* `mainStoreBytes` (`mainStoreBytes_ext`), `receiptCount` (`receiptCount_of_records`),
  `receiptIds` (`LinkRidBytes.receiptIds_of`),
* **`executions`** (`RcptLink.executions_holdsP`, lane v3-rcpt-sound; block lookups from the walk,
  `walkD0_blocks`),
* `pathDepth` (`pathDepth_of_selected`) from `source.selected` and the dictionary depth bound.

**`LinkRestV3Stmt B`** collects exactly what is left: some dictionary `d` with the fields
`RestFieldsV3` (`shape`, `witnessBytes`, `source`, `canonicalScheduler`, `unfoldedBytes`,
`chachaWords`, and `dictDepth`: every source entry's path has `≤ Dp0` items).
**`linkCore_of_rest : LinkRestV3Stmt B → LinkCoreV3Stmt B`**.
-/

namespace ZkFormal.NearV3.Assembly

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 NearSpec NearSpecV3

/-- The views reconstructed from the records and a source dictionary. -/
def xOf (r : V3Records) (d : List DictionaryEntryV3) : ExtV3 :=
  ⟨r.nodes, r.values, LinkImplicit.xHeads (r.ups.map ZkFormal.NearV3.UpsRows.upsE), r.lists, d⟩

/-- `B2` and its predecessor exist in the walked segment. -/
theorem walkD0_blocks {cb : Bytes} {k : WalkD0} (h : walkD0 cb = .ok k) :
    ∃ block previous, k.blks[k.b2i]? = some block ∧ k.blks[k.b2i + 1]? = some previous := by
  unfold walkD0 at h
  repeat' (first
    | (obtain ⟨_, _, h⟩ := ZkFormal.NearV3.Sched.bind_ok h)
    | (split at h)
    | (dsimp only at h))
  all_goals try (cases h; done)
  all_goals try (exfalso; exact ZkFormal.NearV3.Sched.throw_ne (by assumption))
  all_goals
    simp only [pure, Except.pure, Except.ok.injEq] at *
    subst_vars
    dsimp only
    obtain ⟨b, hb, -⟩ := Option.bind_eq_some_iff.1 ‹Option.bind _ _ = some _›
    obtain ⟨h2, -⟩ := List.findIdx?_eq_some_iff_getElem.1 ‹List.findIdx? _ (List.drop _ _) = some _›
    simp only [List.length_drop] at h2
    exact ⟨_, _, hb, List.getElem?_eq_getElem (by omega)⟩


/-- The `GoodV3` fields left open by the link. -/
structure RestFieldsV3 (B : Nat) (cb : Bytes) (k : WalkD0) (x : ExtV3) : Prop where
  shape : V3.D0Shape (stateWitnessOfV3 k x)
  witnessBytes : (V3.encodeSW (stateWitnessOfV3 k x)).length ≤ 8388608
  source : SourceSemanticsV3 k x
  canonicalScheduler : (reads0f k (stateWitnessOfV3 k x)).all (canonical0f k.L) = true
  unfoldedBytes : unfoldBytes cb (witnessOfV3 k x) ≤ B
  chachaWords : chachaWords cb (witnessOfV3 k x) ≤ W0
  /-- every source entry's Merkle path has `≤ Dp0` items -/
  dictDepth : ∀ e : SourceEntryV3, Sum.inl e ∈ x.dictionary → e.path.path.length ≤ Dp0

/-- **What remains of the link**: some dictionary with the open fields. -/
def LinkRestV3Stmt (B : Nat) : Prop :=
  ∀ (cb : Bytes) (h : Hint) (p : Prep) (oh : Nat) (tr : Trace Fp) (r : V3Records) (k : WalkD0),
    prepD0 cb h = .ok p → walkD0 cb = .ok k → ClaimFieldsV3 k →
    (ZkFormal.NearV3.Public.preparedBytes p oh).length < ZkFormal.Algebra.P →
    HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr →
    V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r →
    V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r →
    ZkFormal.Near.ShaFacts
      (shaCountAt tr (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) T_SHA_T true)
      (shaCountAt tr (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) T_SHA_T false) →
    ZkFormal.Near.ShaFacts
      (shaCountAt tr (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) T_SHA_R true)
      (shaCountAt tr (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) T_SHA_R false) →
    V3Balance (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r →
    ∃ d, RestFieldsV3 B cb k (xOf r d)

/-- **The link core from the remaining fields.** -/
theorem linkCore_of_rest {B : Nat} (hR : LinkRestV3Stmt B) : LinkCoreV3Stmt B := by
  intro cb h p oh tr r k hp hw C hsz hH W T hs1 hs2 hb
  obtain ⟨d, R⟩ := hR cb h p oh tr r k hp hw C hsz hH W T hs1 hs2 hb
  have hcount := receiptCount_of_records hp W.lists (xOf r d) rfl
  have hn : h.n = (ZkFormal.NearV3.flatR r.lists).length := by
    rw [hcount]
    simp only [ExtV3.applied, xOf, ZkFormal.NearV3.flatR, List.length_flatMap, List.length_map]
  obtain ⟨block, previous, hmb, hmp⟩ := walkD0_blocks hw
  refine ⟨xOf r d, ⟨R.shape, R.witnessBytes, ?_, R.source, hcount, ?_, ?_, R.canonicalScheduler,
    R.unfoldedBytes, R.chachaWords, ?_⟩⟩
  · exact mainStoreBytes_ext hp hsz hH T W (xOf r d) rfl rfl
  · exact LinkRidBytes.receiptIds_of hp hsz hH T W (xOf r d) rfl
  · exact ZkFormal.NearV3.RcptLink.executions_holdsP hp hsz hH T W hw hn rfl rfl rfl rfl hmb hmp
  · exact pathDepth_of_selected
      (fun b hb s ci hs hh => by
        obtain ⟨e, he, hl, -⟩ := R.source.selected b hb s ci hs hh
        exact ⟨e, he, hl⟩)
      R.dictDepth

end ZkFormal.NearV3.Assembly
