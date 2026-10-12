import ZkFormal.NearV3.Assembly.RcptCanonicalNativeViews

/-!
# Native located-view identity for the unpatched repaired receipt trace

Ports of `RcptNativeShapeIdentity`, `RcptNativeEntityHeads`, `RcptDecodedHeadIdentity`,
`RcptDecodedNativeSequence` and `RcptCanonicalNativeViews` from the routing-q-patched trace
to the plain `booleanReceiptTrace` rendered at `nearAirV3` table 16 (`RcptV3.tableR` has no
routing-q check).  The originals use the patch only through `patch_other` on columns the
patch does not touch; the proofs are otherwise verbatim.
-/

namespace ZkFormal.NearV3.Assembly.RcptSkeleton
open NearSpec NearSpecV3 ZkFormal.Air ZkFormal.Algebra ZkFormal.Near RcptV3 RcptV3Proof

/-- Every receipt row carries the same native shape, including after q repair. -/
theorem native_shape_cellsU (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log pos : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp) (p : ReceiptPlan) (row : Coord)
    (ha : (plannedRows lists)[pos]?=some (.receipt p row)) :
    ∀c∈[Lp,Lv,Ls,kt,hr],
      (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback).cell 0 pos c=
      shapeCell p.input c := by
  intro c hc
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl
  all_goals
    rw [booleanReceiptTrace_planned_cell own ctx lists log pos constants pub digests fallback headerFallback _ ha _ (by decide)]
    rfl

theorem extracted_native_shapeU (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log pos : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp) (p : ReceiptPlan) (row : Coord)
    (ha : (plannedRows lists)[pos]?=some (.receipt p row)) (hw : p.input.receipt.wf=true)
    (hh : 2^log<Algebra.P) (h : Bool) (lp lv ls tag : Nat)
    (lay : Layout (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback)
      0 pos h lp lv ls tag) :
    (⟨pos,h,lp,lv,ls,tag⟩ : RS)=inputShape pos p.input := by
  apply layout_native_shape p.input hw (by exact hh) lay
  exact native_shape_cellsU own ctx lists log pos constants pub digests fallback headerFallback p row ha

/-- Physical native entity heads are active and distinguish list headers from
receipt blocks before any arithmetic or digest interpretation. -/
theorem native_entity_headU (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log pos : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp) (p : EntityPlan)
    (ha : (plannedRows lists)[pos]?=some p.firstRow) :
    let tr := (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback)
    tr.cell 0 pos act=1 ∧ tr.cell 0 pos sCL=(if p.isHeader then 1 else 0) := by
  dsimp only
  rw [booleanReceiptTrace_planned_cell own ctx lists log pos constants pub digests fallback headerFallback _ ha act (by decide),
    booleanReceiptTrace_planned_cell own ctx lists log pos constants pub digests fallback headerFallback _ ha sCL (by decide)]
  cases p <;> exact ⟨rfl,rfl⟩

theorem decoded_head_identityU (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log pos : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp) (p : EntityPlan) (d : DecodedEntity)
    (ha : (plannedRows lists)[pos]?=some p.firstRow)
    (hw : ∀rp,p=EntityPlan.receipt rp→rp.input.receipt.wf=true)
    (hh : 2^log<Algebra.P)
    (hL : TableLocal receiptArithmeticCandidate
      (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0 pub)
    (hs : d.start=pos)
    (hd : d.Valid (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback)) :
    d=nativeEntity pos p := by
  have hc := native_entity_headU own ctx lists log pos constants pub digests fallback headerFallback p ha
  cases d with
  | header s =>
    change s=pos at hs
    subst s
    have hf := hd.st 0 (by decide)
    simp only [Nat.add_zero] at hf
    cases p with
    | header lp => rfl
    | receipt rp =>
      have hz : _= (0:Fp) := hc.2
      have he := hf.symm.trans hz
      have hn : (1:Fp)≠0 := by decide
      exact False.elim (hn he)
  | receipt y =>
    change y.s=pos at hs
    have hf := ReceiptCandidateProof.Layout.row_flags hL hd 0
      (by have := total_pos y.h y.Lp y.Lv y.Ls y.kt;unfold RS.tot;omega)
    simp only [Nat.add_zero,hs] at hf
    cases p with
    | header lp =>
      have ho : _= (1:Fp) := hc.2
      have he := hf.2.symm.trans ho
      have hn : (0:Fp)≠1 := by decide
      exact False.elim (hn he)
    | receipt rp =>
      have he := extracted_native_shapeU own ctx lists log pos constants pub digests fallback headerFallback rp
        ⟨sPL,0,4⟩ ha (hw rp rfl) hh y.h y.Lp y.Lv y.Ls y.kt (by simpa only [DecodedEntity.Valid,hs] using hd)
      have hy0 : y=(⟨pos,y.h,y.Lp,y.Lv,y.Ls,y.kt⟩ : RS) := by cases y; simp_all
      have hy := hy0.trans he
      rw [hy]
      rfl

section seqU
private theorem decoded_activeU {tr : Trace Fp} {d : DecodedEntity} (hd : d.Valid tr) :
    tr.cell 0 d.start act=1 := by
  cases d with
  | header s => simpa [DecodedEntity.start] using hd.act 0 (by decide)
  | receipt y =>
    have hf := hd.flds (sPL,0,4) (by simp [plan])
    simpa [DecodedEntity.start] using hf.fld.act 0 (by decide)

variable (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp)

private abbrev renderU := booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback

theorem native_paddingU (pos : Nat) (hp : (plannedRows lists).length≤pos) :
    (renderU own ctx lists log constants pub digests fallback headerFallback).cell 0 pos act=0 := by
  rw [booleanReceiptTrace_control own ctx lists log pos constants pub digests fallback headerFallback act (by decide)]
  rw [List.getElem?_eq_none hp]

include own ctx lists log constants pub digests fallback headerFallback in
private theorem decoded_native_tailU
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) (hh : 2^log<Algebra.P)
    (hL : TableLocal receiptArithmeticCandidate (renderU own ctx lists log constants pub digests fallback headerFallback) 0 pub)
    (es pre : List EntityPlan) (ds : List DecodedEntity) (endPos : Nat)
    (he : entityPlans lists=pre++es)
    (hd : DecodedSequence (renderU own ctx lists log constants pub digests fallback headerFallback)
      (pre.flatMap EntityPlan.rows).length ds endPos)
    (hend : (renderU own ctx lists log constants pub digests fallback headerFallback).cell 0 endPos act=0) :
    ds=nativeEntities (pre.flatMap EntityPlan.rows).length es := by
  induction es generalizing pre ds with
  | nil =>
    cases ds with
    | nil => rfl
    | cons d ds =>
      have hz := native_paddingU own ctx lists log constants pub digests fallback headerFallback
        (pre.flatMap EntityPlan.rows).length (by simp only [←entityPlans_rows,he,List.append_nil];exact Nat.le_refl _)
      have ho := decoded_activeU hd.2.1
      rw [hd.1] at ho
      have hn : (1:Fp)≠0 := by decide
      exact False.elim (hn (ho.symm.trans hz))
  | cons p es ih =>
    have ha := entity_head_lookup lists pre es p he
    have hf := native_entity_headU own ctx lists log (pre.flatMap EntityPlan.rows).length
      constants pub digests fallback headerFallback p ha
    cases ds with
    | nil =>
      change (pre.flatMap EntityPlan.rows).length=endPos at hd
      rw [hd] at hf
      have hn : (1:Fp)≠0 := by decide
      exact False.elim (hn (hf.1.symm.trans hend))
    | cons d ds =>
      have hp : p∈entityPlans lists := by rw [he];simp
      have heq := decoded_head_identityU own ctx lists log (pre.flatMap EntityPlan.rows).length
        constants pub digests fallback headerFallback p d ha
        (fun rp hr=>entityPlans_receipt_wf lists hw rp (by simpa only [hr] using hp)) hh hL hd.1 hd.2.1
      subst d
      have hei : entityPlans lists=(pre++[p])++es := by simpa only [List.append_assoc,List.singleton_append] using he
      have hdi : DecodedSequence (renderU own ctx lists log constants pub digests fallback headerFallback)
          ((pre++[p]).flatMap EntityPlan.rows).length ds endPos := by
        simpa only [List.flatMap_append,List.flatMap_singleton,List.length_append,nativeEntity_rows] using hd.2.2
      have ht := ih (pre++[p]) ds hei hdi
      simp only [List.flatMap_append,List.flatMap_singleton,List.length_append] at ht
      exact congrArg (List.cons (nativeEntity (pre.flatMap EntityPlan.rows).length p)) ht

theorem decoded_native_sequenceU
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) (hh : 2^log<Algebra.P)
    (hL : TableLocal receiptArithmeticCandidate (renderU own ctx lists log constants pub digests fallback headerFallback) 0 pub)
    (ds : List DecodedEntity) (endPos : Nat)
    (hd : DecodedSequence (renderU own ctx lists log constants pub digests fallback headerFallback) 0 ds endPos)
    (hend : (renderU own ctx lists log constants pub digests fallback headerFallback).cell 0 endPos act=0) :
    ds=nativeEntities 0 (entityPlans lists) :=
  decoded_native_tailU own ctx lists log constants pub digests fallback headerFallback hw hh hL
    (entityPlans lists) [] ds endPos rfl hd hend

end seqU
/-- The actual canonical ListChain's flat receipt views equal the executable
native locations. No assumed leaf identity, ordering, or layout match is used. -/
theorem canonical_native_viewsU (own : Nat) (ctx : ApplyCtx) (lists : List (List Input))
    (log : Nat) (constants : ReceiptPlan→Nat→Fp) (pub : List Fp)
    (digests : ReceiptPlan→Nat→List Fp) (fallback : ReceiptPlan→Coord→Nat→Fp)
    (headerFallback : ListPlan→Coord→Nat→Fp)
    (hw : ∀xs∈lists,∀x∈xs,x.receipt.wf=true) (hh : 2^log<Algebra.P)
    (hL : TableLocal receiptArithmeticCandidate (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0 pub)
    (bs : List ListBlock) (e : Nat)
    (hc : ListChain (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0 0 bs e) :
    flatR (bs.map (RcptV3Proof.ListBlock.view (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) 0))=
      locatedViews (booleanReceiptTrace own ctx lists log constants pub digests fallback headerFallback) lists := by
  have he := decoded_native_sequenceU own ctx lists log constants pub digests fallback headerFallback hw hh hL
    _ e (ListChain.decoded hc) (ReceiptCandidateProof.ListChain.end_padding hc).2
  rw [←decoded_block_views,he,native_entity_views]
  rfl

end ZkFormal.NearV3.Assembly.RcptSkeleton
