import NearCompression.PackedBusRefinement

/-! Structural certificate for full packed-to-original HoldsP transfer.
This is semantic AIR refinement, not cryptographic acceptance soundness. -/
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Chacha

structure PackedAirRefinement (original packed : AirP) (layouts : Nat → List (Nat × Nat)) where
  originalShape : original.tables=[original.tables[0]!,original.tables[1]!]
  packedShape : packed.tables=[packed.tables[0]!,packed.tables[1]!,packed.tables[2]!]
  publicSegments : original.pubSegs=packed.pubSegs
  publicMaximum : original.maxPub=packed.maxPub
  rangeSource : PackedRangeSource packed 2
  consistent : ∀ t,t<2 → PackedLayoutConsistent (layouts t)
  maxLog : ∀ t,t<2 → packed.tables[t]!.maxLog≤original.tables[t]!.maxLog
  coverage : ∀ t,t<2 → ∀ e∈original.tables[t]!.constraints,
    PackedConstraintWitness (layouts t) packed.tables[t]!.constraints e
  retained : Nat → List Interaction
  extra : Nat → List Interaction
  splitInteractions : ∀ t,t<2 → packed.tables[t]!.interactions=retained t++extra t
  pairings : ∀ t,t<2 → PackedPairs (fun i j=>packedRewriteInteraction
    (packedConcreteMacro (layouts t)) (packedConcreteColumn (layouts t)) i=some j)
    original.tables[t]!.interactions (retained t)
  extraRange : ∀ t,t<2 → ∀ i∈extra t,i.bus=4
  rangeTableOnly : ∀ i∈packed.tables[2]!.interactions,i.bus=4
  oldNoRange : ∀ t,t<2 → ∀ i∈original.tables[t]!.interactions,i.bus≠4
  senders : ∀ t,t<2 → ∀ base∈packedMacroBases (layouts t),
    packedRangeSend (packedColumnIndex (layouts t) base)∈packed.tables[t]!.interactions ∧
    packedRangeSend (packedColumnIndex (layouts t) (base+8))∈packed.tables[t]!.interactions

private theorem pairing_member {R : Interaction → Interaction → Prop} {xs ys : List Interaction}
    (paired : PackedPairs R xs ys) (i : Interaction) (member : i∈xs) :
    ∃ j∈ys,R i j := by
  induction paired with
  | nil => simp at member
  | @cons a b as bs h tail ih =>
    rcases List.mem_cons.mp member with eq | rest
    · subst i; exact ⟨b,by simp,h⟩
    · obtain ⟨j,hj,rel⟩:=ih rest
      exact ⟨j,by simp [hj],rel⟩

private theorem no_table_bus (is : List Interaction) (tr : Trace Fp) (pub : List Fp)
    (t b : Nat) (side : Bool) (message : List Fp) (none : ∀ i∈is,i.bus≠b) :
    tableBusCount is tr t pub b side message=0 := by
  by_cases h : tableBusCount is tr t pub b side message=0
  · exact h
  apply False.elim
  obtain ⟨_,_,i,hi,bus,_,_,_⟩:=exists_of_tableBusCount h
  exact none i hi bus

/-- All original AIR obligations follow from packed HoldsP and the structural
certificate, for every trace/public input, not only the benchmark fixture. -/
theorem packed_holds_refinement (original packed : AirP) (layouts : Nat → List (Nat × Nat))
    (cert : PackedAirRefinement original packed layouts) (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP packed pub tr) : HoldsP original pub (packedLiftTrace layouts tr) := by
  have oldLength : original.tables.length=2 := congrArg List.length cert.originalShape
  have newLength : packed.tables.length=3 := congrArg List.length cert.packedShape
  have ranges (t r : Nat) (ht : t<2) (hr : r<tr.height t) :
      PackedMacroRanges (layouts t) (rowEnv tr t r pub) :=
    packed_macro_ranges_from_holds packed tr pub holds 2 cert.rangeSource (layouts t) t r
      (by omega) hr (cert.senders t ht)
  have countEq (b : Nat) (side : Bool) (message : List Fp) (hb : b≠4) :
      busCount original.toAir (packedLiftTrace layouts tr) pub b side message=
      busCount packed.toAir tr pub b side message := by
    have tableEq (t : Nat) (ht : t<2) :
        tableBusCount original.tables[t]!.interactions (packedLiftTrace layouts tr) t pub b side message=
        tableBusCount packed.tables[t]!.interactions tr t pub b side message := by
      rw [cert.splitInteractions t ht]
      exact packed_table_rewrite_bus_eq layouts tr pub t b side message (cert.consistent t ht)
        (ranges t · ht) _ _ _ (cert.pairings t ht) (cert.extraRange t ht) hb
    exact packed_two_table_global_bus_eq _ _ _ _ pub _ _ _ _ _ cert.originalShape cert.packedShape
      b side message hb (tableEq 0 (by decide)) (tableEq 1 (by decide)) cert.rangeTableOnly
  have pubEq (b : Nat) (side : Bool) (message : List Fp) :
      pubCount original pub b side message=pubCount packed pub b side message := by
    simp only [pubCount,pubMsgs,cert.publicSegments]
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro t ht
    have ht2 : t<2 := by omega
    have h:=holds.logBound t (by omega)
    have limit:=cert.maxLog t ht2
    have newHt : t<packed.tables.length := by omega
    simpa [packedLiftTrace,ht,newHt] using And.intro h.1 (Nat.le_trans h.2 (by simpa [ht,newHt] using limit))
  · intro t ht r hr e he
    have newHt : t<packed.tables.length := by omega
    apply packed_constraints_from_holds packed tr pub holds 2 cert.rangeSource layouts t r newHt hr
      (cert.consistent t (by omega)) (cert.senders t (by omega)) original.tables[t].constraints
    · intro a ha
      simpa [ht,newHt] using cert.coverage t (by omega) a (by simpa [ht] using ha)
    · exact he
  · intro t ht r hr i hi e he
    have ht2 : t<2 := by omega
    have newHt : t<packed.tables.length := by omega
    obtain ⟨j,hj,rewrite⟩:=pairing_member (cert.pairings t ht2) i (by simpa [ht] using hi)
    have member : j∈packed.tables[t].interactions := by
      have h : j∈packed.tables[t]!.interactions := by
        rw [cert.splitInteractions t ht2]
        exact List.mem_append_left _ hj
      simpa [newHt] using h
    exact packed_interaction_bits layouts tr pub t r (cert.consistent t ht2) (ranges t r ht2 hr)
      i j rewrite (holds.bits t newHt r hr j member) e he
  · simpa only [pubFit,cert.publicSegments,cert.publicMaximum] using holds.pubFit
  · intro b message
    by_cases hb : b=4
    · subst b
      have zeroCount (side : Bool) : busCount original.toAir (packedLiftTrace layouts tr) pub 4 side message=0 := by
        unfold busCount
        rw [cert.originalShape]
        simp only [busCount.go,Nat.reduceAdd,Nat.add_zero]
        rw [no_table_bus _ _ _ 0 4 side message (cert.oldNoRange 0 (by decide)),
          no_table_bus _ _ _ 1 4 side message (cert.oldNoRange 1 (by decide))]
      have zeroPub (side : Bool) : pubCount original pub 4 side message=0 := by
        rw [pubEq]
        apply pubCount_zero
        intro seg member bus
        exact False.elim (cert.rangeSource.noPublic seg member bus)
      rw [zeroCount true,zeroCount false,zeroPub true,zeroPub false]
    · rw [countEq b true message hb,countEq b false message hb,pubEq b true message,pubEq b false message]
      exact holds.balance b message

end NearCompression
