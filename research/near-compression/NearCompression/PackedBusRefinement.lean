import NearCompression.PackedConstraintRefinement

/-! Exact natural bus-count preservation. These results do not substitute
field-valued sums for multiplicities or assume a particular honest witness. -/
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha

inductive PackedPairs {α β : Type} (R : α → β → Prop) : List α → List β → Prop where
  | nil : PackedPairs R [] []
  | cons {a : α} {b : β} {as : List α} {bs : List β} :
      R a b → PackedPairs R as bs → PackedPairs R (a::as) (b::bs)

private theorem flatMap_eq_of_pointwise {α β : Type} (xs : List α) (f g : α → List β)
    (same : ∀ x∈xs,f x=g x) : xs.flatMap f=xs.flatMap g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons]
    rw [same x (by simp),ih (fun y hy=>same y (by simp [hy]))]

theorem packed_mult_go_eq (old packed : Trace Fp) (pub : List Fp) (t r : Nat)
    (xs ys : List Expr)
    (values : xs.map (fun e=>e.eval old t r pub)=ys.map (fun e=>e.eval packed t r pub)) (k : Nat) :
    Interaction.multNat.go old t r pub xs k=Interaction.multNat.go packed t r pub ys k := by
  induction xs generalizing ys k with
  | nil => cases ys <;> simp_all [Interaction.multNat.go]
  | cons x xs ih =>
    cases ys with
    | nil => simp at values
    | cons y ys =>
      simp only [List.map_cons,List.cons.injEq] at values
      rw [Interaction.multNat.go,Interaction.multNat.go,values.1,ih ys values.2 (k+1)]

def PackedInteractionEq (old packed : Trace Fp) (pub : List Fp) (t r : Nat)
    (i j : Interaction) : Prop :=
  i.bus=j.bus ∧ i.send=j.send ∧ i.msgVal old t r pub=j.msgVal packed t r pub ∧
    i.multNat old t r pub=j.multNat packed t r pub

theorem packed_interaction_eq (layouts : Nat → List (Nat × Nat))
    (tr : Trace Fp) (pub : List Fp) (t r : Nat)
    (consistent : PackedLayoutConsistent (layouts t))
    (ranges : PackedMacroRanges (layouts t) (rowEnv tr t r pub)) (i j : Interaction)
    (rewrite : packedRewriteInteraction (packedConcreteMacro (layouts t))
      (packedConcreteColumn (layouts t)) i=some j) :
    PackedInteractionEq (packedLiftTrace layouts tr) tr pub t r i j := by
  obtain ⟨bus,side,msg,mult⟩:=packed_concrete_interaction (layouts t) consistent
    (rowEnv tr t r pub) rfl rfl rfl ranges i j rewrite
  have mapEq (es : List Expr) : es.map (fun e=>e.eval (packedLiftTrace layouts tr) t r pub)=
      es.map (fun e=>e.evalWith (packedLiftEnv (layouts t) (rowEnv tr t r pub))) := by
    simp only [Expr.eval,packed_lift_trace_env]
  refine ⟨bus.symm,side.symm,?_,?_⟩
  · unfold Interaction.msgVal
    rw [mapEq]
    exact msg.symm
  · apply packed_mult_go_eq
    rw [mapEq]
    exact mult.symm

theorem packed_row_traffic_eq (old packed : Trace Fp) (pub : List Fp) (t r b : Nat)
    (side : Bool) (xs ys : List Interaction)
    (paired : PackedPairs (PackedInteractionEq old packed pub t r) xs ys) :
    rowTraffic xs old t r pub b side=rowTraffic ys packed t r pub b side := by
  induction paired with
  | nil => rfl
  | cons h _ ih =>
    obtain ⟨bus,dir,msg,mult⟩:=h
    simp only [rowTraffic,List.flatMap_cons] at ih ⊢
    rw [bus,dir,msg,mult,ih]

theorem packed_table_bus_eq (old packed : Trace Fp) (pub : List Fp) (t b : Nat)
    (side : Bool) (message : List Fp) (xs ys : List Interaction)
    (height : old.height t=packed.height t)
    (paired : ∀ r,r<old.height t → PackedPairs (PackedInteractionEq old packed pub t r) xs ys) :
    tableBusCount xs old t pub b side message=tableBusCount ys packed t pub b side message := by
  rw [tableBusCount_eq,tableBusCount_eq,←height]
  congr 1
  apply flatMap_eq_of_pointwise
  intro r hr
  exact packed_row_traffic_eq old packed pub t r b side xs ys (paired r (List.mem_range.mp hr))

/-- Appending interactions on a different bus changes no traffic on this bus. -/
theorem packed_row_extra_bus (xs extra : List Interaction) (tr : Trace Fp)
    (pub : List Fp) (t r b : Nat) (side : Bool)
    (separate : ∀ i∈extra,i.bus≠b) :
    rowTraffic (xs++extra) tr t r pub b side=rowTraffic xs tr t r pub b side := by
  unfold rowTraffic
  rw [List.flatMap_append]
  have empty : extra.flatMap (fun i=>if i.bus=b ∧ i.send=side then
      List.replicate (i.multNat tr t r pub) (i.msgVal tr t r pub) else [])=[] := by
    induction extra with
    | nil => rfl
    | cons i tail ih =>
      simp only [List.flatMap_cons]
      rw [ite_eq_right (fun h=>separate i (by simp) h.1)]
      exact ih (fun j hj=>separate j (by simp [hj]))
  rw [empty,List.append_nil]

theorem packed_table_extra_bus (xs extra : List Interaction) (tr : Trace Fp)
    (pub : List Fp) (t b : Nat) (side : Bool) (message : List Fp)
    (separate : ∀ i∈extra,i.bus≠b) :
    tableBusCount (xs++extra) tr t pub b side message=tableBusCount xs tr t pub b side message := by
  rw [tableBusCount_eq,tableBusCount_eq]
  congr 1
  apply flatMap_eq_of_pointwise
  intro r _
  exact packed_row_extra_bus xs extra tr pub t r b side separate

/-- Rewritten interactions plus range-only additions preserve a complete
original table's count on every bus except the new range bus. -/
theorem packed_table_rewrite_bus_eq (layouts : Nat → List (Nat × Nat))
    (tr : Trace Fp) (pub : List Fp) (t b : Nat) (side : Bool) (message : List Fp)
    (consistent : PackedLayoutConsistent (layouts t))
    (ranges : ∀ r,r<tr.height t → PackedMacroRanges (layouts t) (rowEnv tr t r pub))
    (xs ys extra : List Interaction)
    (rewrites : PackedPairs (fun i j=>packedRewriteInteraction (packedConcreteMacro (layouts t))
      (packedConcreteColumn (layouts t)) i=some j) xs ys)
    (rangeOnly : ∀ i∈extra,i.bus=4) (notRange : b≠4) :
    tableBusCount xs (packedLiftTrace layouts tr) t pub b side message=
      tableBusCount (ys++extra) tr t pub b side message := by
  rw [packed_table_extra_bus ys extra tr pub t b side message
    (fun i hi h=>notRange (h.symm.trans (rangeOnly i hi)))]
  apply packed_table_bus_eq (packedLiftTrace layouts tr) tr pub t b side message xs ys rfl
  intro r hr
  induction rewrites with
  | nil => exact .nil
  | cons h _ ih =>
    exact .cons (packed_interaction_eq layouts tr pub t r consistent (ranges r hr) _ _ h) ih

/-- Summing the two retained tables and the appended range table preserves
all original-bus counts. Public segments are handled separately by HoldsP. -/
theorem packed_two_table_global_bus_eq (oldAir packedAir : Air) (old packed : Trace Fp)
    (pub : List Fp) (exec code newExec newCode range : Table)
    (oldTables : oldAir.tables=[exec,code])
    (newTables : packedAir.tables=[newExec,newCode,range])
    (b : Nat) (side : Bool) (message : List Fp) (notRange : b≠4)
    (execCount : tableBusCount exec.interactions old 0 pub b side message=
      tableBusCount newExec.interactions packed 0 pub b side message)
    (codeCount : tableBusCount code.interactions old 1 pub b side message=
      tableBusCount newCode.interactions packed 1 pub b side message)
    (rangeOnly : ∀ i∈range.interactions,i.bus=4) :
    busCount oldAir old pub b side message=busCount packedAir packed pub b side message := by
  have noRange : tableBusCount range.interactions packed 2 pub b side message=0 := by
    have h:=packed_table_extra_bus [] range.interactions packed pub 2 b side message
      (fun i hi eq=>notRange (eq.symm.trans (rangeOnly i hi)))
    simp only [List.nil_append] at h
    rw [h,tableBusCount_eq]
    simp only [rowTraffic,List.flatMap_nil]
    have empty (rows : List Nat) : rows.flatMap (fun _=>([] : List (List Fp)))=[] := by
      induction rows <;> simp_all
    rw [empty]
    rfl
  simp only [busCount,oldTables,newTables,busCount.go,Nat.reduceAdd,Nat.add_zero]
  rw [execCount,codeCount,noRange,Nat.add_zero]

theorem packed_interaction_bits (layouts : Nat → List (Nat × Nat))
    (tr : Trace Fp) (pub : List Fp) (t r : Nat)
    (consistent : PackedLayoutConsistent (layouts t))
    (ranges : PackedMacroRanges (layouts t) (rowEnv tr t r pub)) (i j : Interaction)
    (rewrite : packedRewriteInteraction (packedConcreteMacro (layouts t))
      (packedConcreteColumn (layouts t)) i=some j)
    (bits : ∀ e∈j.mult,e.eval tr t r pub=0 ∨ e.eval tr t r pub=1) :
    ∀ e∈i.mult,e.eval (packedLiftTrace layouts tr) t r pub=0 ∨
      e.eval (packedLiftTrace layouts tr) t r pub=1 := by
  have values:=(packed_concrete_interaction (layouts t) consistent (rowEnv tr t r pub)
    rfl rfl rfl ranges i j rewrite).2.2.2
  intro e he
  have member : e.evalWith (packedLiftEnv (layouts t) (rowEnv tr t r pub)) ∈
      j.mult.map (fun e=>e.evalWith (rowEnv tr t r pub)) := by
    rw [values]
    exact List.mem_map.mpr ⟨e,he,rfl⟩
  obtain ⟨e',he',same⟩:=List.mem_map.mp member
  have h:=bits e' he'
  simp only [Expr.eval] at h ⊢
  rw [packed_lift_trace_env,←same]
  exact h

def packedInteractionsCheck (regions : List (Nat × Nat)) : List Interaction → List Interaction → Bool
  | [],[] => true
  | i::is,j::js => decide (packedRewriteInteraction (packedConcreteMacro regions)
      (packedConcreteColumn regions) i=some j) && packedInteractionsCheck regions is js
  | _,_ => false

theorem packed_interactions_check_sound (regions : List (Nat × Nat)) (xs ys : List Interaction)
    (accepted : packedInteractionsCheck regions xs ys=true) :
    PackedPairs (fun i j=>packedRewriteInteraction (packedConcreteMacro regions)
      (packedConcreteColumn regions) i=some j) xs ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all [packedInteractionsCheck,PackedPairs.nil]
  | cons i is ih =>
    cases ys with
    | nil => simp [packedInteractionsCheck] at accepted
    | cons j js =>
      simp only [packedInteractionsCheck,Bool.and_eq_true,decide_eq_true_eq] at accepted
      exact .cons accepted.1 (ih js accepted.2)

end NearCompression
