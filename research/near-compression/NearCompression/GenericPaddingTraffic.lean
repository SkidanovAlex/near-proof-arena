import ZkFormal.Air.Basic

/-! Exact natural-multiplicity traffic preservation under padding. The
active prefix must include every terminal/tail row. This module does not
assert that changing height preserves local constraints or cyclic next reads. -/
namespace NearCompression

/-- Messages may include the bus and send/receive tag, so equality retains
the complete interaction identity. Multiplicity is a natural, not a field. -/
abbrev GenericTrafficRow (Message : Type) := List (Message × Nat)

def genericTrafficRowExpand {Message : Type} (row : GenericTrafficRow Message) : List Message :=
  row.flatMap fun entry => List.replicate entry.2 entry.1

def genericTrafficExpand {Message : Type} (rows : List (GenericTrafficRow Message)) : List Message :=
  rows.flatMap genericTrafficRowExpand

def GenericZeroTrafficRow {Message : Type} (row : GenericTrafficRow Message) : Prop :=
  ∀ entry ∈ row, entry.2 = 0

def GenericZeroTrafficPadding {Message : Type} (rows : List (GenericTrafficRow Message)) : Prop :=
  ∀ row ∈ rows, GenericZeroTrafficRow row

theorem generic_zero_traffic_row_expand {Message : Type} (row : GenericTrafficRow Message)
    (zero : GenericZeroTrafficRow row) : genericTrafficRowExpand row = [] := by
  induction row with
  | nil => rfl
  | cons entry rest ih =>
    have he := zero entry (List.mem_cons_self ..)
    have hr := ih (fun e hm => zero e (List.mem_cons_of_mem _ hm))
    simp only [genericTrafficRowExpand, List.flatMap_cons, he, List.replicate_zero, List.nil_append]
    exact hr

theorem generic_zero_traffic_padding_expand {Message : Type}
    (padding : List (GenericTrafficRow Message)) (zero : GenericZeroTrafficPadding padding) :
    genericTrafficExpand padding = [] := by
  induction padding with
  | nil => rfl
  | cons row rest ih =>
    have hr := generic_zero_traffic_row_expand row (zero row (List.mem_cons_self ..))
    have hs := ih (fun r hm => zero r (List.mem_cons_of_mem _ hm))
    simp only [genericTrafficExpand, List.flatMap_cons, hr, List.nil_append]
    exact hs

theorem generic_traffic_expand_append {Message : Type}
    (left right : List (GenericTrafficRow Message)) :
    genericTrafficExpand (left++right) = genericTrafficExpand left ++ genericTrafficExpand right := by
  exact List.flatMap_append

theorem generic_traffic_append_zero_padding {Message : Type}
    (active padding : List (GenericTrafficRow Message)) (zero : GenericZeroTrafficPadding padding) :
    genericTrafficExpand (active++padding) = genericTrafficExpand active := by
  rw [generic_traffic_expand_append, generic_zero_traffic_padding_expand padding zero, List.append_nil]

theorem generic_traffic_two_padding_expansions {Message : Type}
    (active padding₁ padding₂ : List (GenericTrafficRow Message))
    (zero₁ : GenericZeroTrafficPadding padding₁) (zero₂ : GenericZeroTrafficPadding padding₂) :
    genericTrafficExpand (active++padding₁) = genericTrafficExpand (active++padding₂) := by
  rw [generic_traffic_append_zero_padding active padding₁ zero₁,
    generic_traffic_append_zero_padding active padding₂ zero₂]

def genericTrafficCount {Message : Type} [DecidableEq Message]
    (rows : List (GenericTrafficRow Message)) (message : Message) : Nat :=
  (genericTrafficExpand rows).count message

/-- Same natural-count arithmetic as Air.tableBusCount once bus, direction,
and evaluated message have been bundled into the message identity. -/
def genericTrafficRowCount {Message : Type} [DecidableEq Message]
    (row : GenericTrafficRow Message) (message : Message) : Nat :=
  row.foldr (fun entry acc => (if entry.1=message then entry.2 else 0)+acc) 0

theorem generic_traffic_row_count_expand {Message : Type} [DecidableEq Message]
    (row : GenericTrafficRow Message) (message : Message) :
    (genericTrafficRowExpand row).count message = genericTrafficRowCount row message := by
  induction row with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨m,n⟩ := entry
    simp only [genericTrafficRowExpand, List.flatMap_cons, List.count_append] at *
    rw [ih]
    by_cases h : m=message
    · subst m; simp [genericTrafficRowCount]
    · simp [genericTrafficRowCount, List.count_replicate, h]

theorem generic_traffic_count_fold {Message : Type} [DecidableEq Message]
    (rows : List (GenericTrafficRow Message)) (message : Message) :
    genericTrafficCount rows message =
      rows.foldr (fun row acc => genericTrafficRowCount row message+acc) 0 := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    change (genericTrafficRowExpand row ++ genericTrafficExpand rest).count message = _
    rw [List.count_append, generic_traffic_row_count_expand]
    change genericTrafficRowCount row message + genericTrafficCount rest message = _
    rw [ih]
    rfl

theorem generic_traffic_two_padding_counts {Message : Type} [DecidableEq Message]
    (active padding₁ padding₂ : List (GenericTrafficRow Message))
    (zero₁ : GenericZeroTrafficPadding padding₁) (zero₂ : GenericZeroTrafficPadding padding₂)
    (message : Message) :
    genericTrafficCount (active++padding₁) message = genericTrafficCount (active++padding₂) message := by
  unfold genericTrafficCount
  rw [generic_traffic_two_padding_expansions active padding₁ padding₂ zero₁ zero₂]

/-- Actual AIR interactions evaluated as natural-multiplicity rows. -/
def genericAirTrafficRows {F : Type} [Lean.Grind.CommRing F] [DecidableEq F]
    (is : List ZkFormal.Air.Interaction) (tr : ZkFormal.Air.Trace F)
    (t : Nat) (pub : List F) : List (GenericTrafficRow (Nat × Bool × List F)) :=
  (List.range (tr.height t)).map fun r =>
    is.map fun i => ((i.bus,i.send,i.msgVal tr t r pub),i.multNat tr t r pub)

theorem generic_air_row_count_acc {F : Type} [Lean.Grind.CommRing F] [DecidableEq F]
    (is : List ZkFormal.Air.Interaction) (tr : ZkFormal.Air.Trace F)
    (t r : Nat) (pub : List F) (b : Nat) (send : Bool) (m : List F) (acc : Nat) :
    is.foldr (fun i acc' =>
      (if i.bus=b ∧ i.send=send ∧ i.msgVal tr t r pub=m then i.multNat tr t r pub else 0)+acc') acc =
      genericTrafficRowCount
        (is.map fun i => ((i.bus,i.send,i.msgVal tr t r pub),i.multNat tr t r pub)) (b,send,m)+acc := by
  induction is with
  | nil => simp [genericTrafficRowCount]
  | cons i rest ih =>
    simp only [List.foldr_cons, List.map_cons, genericTrafficRowCount, Prod.mk.injEq] at *
    rw [ih]
    omega

/-- The expansion counts are exactly the existing AIR's tableBusCount,
not a field-valued surrogate. -/
theorem generic_air_table_count {F : Type} [Lean.Grind.CommRing F] [DecidableEq F]
    (is : List ZkFormal.Air.Interaction) (tr : ZkFormal.Air.Trace F)
    (t : Nat) (pub : List F) (b : Nat) (send : Bool) (m : List F) :
    genericTrafficCount (genericAirTrafficRows is tr t pub) (b,send,m) =
      ZkFormal.Air.tableBusCount is tr t pub b send m := by
  rw [generic_traffic_count_fold]
  simp only [genericAirTrafficRows, List.foldr_map, ZkFormal.Air.tableBusCount]
  simp only [generic_air_row_count_acc]

/-- Direct composition into the main AIR count. Identifying each trace's
evaluated rows with active++padding remains a concrete renderer obligation. -/
theorem generic_air_table_count_padding_invariant {F : Type}
    [Lean.Grind.CommRing F] [DecidableEq F]
    (is : List ZkFormal.Air.Interaction) (left right : ZkFormal.Air.Trace F)
    (t : Nat) (pub : List F)
    (active padding₁ padding₂ : List (GenericTrafficRow (Nat × Bool × List F)))
    (leftRows : genericAirTrafficRows is left t pub = active++padding₁)
    (rightRows : genericAirTrafficRows is right t pub = active++padding₂)
    (zero₁ : GenericZeroTrafficPadding padding₁) (zero₂ : GenericZeroTrafficPadding padding₂)
    (b : Nat) (send : Bool) (m : List F) :
    ZkFormal.Air.tableBusCount is left t pub b send m =
      ZkFormal.Air.tableBusCount is right t pub b send m := by
  rw [← generic_air_table_count, ← generic_air_table_count, leftRows, rightRows]
  exact generic_traffic_two_padding_counts active padding₁ padding₂ zero₁ zero₂ (b,send,m)

end NearCompression
