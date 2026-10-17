import ZkFormal.Chacha.Bus

namespace NearCompression
open Lean.Grind ZkFormal.Air ZkFormal.V2
variable {F : Type} [CommRing F] [DecidableEq F] [PubVal F]

/-- Expanded natural traffic; public inputs are arbitrary field elements,
not the byte-only public vector of the older transcript model. -/
def busTraceRow (interactions : List Interaction) (tr : Trace F) (pub : List F)
    (table row : Nat) (side : Bool) : List (Nat × List F) :=
  interactions.flatMap fun i => if i.send=side then
    List.replicate (i.multNat tr table row pub) (i.bus,i.msgVal tr table row pub) else []

def busTraceTables (tr : Trace F) (pub : List F) (side : Bool) : List Table → Nat → List (Nat × List F)
  | [], _ => []
  | table::rest, t => (List.range (tr.height t)).flatMap (fun r=>busTraceRow table.interactions tr pub t r side)
      ++ busTraceTables tr pub side rest (t+1)

def busTracePublic (air : AirP) (pub : List F) (side : Bool) : List (Nat × List F) :=
  ((pubMsgs air pub).filter (fun x=>x.2.1==side)).map (fun x=>(x.1,x.2.2))

def busTraceMessages (air : AirP) (tr : Trace F) (pub : List F) (side : Bool) : List (Nat × List F) :=
  busTraceTables tr pub side air.tables 0 ++ busTracePublic air pub side

omit [PubVal F] in
private theorem row_count (interactions : List Interaction) (tr : Trace F) (pub : List F)
    (t r b : Nat) (side : Bool) (message : List F) :
    List.count (b,message) (busTraceRow interactions tr pub t r side)=
      interactions.foldr (fun i acc=>
        (if i.bus=b ∧ i.send=side ∧ i.msgVal tr t r pub=message
          then i.multNat tr t r pub else 0)+acc) 0 := by
  induction interactions with
  | nil => rfl
  | cons i rest ih =>
    simp only [busTraceRow,List.flatMap_cons,List.count_append,List.foldr_cons] at ih ⊢
    rw [ih]
    congr 1
    by_cases hs : i.send=side
    · simp only [hs,ite_true,List.count_replicate]
      by_cases hb : i.bus=b <;> by_cases hm : i.msgVal tr t r pub=message <;> simp_all
    · simp [hs]

private theorem tables_count (tr : Trace F) (pub : List F) (side : Bool) (b : Nat) (message : List F)
    (tables : List Table) (t : Nat) :
    List.count (b,message) (busTraceTables tr pub side tables t)=busCount.go tr pub b side message tables t := by
  induction tables generalizing t with
  | nil => rfl
  | cons table rest ih =>
    simp only [busTraceTables,List.count_append,List.count_flatMap,ih,busCount.go]
    rw [ZkFormal.Chacha.tableBusCount_eq,List.count_flatMap]
    congr 1
    apply congrArg List.sum
    apply List.map_congr_left
    intro r _
    simp only [Function.comp_def]
    rw [row_count, ZkFormal.Chacha.count_rowTraffic]

private theorem public_count (air : AirP) (pub : List F) (side : Bool) (b : Nat) (message : List F) :
    List.count (b,message) (busTracePublic air pub side)=pubCount air pub b side message := by
  unfold busTracePublic pubCount
  generalize pubMsgs air pub=messages
  induction messages with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨xb,xs,xm⟩:=x
    by_cases hs : xs=side
    · subst xs
      simp only [List.filter_cons,beq_self_eq_true,ite_true,List.map_cons,List.count_cons]
      by_cases hb : xb=b <;> by_cases hm : xm=message <;> simp_all
    · simp [hs,ih]

/-- Exact natural counts, including multiplicity expansion and public records. -/
theorem bus_trace_messages_count (air : AirP) (tr : Trace F) (pub : List F)
    (side : Bool) (b : Nat) (message : List F) :
    List.count (b,message) (busTraceMessages air tr pub side)=
      busCount air.toAir tr pub b side message+pubCount air pub b side message := by
  rw [busTraceMessages,List.count_append,tables_count,public_count]
  rfl

/-- Exact equivalence for the balance field of HoldsP, before probabilistic
fingerprinting or any commitment assumptions are introduced. -/
theorem bus_trace_balance_iff_perm (air : AirP) (tr : Trace F) (pub : List F) :
    (∀ b m,busCount air.toAir tr pub b true m+pubCount air pub b true m=
      busCount air.toAir tr pub b false m+pubCount air pub b false m) ↔
    (busTraceMessages air tr pub true).Perm (busTraceMessages air tr pub false) := by
  rw [List.perm_iff_count]
  constructor
  · intro balanced pair
    obtain ⟨b,m⟩:=pair
    rw [bus_trace_messages_count,bus_trace_messages_count]
    exact balanced b m
  · intro equal b m
    rw [←bus_trace_messages_count air tr pub true b m,←bus_trace_messages_count air tr pub false b m]
    exact equal (b,m)

/-- An actual imbalance forces distinct message multisets; no decoded
transcript or byte-valued-public-input assumption is needed. -/
theorem bus_trace_unbalanced_not_perm (air : AirP) (tr : Trace F) (pub : List F)
    (unbalanced : ¬∀ b m,busCount air.toAir tr pub b true m+pubCount air pub b true m=
      busCount air.toAir tr pub b false m+pubCount air pub b false m) :
    ¬(busTraceMessages air tr pub true).Perm (busTraceMessages air tr pub false) := by
  intro perm
  apply unbalanced
  intro b m
  rw [←bus_trace_messages_count air tr pub true b m,←bus_trace_messages_count air tr pub false b m]
  exact perm.count_eq _

end NearCompression
