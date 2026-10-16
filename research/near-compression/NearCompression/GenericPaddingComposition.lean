import NearCompression.GenericPaddingTraffic
import ZkFormal.V2.Air

/-! Composition contract for height changes. New local legality is proved
separately (e.g. with GenericPaddingLocal); exact natural traffic invariance
comes from GenericPaddingTraffic. The public tape is identical. No concrete
NEAR renderer is instantiated by this module. -/
namespace NearCompression
open ZkFormal.Air ZkFormal.V2

variable {F : Type} [Lean.Grind.CommRing F] [DecidableEq F]

theorem generic_bus_count_go_congr (tables : List Table) (left right : Trace F)
    (pub : List F) (offset b : Nat) (send : Bool) (m : List F)
    (counts : ∀ j (hj : j<tables.length),
      tableBusCount tables[j].interactions left (offset+j) pub b send m =
      tableBusCount tables[j].interactions right (offset+j) pub b send m) :
    busCount.go left pub b send m tables offset = busCount.go right pub b send m tables offset := by
  induction tables generalizing offset with
  | nil => rfl
  | cons table rest ih =>
    have head := counts 0 (by simp)
    have tail : ∀ j (hj : j<rest.length),
        tableBusCount rest[j].interactions left (offset+1+j) pub b send m =
        tableBusCount rest[j].interactions right (offset+1+j) pub b send m := by
      intro j hj
      have h := counts (j+1) (by simp; omega)
      simpa only [List.getElem_cons_succ, Nat.add_assoc, Nat.add_comm 1 j] using h
    simp only [List.getElem_cons_zero, Nat.add_zero] at head
    simp only [busCount.go]
    rw [head, ih (offset+1) tail]

theorem generic_bus_count_congr (air : Air) (left right : Trace F) (pub : List F)
    (counts : ∀ t (ht : t<air.tables.length) b send m,
      tableBusCount air.tables[t].interactions left t pub b send m =
      tableBusCount air.tables[t].interactions right t pub b send m)
    (b : Nat) (send : Bool) (m : List F) :
    busCount air left pub b send m = busCount air right pub b send m := by
  apply generic_bus_count_go_congr
  intro j hj
  simpa only [Nat.zero_add] using counts j hj b send m

variable [PubVal F]

/-- Transfer all five actual HoldsP fields; local legality and traffic are
distinct premises, with public fit inherited on the unchanged public tape. -/
theorem generic_padding_holds_transfer (air : AirP) (pub : List F) (old new : Trace F)
    (honest : HoldsP air pub old)
    (logs : ∀ t (ht : t<air.tables.length), 1≤new.log t ∧ new.log t≤air.tables[t].maxLog)
    (localConstraints : ∀ t (ht : t<air.tables.length) r, r<new.height t →
      ∀ e∈air.tables[t].constraints, e.eval new t r pub=0)
    (localBits : ∀ t (ht : t<air.tables.length) r, r<new.height t →
      ∀ i∈air.tables[t].interactions, ∀ bit∈i.mult,
        bit.eval new t r pub=0 ∨ bit.eval new t r pub=1)
    (counts : ∀ t (ht : t<air.tables.length) b send m,
      tableBusCount air.tables[t].interactions old t pub b send m =
      tableBusCount air.tables[t].interactions new t pub b send m) :
    HoldsP air pub new := by
  refine ⟨logs,localConstraints,localBits,honest.pubFit,?_⟩
  intro b m
  have sends := generic_bus_count_congr air.toAir old new pub counts b true m
  have receives := generic_bus_count_congr air.toAir old new pub counts b false m
  rw [← sends,← receives]
  exact honest.balance b m

/-- Compose the evaluated-row padding theorem directly into HoldsP transfer.
The missing renderer work is explicit: four adjacency classes for the local
premises, and each table's active/padding decomposition and zero multiplicities. -/
theorem generic_padding_holds_of_decompositions (air : AirP) (pub : List F) (old new : Trace F)
    (honest : HoldsP air pub old)
    (logs : ∀ t (ht : t<air.tables.length), 1≤new.log t ∧ new.log t≤air.tables[t].maxLog)
    (localConstraints : ∀ t (ht : t<air.tables.length) r, r<new.height t →
      ∀ e∈air.tables[t].constraints, e.eval new t r pub=0)
    (localBits : ∀ t (ht : t<air.tables.length) r, r<new.height t →
      ∀ i∈air.tables[t].interactions, ∀ bit∈i.mult,
        bit.eval new t r pub=0 ∨ bit.eval new t r pub=1)
    (active oldPadding newPadding : Nat → List (GenericTrafficRow (Nat × Bool × List F)))
    (oldRows : ∀ t (ht : t<air.tables.length),
      genericAirTrafficRows air.tables[t].interactions old t pub = active t ++ oldPadding t)
    (newRows : ∀ t (ht : t<air.tables.length),
      genericAirTrafficRows air.tables[t].interactions new t pub = active t ++ newPadding t)
    (oldZero : ∀ t,t<air.tables.length → GenericZeroTrafficPadding (oldPadding t))
    (newZero : ∀ t,t<air.tables.length → GenericZeroTrafficPadding (newPadding t)) :
    HoldsP air pub new := by
  apply generic_padding_holds_transfer air pub old new honest logs localConstraints localBits
  intro t ht b send m
  exact generic_air_table_count_padding_invariant air.tables[t].interactions old new t pub
    (active t) (oldPadding t) (newPadding t) (oldRows t ht) (newRows t ht)
    (oldZero t ht) (newZero t ht) b send m

end NearCompression
