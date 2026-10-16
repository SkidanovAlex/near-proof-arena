import NearCompression.BusTraceMass
import NearCompression.BusNaturalFactor

namespace NearCompression
open Lean.Grind ZkFormal.Air ZkFormal.V2 ZkFormal.Udr
variable {F K : Type} [CommRing F] [DecidableEq F] [Field K]

private theorem product_append (xs ys : List K) : (xs++ys).prod=xs.prod*ys.prod := by
  induction xs with
  | nil => simp only [List.nil_append,List.prod_nil]; grind
  | cons x xs ih => simp only [List.cons_append,List.prod_cons,ih]; grind

private theorem product_replicate (n : Nat) (x : K) : (List.replicate n x).prod=x^n := by
  induction n with
  | zero => simp [Semiring.pow_zero]
  | succ n ih => simp only [List.replicate_succ,List.prod_cons,ih,Semiring.pow_succ]; grind

private theorem product_flatMap {A : Type} (xs : List A) (f : A→List K) :
    (xs.flatMap f).prod=(xs.map (fun x=>(f x).prod)).prod := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons,product_append,List.map_cons,List.prod_cons,ih]

private theorem product_pointwise {A : Type} (xs : List A) (f g : A→K) :
    (xs.map (fun x=>f x*g x)).prod=(xs.map f).prod*(xs.map g).prod := by
  induction xs with
  | nil => simp only [List.map_nil,List.prod_nil]; grind
  | cons x xs ih => simp only [List.map_cons,List.prod_cons,ih]; grind

private theorem product_ones {A : Type} (xs : List A) :
    (xs.map (fun _=>(1:K))).prod=1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons,List.prod_cons,ih]; grind

private theorem product_transpose {A B : Type} (xs : List A) (ys : List B) (f : A→B→K) :
    (xs.map (fun x=>(ys.map (f x)).prod)).prod=
      (ys.map (fun y=>(xs.map (fun x=>f x y)).prod)).prod := by
  induction xs with
  | nil => simp [product_ones]
  | cons x xs ih =>
    simp only [List.map_cons,List.prod_cons]
    rw [product_pointwise,ih]

def busMessageFactor (embed : F→K) (tag : Nat→K) (alpha gamma : K) (message : Nat × List F) : K :=
  gamma-fp alpha (busEncodeMessage embed tag message)

def busInteractionRowPower (tr : Trace F) (pubValues : List F) (t r : Nat)
    (embed : F→K) (tag : Nat→K) (alpha gamma : K) (i : Interaction) : K :=
  (busMessageFactor embed tag alpha gamma (i.bus,i.msgVal tr t r pubValues))^(i.multNat tr t r pubValues)

def busInteractionFinalPower (tr : Trace F) (pubValues : List F) (t : Nat)
    (embed : F→K) (tag : Nat→K) (alpha gamma : K) (i : Interaction) : K :=
  ((List.range (tr.height t)).map (fun r=>busInteractionRowPower tr pubValues t r embed tag alpha gamma i)).prod

/-- Exact natural message expansion on a row, for either direction and any
payload embedding. This is an identity, not a probabilistic balance claim. -/
theorem bus_expanded_row_product (interactions : List Interaction) (tr : Trace F) (pubValues : List F)
    (t r : Nat) (side : Bool) (embed : F→K) (tag : Nat→K) (alpha gamma : K) :
    ((busTraceRow interactions tr pubValues t r side).map (busMessageFactor embed tag alpha gamma)).prod=
      (interactions.map (fun i=>if i.send=side then busInteractionRowPower tr pubValues t r embed tag alpha gamma i else 1)).prod := by
  induction interactions with
  | nil => rfl
  | cons i rest ih =>
    simp only [busTraceRow,List.flatMap_cons,List.map_append,product_append,List.map_cons,List.prod_cons] at ih ⊢
    rw [ih]
    by_cases h : i.send=side
    · simp only [h,ite_true,List.map_replicate,product_replicate,busInteractionRowPower]
    · simp [h]

/-- Reorders the expanded row-major traffic into one final product per source
interaction. Commutativity is sufficient; zero factors need no special case. -/
theorem bus_expanded_table_product (interactions : List Interaction) (tr : Trace F) (pubValues : List F)
    (t : Nat) (side : Bool) (embed : F→K) (tag : Nat→K) (alpha gamma : K) :
    (((List.range (tr.height t)).flatMap (fun r=>busTraceRow interactions tr pubValues t r side)).map
      (busMessageFactor embed tag alpha gamma)).prod=
      (interactions.map (fun i=>if i.send=side then busInteractionFinalPower tr pubValues t embed tag alpha gamma i else 1)).prod := by
  rw [List.map_flatMap,product_flatMap]
  simp only [bus_expanded_row_product]
  rw [product_transpose]
  congr 1
  apply List.map_congr_left
  intro i _
  by_cases h : i.send=side
  · simp only [h,ite_true,busInteractionFinalPower]
  · simp [h,product_ones]

def busTablesFinalPower (tr : Trace F) (pubValues : List F) (side : Bool)
    (embed : F→K) (tag : Nat→K) (alpha gamma : K) : List Table → Nat → K
  | [],_ => 1
  | table::rest,t =>
    (table.interactions.map (fun i=>if i.send=side then busInteractionFinalPower tr pubValues t embed tag alpha gamma i else 1)).prod *
      busTablesFinalPower tr pubValues side embed tag alpha gamma rest (t+1)

theorem bus_expanded_tables_product (tables : List Table) (tr : Trace F) (pubValues : List F)
    (t : Nat) (side : Bool) (embed : F→K) (tag : Nat→K) (alpha gamma : K) :
    ((busTraceTables tr pubValues side tables t).map (busMessageFactor embed tag alpha gamma)).prod=
      busTablesFinalPower tr pubValues side embed tag alpha gamma tables t := by
  induction tables generalizing t with
  | nil => rfl
  | cons table rest ih =>
    simp only [busTraceTables,List.map_append,product_append,bus_expanded_table_product,ih,busTablesFinalPower]

/-- Full source-plus-public message product in the exact encoding used by the
joint challenge bound. Public records are counted once on their own side. -/
theorem bus_expanded_global_product [PubVal F] (air : AirP) (tr : Trace F) (pubValues : List F)
    (side : Bool) (embed : F→K) (tag : Nat→K) (alpha gamma : K) :
    ((((busTraceMessages air tr pubValues side).map (busEncodeMessage embed tag)).map (fp alpha)).map (gamma-·)).prod=
      busTablesFinalPower tr pubValues side embed tag alpha gamma air.tables 0 *
        ((busTracePublic air pubValues side).map (busMessageFactor embed tag alpha gamma)).prod := by
  simp only [List.map_map,Function.comp_def]
  change ((busTraceMessages air tr pubValues side).map (busMessageFactor embed tag alpha gamma)).prod=_
  rw [busTraceMessages,List.map_append,product_append,bus_expanded_tables_product]

def busGlobalSideProduct [PubVal F] (air : AirP) (tr : Trace F) (pubValues : List F)
    (side : Bool) (embed : F→K) (tag : Nat→K) (alpha gamma : K) : K :=
  busTablesFinalPower tr pubValues side embed tag alpha gamma air.tables 0 *
    ((busTracePublic air pubValues side).map (busMessageFactor embed tag alpha gamma)).prod

/-- The conservative concrete Ext8 bus budget now applies to the semantic
interaction-final/public-product equation. Commitments and transcript sampling
are still outside this fixed-trace, ideal-challenge theorem. -/
theorem bus_global_side_fp8_bound (air : AirP) (tr : Trace ZkFormal.Algebra.Fp)
    (pubValues : List ZkFormal.Algebra.Fp) (width : Nat)
    (sourceBounds : ∀ table∈air.tables,∀ i∈table.interactions,
      i.bus<ZkFormal.Algebra.P-1 ∧ i.msg.length+1≤width)
    (publicBounds : ∀ record∈pubMsgs air pubValues,
      record.1<ZkFormal.Algebra.P-1 ∧ record.2.2.length+1≤width)
    (unbalanced : ¬∀ b m,busCount air.toAir tr pubValues b true m+pubCount air pubValues b true m=
      busCount air.toAir tr pubValues b false m+pubCount air pubValues b false m)
    (sample : List ZkFormal.Algebra.Fp8) (distinct : sample.Nodup) :
    ArenaCore.Security.count (sample.flatMap (fun a=>sample.map (fun g=>(a,g))))
      (fun pair=>busGlobalSideProduct air tr pubValues true ZkFormal.Algebra.Fp8.ofBase
        (fun b=>((b+1:Nat):ZkFormal.Algebra.Fp8)) pair.1 pair.2=
        busGlobalSideProduct air tr pubValues false ZkFormal.Algebra.Fp8.ofBase
        (fun b=>((b+1:Nat):ZkFormal.Algebra.Fp8)) pair.1 pair.2) ≤
      busTraceErrorBudget air tr pubValues width*sample.length := by
  have bound:=bus_trace_budget_fp8_bound air tr pubValues width sourceBounds publicBounds unbalanced sample distinct
  simpa only [bus_expanded_global_product,busGlobalSideProduct] using bound

end NearCompression
