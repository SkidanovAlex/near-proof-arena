import NearCompression.BusTraceSupport

namespace NearCompression
open Lean.Grind ZkFormal.Air ZkFormal.V2
variable {F : Type} [CommRing F] [DecidableEq F]

private theorem multiplicity_tail (tr : Trace F) (pub : List F) (t r : Nat) (bits : List Expr) (k : Nat) :
    Interaction.multNat.go tr t r pub bits k+2^k≤2^(k+bits.length) := by
  induction bits generalizing k with
  | nil => simp [Interaction.multNat.go]
  | cons bit rest ih =>
    have tail:=ih (k+1)
    have exponent : k+(bit::rest).length=(k+1)+rest.length := by simp; omega
    rw [exponent]
    simp only [Interaction.multNat.go]
    have power : 2^(k+1)=2^k*2 := Nat.pow_succ 2 k
    split <;> omega

/-- Exact natural multiplicity is at most 2^bitcount-1. This bound does not
assume booleanity; the semantic definition counts only bits equal to one. -/
theorem bus_interaction_multiplicity_bound (i : Interaction) (tr : Trace F) (pub : List F) (t r : Nat) :
    i.multNat tr t r pub≤2^i.mult.length-1 := by
  have bound:=multiplicity_tail tr pub t r i.mult 0
  simp only [Nat.pow_zero,Nat.zero_add] at bound
  unfold Interaction.multNat
  omega

def busRowMass (interactions : List Interaction) (side : Bool) : Nat :=
  (interactions.map (fun i=>if i.send=side then 2^i.mult.length-1 else 0)).sum

def busTableMass (tr : Trace F) (side : Bool) : List Table → Nat → Nat
  | [], _ => 0
  | table::rest,t => tr.height t*busRowMass table.interactions side+busTableMass tr side rest (t+1)

private theorem row_length (tr : Trace F) (pub : List F) (t r : Nat) (side : Bool) (interactions : List Interaction) :
    (busTraceRow interactions tr pub t r side).length≤busRowMass interactions side := by
  induction interactions with
  | nil => exact Nat.le_refl _
  | cons i rest ih =>
    simp only [busTraceRow,List.flatMap_cons,List.length_append,busRowMass,List.map_cons,List.sum_cons] at ih ⊢
    have bound:=bus_interaction_multiplicity_bound i tr pub t r
    split <;> simp_all <;> omega

private theorem sum_bound (xs : List Nat) (f : Nat→Nat) (limit : Nat)
    (bound : ∀ x∈xs,f x≤limit) : (xs.map f).sum≤xs.length*limit := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have head:=bound x (by simp)
    have tail:=ih (fun y hy=>bound y (by simp [hy]))
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

private theorem tables_length (tr : Trace F) (pub : List F) (side : Bool) (tables : List Table) (t : Nat) :
    (busTraceTables tr pub side tables t).length≤busTableMass tr side tables t := by
  induction tables generalizing t with
  | nil => exact Nat.le_refl _
  | cons table rest ih =>
    simp only [busTraceTables,List.length_append,List.length_flatMap,busTableMass]
    have rowBound:=sum_bound (List.range (tr.height t))
      (fun r=>(busTraceRow table.interactions tr pub t r side).length)
      (busRowMass table.interactions side) (fun r _=>row_length tr pub t r side table.interactions)
    rw [List.length_range] at rowBound
    exact Nat.add_le_add rowBound (ih (t+1))

/-- Public messages contribute one each; trace multiplicities use separate
side-specific descriptor budgets. No honest-witness counts are assumed. -/
theorem bus_trace_mass_bound [PubVal F] (air : AirP) (tr : Trace F) (pub : List F) (side : Bool) :
    (busTraceMessages air tr pub side).length≤
      busTableMass tr side air.tables 0+(busTracePublic air pub side).length := by
  simp only [busTraceMessages,List.length_append]
  exact Nat.add_le_add_right (tables_length tr pub side air.tables 0) _

/-- Deterministic bus-only numerator: support collision budget plus the
larger side's expanded multiplicity budget. -/
def busTraceErrorBudget [PubVal F] (air : AirP) (tr : Trace F) (pub : List F) (width : Nat) : Nat :=
  (busSupportSize tr air.tables 0+(pubMsgs air pub).length)*width+
    max (busTableMass tr true air.tables 0+(busTracePublic air pub true).length)
        (busTableMass tr false air.tables 0+(busTracePublic air pub false).length)

open ZkFormal.Algebra ArenaCore.Security ZkFormal.Udr

/-- Both challenge samples use the same distinct list. Dividing this count
by sample.length squared yields budget/sample.length in the nonempty ideal
uniform experiment. No expanded-list length or honest multiplicity premise. -/
theorem bus_trace_budget_fp8_bound (air : AirP) (tr : Trace Fp) (pub : List Fp) (width : Nat)
    (sourceBounds : ∀ table∈air.tables,∀ i∈table.interactions,i.bus<P-1 ∧ i.msg.length+1≤width)
    (publicBounds : ∀ record∈pubMsgs air pub,record.1<P-1 ∧ record.2.2.length+1≤width)
    (unbalanced : ¬∀ b m,busCount air.toAir tr pub b true m+pubCount air pub b true m=
      busCount air.toAir tr pub b false m+pubCount air pub b false m)
    (sample : List Fp8) (distinct : sample.Nodup) :
    let encode := busEncodeMessage Fp8.ofBase (fun b=>((b+1:Nat):Fp8))
    let send := (busTraceMessages air tr pub true).map encode
    let receive := (busTraceMessages air tr pub false).map encode
    count (sample.flatMap (fun a=>sample.map (fun g=>(a,g))))
      (fun pair=>((send.map (fp pair.1)).map (pair.2 - ·)).prod =
                  ((receive.map (fp pair.1)).map (pair.2 - ·)).prod) ≤
      busTraceErrorBudget air tr pub width*sample.length := by
  have bound:=bus_trace_supported_fp8_bound air tr pub width sourceBounds publicBounds
    unbalanced sample sample distinct distinct
  have sendBound:=bus_trace_mass_bound air tr pub true
  have receiveBound:=bus_trace_mass_bound air tr pub false
  have mass : max (busTraceMessages air tr pub true).length (busTraceMessages air tr pub false).length ≤
      max (busTableMass tr true air.tables 0+(busTracePublic air pub true).length)
          (busTableMass tr false air.tables 0+(busTracePublic air pub false).length) :=
    Nat.max_le.mpr ⟨Nat.le_trans sendBound (Nat.le_max_left _ _),
      Nat.le_trans receiveBound (Nat.le_max_right _ _)⟩
  have total:=Nat.le_trans bound (Nat.add_le_add_left (Nat.mul_le_mul_left sample.length mass) _)
  simpa only [busTraceErrorBudget,Nat.add_mul,Nat.mul_add,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using total

end NearCompression
