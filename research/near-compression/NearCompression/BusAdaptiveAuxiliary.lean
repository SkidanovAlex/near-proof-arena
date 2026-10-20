import NearCompression.BusExt8SourceTransport

namespace NearCompression
open Lean.Grind ZkFormal.Air ZkFormal.V2 ZkFormal.Algebra ArenaCore.Security

/-- Source cells and heights are fixed. Auxiliary coordinate cells may be
chosen after alpha/gamma; they cannot overwrite a source column. -/
def busAttachAuxiliary (source : Trace Fp) (sourceWidth : Nat→Nat)
    (auxiliary : Nat→Nat→Nat→Fp) : Trace Fp where
  log:=source.log
  cell:=fun t r c=>if c<sourceWidth t then source.cell t r c else auxiliary t r c

theorem bus_attached_source_eval (source : Trace Fp) (sourceWidth : Nat→Nat)
    (auxiliary : Nat→Nat→Nat→Fp) (t r : Nat) (pubValues : List Fp)
    (e : Expr) (bound : e.colBound≤sourceWidth t) :
    e.eval (busAttachAuxiliary source sourceWidth auxiliary) t r pubValues=e.eval source t r pubValues := by
  induction e with
  | const n | pub p | isFirst | isLast | isTransition => rfl
  | col c nx =>
    have hc : c<sourceWidth t := by change c+1≤sourceWidth t at bound;omega
    simp [Expr.eval,Expr.evalWith,rowEnv,busAttachAuxiliary,Trace.height,hc]
  | add a b ha hb | mul a b ha hb =>
    have ba:=Nat.le_trans (Nat.le_max_left a.colBound b.colBound) bound
    have bb:=Nat.le_trans (Nat.le_max_right a.colBound b.colBound) bound
    simp only [Expr.eval,Expr.evalWith] at ha hb ⊢
    rw [ha ba,hb bb]
    rfl
  | neg a ha => exact congrArg Neg.neg (ha bound)

theorem bus_attached_source_interaction (source : Trace Fp) (sourceWidth : Nat→Nat)
    (auxiliary : Nat→Nat→Nat→Fp) (t r : Nat) (pubValues : List Fp) (i : Interaction)
    (bounds : ∀ e∈i.exprs,e.colBound≤sourceWidth t) :
    i.msgVal (busAttachAuxiliary source sourceWidth auxiliary) t r pubValues=i.msgVal source t r pubValues ∧
    i.multNat (busAttachAuxiliary source sourceWidth auxiliary) t r pubValues=i.multNat source t r pubValues := by
  constructor
  · unfold Interaction.msgVal
    apply List.map_congr_left
    intro e he
    exact bus_attached_source_eval source sourceWidth auxiliary t r pubValues e
      (bounds e (List.mem_append_right _ he))
  · have go (bits : List Expr) (k : Nat) (bound : ∀ e∈bits,e.colBound≤sourceWidth t) :
        Interaction.multNat.go (busAttachAuxiliary source sourceWidth auxiliary) t r pubValues bits k=
          Interaction.multNat.go source t r pubValues bits k := by
      induction bits generalizing k with
      | nil => rfl
      | cons bit rest ih =>
        simp only [Interaction.multNat.go,
          bus_attached_source_eval source sourceWidth auxiliary t r pubValues bit (bound bit (List.mem_cons_self ..))]
        rw [ih (k+1) (fun e he=>bound e (List.mem_cons_of_mem _ he))]
    exact go i.mult 0 (fun e he=>bounds e (List.mem_append_left _ he))

/-- Under generated residual validity, attached coordinates do not change any
semantic source-side product. The auxiliary choice is unrestricted. -/
theorem bus_attached_tables_fixed (tables : List Table) (source : Trace Fp) (sourceWidth : Nat→Nat)
    (auxiliary : Nat→Nat→Nat→Fp) (t : Nat) (pubValues : List Fp) (alpha gamma : Fp8)
    (finals : Nat→Nat→Fp8) (side : Bool)
    (holds : busExt8TablesResidualsZero (busAttachAuxiliary source sourceWidth auxiliary) sourceWidth
      pubValues alpha gamma finals tables t) :
    busTablesFinalPower (busAttachAuxiliary source sourceWidth auxiliary) pubValues side Fp8.ofBase
      (fun b=>((b+1:Nat):Fp8)) alpha gamma tables t=
    busTablesFinalPower source pubValues side Fp8.ofBase (fun b=>((b+1:Nat):Fp8)) alpha gamma tables t := by
  induction tables generalizing t with
  | nil => rfl
  | cons table rest ih =>
    simp only [busTablesFinalPower]
    rw [ih (t+1) holds.2.2.2.2]
    congr 1
    congr 1
    apply List.map_congr_left
    intro i hi
    by_cases direction : i.send=side
    · simp only [direction,ite_true,busInteractionFinalPower]
      change ((List.range (source.height t)).map _).prod=_
      congr 1
      apply List.map_congr_left
      intro r _
      have same:=bus_attached_source_interaction source sourceWidth auxiliary t r pubValues i (holds.2.1 i hi)
      simp only [busInteractionRowPower,same.1,same.2]
    · simp [direction]

/-- Existential witnesses are inside the challenge event: both auxiliary
coordinates and finals may depend on the sampled pair. -/
def busAdaptiveAuxiliaryAccept (air : AirP) (source : Trace Fp) (sourceWidth : Nat→Nat)
    (pubValues : List Fp) (alpha gamma : Fp8) : Prop :=
  ∃ auxiliary finals,
    busExt8TablesResidualsZero (busAttachAuxiliary source sourceWidth auxiliary) sourceWidth
      pubValues alpha gamma finals air.tables 0 ∧
    busExt8ClaimedSideProduct air (busAttachAuxiliary source sourceWidth auxiliary) sourceWidth pubValues alpha gamma finals true=
      busExt8ClaimedSideProduct air (busAttachAuxiliary source sourceWidth auxiliary) sourceWidth pubValues alpha gamma finals false

theorem bus_adaptive_auxiliary_implies_source (air : AirP) (source : Trace Fp) (sourceWidth : Nat→Nat)
    (pubValues : List Fp) (alpha gamma : Fp8)
    (accepted : busAdaptiveAuxiliaryAccept air source sourceWidth pubValues alpha gamma) :
    busGlobalSideProduct air source pubValues true Fp8.ofBase (fun b=>((b+1:Nat):Fp8)) alpha gamma=
      busGlobalSideProduct air source pubValues false Fp8.ofBase (fun b=>((b+1:Nat):Fp8)) alpha gamma := by
  obtain ⟨auxiliary,finals,holds,equal⟩:=accepted
  rw [bus_ext8_claimed_global_product _ _ _ _ _ _ _ true holds,
    bus_ext8_claimed_global_product _ _ _ _ _ _ _ false holds] at equal
  unfold busGlobalSideProduct at equal ⊢
  rw [bus_attached_tables_fixed _ _ _ _ _ _ _ _ _ true holds,
    bus_attached_tables_fixed _ _ _ _ _ _ _ _ _ false holds] at equal
  exact equal

/-- The same ideal Ext8 budget holds even for adaptively chosen auxiliary
coordinates/finals. Only the source trace and public vector are fixed. -/
theorem bus_adaptive_auxiliary_fp8_bound (air : AirP) (source : Trace Fp) (sourceWidth : Nat→Nat)
    (pubValues : List Fp) (width : Nat)
    (sourceBounds : ∀ table∈air.tables,∀ i∈table.interactions,i.bus<P-1 ∧ i.msg.length+1≤width)
    (publicBounds : ∀ record∈pubMsgs air pubValues,record.1<P-1 ∧ record.2.2.length+1≤width)
    (unbalanced : ¬∀ b m,busCount air.toAir source pubValues b true m+pubCount air pubValues b true m=
      busCount air.toAir source pubValues b false m+pubCount air pubValues b false m)
    (sample : List Fp8) (distinct : sample.Nodup) :
    count (sample.flatMap (fun a=>sample.map (fun g=>(a,g))))
      (fun pair=>busAdaptiveAuxiliaryAccept air source sourceWidth pubValues pair.1 pair.2) ≤
      busTraceErrorBudget air source pubValues width*sample.length := by
  let target := fun pair : Fp8 × Fp8=>
    busGlobalSideProduct air source pubValues true Fp8.ofBase (fun b=>((b+1:Nat):Fp8)) pair.1 pair.2=
      busGlobalSideProduct air source pubValues false Fp8.ofBase (fun b=>((b+1:Nat):Fp8)) pair.1 pair.2
  have sub := count_mono_mem (sample.flatMap (fun a=>sample.map (fun g=>(a,g))))
    (E:=fun pair=>busAdaptiveAuxiliaryAccept air source sourceWidth pubValues pair.1 pair.2)
    (F:=target) (fun pair _ h=>bus_adaptive_auxiliary_implies_source
      air source sourceWidth pubValues pair.1 pair.2 h)
  exact Nat.le_trans sub (bus_global_side_fp8_bound air source pubValues width sourceBounds publicBounds unbalanced sample distinct)

end NearCompression
