import NearCompression.BusTraceChallengeBound

namespace NearCompression
open Lean.Grind ZkFormal.Air ZkFormal.V2
variable {F : Type} [CommRing F] [DecidableEq F] [PubVal F]

/-- One candidate per row/interaction, irrespective of multiplicity or side.
Zero-multiplicity entries may remain; they only make the bound conservative. -/
def busSupportTables (tr : Trace F) (pub : List F) : List Table → Nat → List (Nat × List F)
  | [], _ => []
  | table::rest,t => (List.range (tr.height t)).flatMap (fun r=>
      table.interactions.map (fun i=>(i.bus,i.msgVal tr t r pub))) ++ busSupportTables tr pub rest (t+1)

def busTraceSupport (air : AirP) (tr : Trace F) (pub : List F) : List (Nat × List F) :=
  busSupportTables tr pub air.tables 0 ++ (pubMsgs air pub).map (fun x=>(x.1,x.2.2))

def busSupportSize (tr : Trace F) : List Table → Nat → Nat
  | [], _ => 0
  | table::rest,t => tr.height t*table.interactions.length+busSupportSize tr rest (t+1)

omit [PubVal F] in
private theorem table_covered (tr : Trace F) (pub : List F) (side : Bool)
    (tables : List Table) (t : Nat) (message : Nat × List F)
    (member : message∈busTraceTables tr pub side tables t) :
    message∈busSupportTables tr pub tables t := by
  induction tables generalizing t with
  | nil => simp [busTraceTables] at member
  | cons table rest ih =>
    simp only [busTraceTables,List.mem_append] at member
    simp only [busSupportTables,List.mem_append]
    rcases member with head|tail
    · left
      obtain ⟨r,hr,hm⟩:=List.mem_flatMap.mp head
      unfold busTraceRow at hm
      obtain ⟨i,hi,hcopy⟩:=List.mem_flatMap.mp hm
      split at hcopy
      · have eq:=List.eq_of_mem_replicate hcopy
        exact List.mem_flatMap.mpr ⟨r,hr,List.mem_map.mpr ⟨i,hi,eq.symm⟩⟩
      · simp at hcopy
    · exact Or.inr (ih (t+1) tail)

/-- Coverage is derived from the actual trace, including all public traffic. -/
theorem bus_trace_support_covers (air : AirP) (tr : Trace F) (pub : List F) (side : Bool)
    (message : Nat × List F) (member : message∈busTraceMessages air tr pub side) :
    message∈busTraceSupport air tr pub := by
  rcases List.mem_append.mp member with source|pubMember
  · exact List.mem_append_left _ (table_covered tr pub side air.tables 0 message source)
  · obtain ⟨record,hr,eq⟩:=List.mem_map.mp pubMember
    exact List.mem_append_right _ (List.mem_map.mpr ⟨record,(List.mem_filter.mp hr).1,eq⟩)

omit [DecidableEq F] [PubVal F] in
private theorem tables_length (tr : Trace F) (pub : List F) (tables : List Table) (t : Nat) :
    (busSupportTables tr pub tables t).length=busSupportSize tr tables t := by
  induction tables generalizing t with
  | nil => rfl
  | cons table rest ih =>
    simp only [busSupportTables,List.length_append,List.length_flatMap,List.length_map,ih,busSupportSize]
    have constant (xs : List Nat) (n : Nat) : (xs.map (fun _=>n)).sum=xs.length*n := by
      induction xs with
      | nil => simp
      | cons x xs ih => simp only [List.map_cons,List.sum_cons,List.length_cons,ih,Nat.add_mul,Nat.one_mul]; omega
    rw [constant,List.length_range]

/-- Multiplicity does not inflate fingerprint support: the exact candidate
count is row/interaction pairs plus public records. -/
theorem bus_trace_support_length (air : AirP) (tr : Trace F) (pub : List F) :
    (busTraceSupport air tr pub).length=busSupportSize tr air.tables 0+(pubMsgs air pub).length := by
  simp only [busTraceSupport,List.length_append,List.length_map,tables_length]

omit [DecidableEq F] [PubVal F] in
private theorem tables_shape (tr : Trace F) (pub : List F) (tables : List Table)
    (t limit width : Nat)
    (bounds : ∀ table∈tables,∀ i∈table.interactions,i.bus<limit ∧ i.msg.length+1≤width)
    (message : Nat × List F) (member : message∈busSupportTables tr pub tables t) :
    message.1<limit ∧ message.2.length+1≤width := by
  induction tables generalizing t with
  | nil => simp [busSupportTables] at member
  | cons table rest ih =>
    rcases List.mem_append.mp member with head|tail
    · obtain ⟨r,_,hm⟩:=List.mem_flatMap.mp head
      obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hm
      simpa [Interaction.msgVal] using bounds table (by simp) i hi
    · exact ih (t+1) (fun table ht=>bounds table (by simp [ht])) tail

/-- Source descriptors and public record shapes suffice; trace values do
not influence the bus-tag or message-width bounds. -/
theorem bus_trace_support_shape (air : AirP) (tr : Trace F) (pub : List F) (limit width : Nat)
    (sourceBounds : ∀ table∈air.tables,∀ i∈table.interactions,i.bus<limit ∧ i.msg.length+1≤width)
    (publicBounds : ∀ record∈pubMsgs air pub,record.1<limit ∧ record.2.2.length+1≤width)
    (message : Nat × List F) (member : message∈busTraceSupport air tr pub) :
    message.1<limit ∧ message.2.length+1≤width := by
  rcases List.mem_append.mp member with source|pubMember
  · exact tables_shape tr pub air.tables 0 limit width sourceBounds message source
  · obtain ⟨record,hr,rfl⟩:=List.mem_map.mp pubMember
    exact publicBounds record hr

open ZkFormal.Algebra ArenaCore.Security ZkFormal.Udr

/-- The support is constructed from the trace. Only descriptor/public width
bounds remain; neither coverage nor a candidate-list size is supplied. -/
theorem bus_trace_supported_fp8_bound (air : AirP) (tr : Trace Fp) (pub : List Fp) (width : Nat)
    (sourceBounds : ∀ table∈air.tables,∀ i∈table.interactions,i.bus<P-1 ∧ i.msg.length+1≤width)
    (publicBounds : ∀ record∈pubMsgs air pub,record.1<P-1 ∧ record.2.2.length+1≤width)
    (unbalanced : ¬∀ b m,busCount air.toAir tr pub b true m+pubCount air pub b true m=
      busCount air.toAir tr pub b false m+pubCount air pub b false m)
    (alphas gammas : List Fp8) (alphaDistinct : alphas.Nodup) (gammaDistinct : gammas.Nodup) :
    let encode := busEncodeMessage Fp8.ofBase (fun b=>((b+1:Nat):Fp8))
    let send := (busTraceMessages air tr pub true).map encode
    let receive := (busTraceMessages air tr pub false).map encode
    count (alphas.flatMap (fun a=>gammas.map (fun g=>(a,g))))
      (fun pair=>((send.map (fp pair.1)).map (pair.2 - ·)).prod =
                  ((receive.map (fp pair.1)).map (pair.2 - ·)).prod) ≤
      (busSupportSize tr air.tables 0+(pubMsgs air pub).length)*width*gammas.length+
        alphas.length*max (busTraceMessages air tr pub true).length (busTraceMessages air tr pub false).length := by
  have bound:=bus_trace_fp8_joint_bound air tr pub width (busTraceSupport air tr pub)
    (by
      intro m hm
      rcases List.mem_append.mp hm with hs|hr
      · exact bus_trace_support_covers air tr pub true m hs
      · exact bus_trace_support_covers air tr pub false m hr)
    (bus_trace_support_shape air tr pub (P-1) width sourceBounds publicBounds)
    unbalanced alphas gammas alphaDistinct gammaDistinct
  rw [bus_trace_support_length] at bound
  exact bound

end NearCompression
