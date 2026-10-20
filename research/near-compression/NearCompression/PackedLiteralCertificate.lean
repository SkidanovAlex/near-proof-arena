import NearCompression.PackedLiteralCoverage

set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2

local instance : BEq Interaction := instBEqOfDecidableEq
local instance : LawfulBEq Interaction := instLawfulBEq
local instance : BEq Expr := instBEqOfDecidableEq
local instance : LawfulBEq Expr := instLawfulBEq

def packedLiteralLayouts (t : Nat) : List (Nat × Nat) :=
  if t=0 then packedExecRegions else packedCodeRegions

def packedLiteralRetained (t : Nat) : List Interaction :=
  if t=0 then packedCandidateInteractions0.take 3 else packedCandidateInteractions1.take 2

def packedLiteralExtra (t : Nat) : List Interaction :=
  if t=0 then packedCandidateInteractions0.drop 3 else packedCandidateInteractions1.drop 2

theorem packed_literal_range_table_eq : packedCandidateTable2=packedRangeTable := by rfl

private theorem concreteNoPublic : ∀ seg∈packedCandidateAir.pubSegs,seg.bus≠4 := by decide
private theorem concreteReceiver : ∀ t∈List.range 3, ∀ i∈packedCandidateAir.tables[t]!.interactions,
    i.bus=4 → i.send=false → t=2 ∧ i=packedRangeReceive := by decide
private theorem concreteSenders : ∀ t∈List.range 2, ∀ base∈packedMacroBases (packedLiteralLayouts t),
    packedRangeSend (packedColumnIndex (packedLiteralLayouts t) base)∈packedCandidateAir.tables[t]!.interactions ∧
    packedRangeSend (packedColumnIndex (packedLiteralLayouts t) (base+8))∈packedCandidateAir.tables[t]!.interactions := by decide
private theorem concreteExtra : ∀ t∈List.range 2, ∀ i∈packedLiteralExtra t,i.bus=4 := by decide
private theorem concreteOldNoRange : ∀ t∈List.range 2, ∀ i∈packedOriginalAir.tables[t]!.interactions,i.bus≠4 := by decide

/-- Closed structural certificate for the actual retained 193-instruction AIR. -/
def packedLiteralCertificate : PackedAirRefinement packedOriginalAir packedCandidateAir packedLiteralLayouts where
  originalShape := rfl
  packedShape := rfl
  publicSegments := rfl
  publicMaximum := rfl
  rangeSource := {
    noPublic := concreteNoPublic
    receiver := by
      intro t ht i hi hb hs
      exact concreteReceiver t (List.mem_range.mpr ht) i hi hb hs
    constraints := by
      intro ht e he
      exact he }
  consistent := by
    intro t ht
    have cases : t=0 ∨ t=1 := by omega
    rcases cases with h | h <;> subst t
    · exact packed_exec_layout_consistent
    · exact packed_code_layout_consistent
  maxLog := by
    intro t ht
    have cases : t=0 ∨ t=1 := by omega
    rcases cases with h | h <;> subst t <;> decide
  coverage := by
    intro t ht
    have cases : t=0 ∨ t=1 := by omega
    rcases cases with h | h <;> subst t
    · exact packedCoverageTable0
    · exact packedCoverageTable1
  retained := packedLiteralRetained
  extra := packedLiteralExtra
  splitInteractions := by
    intro t ht
    have cases : t=0 ∨ t=1 := by omega
    rcases cases with h | h <;> subst t <;> rfl
  pairings := by
    intro t ht
    apply packed_interactions_check_sound
    have cases : t=0 ∨ t=1 := by omega
    rcases cases with h | h <;> subst t <;> decide +kernel
  extraRange := fun t ht=>concreteExtra t (List.mem_range.mpr ht)
  rangeTableOnly := by decide
  oldNoRange := fun t ht=>concreteOldNoRange t (List.mem_range.mpr ht)
  senders := fun t ht=>concreteSenders t (List.mem_range.mpr ht)

/-- No external structural certificate or byte-range premise remains. -/
theorem packed_literal_holds (tr : Trace Fp) (pub : List Fp)
    (holds : HoldsP packedCandidateAir pub tr) :
    HoldsP (preparedLiteralAir 193) pub (packedLiftTrace packedLiteralLayouts tr) := by
  rw [←packed_original_literal_eq]
  exact packed_holds_refinement packedOriginalAir packedCandidateAir packedLiteralLayouts
    packedLiteralCertificate tr pub holds

end NearCompression
