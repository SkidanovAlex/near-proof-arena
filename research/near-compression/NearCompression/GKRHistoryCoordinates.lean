import NearCompression.HeterogeneousOpeningOracle
namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

/-- Row coordinates followed by final GKR left/right coordinates and gamma. -/
def gkrHistoryLength (layout : GKRJointLayout) : Nat :=
  layout.rowCoordinates+2*layout.inputLog+1

def gkrHistoryRowpoints (_layout : GKRJointLayout) (history : List K) (lane : GKRSourceLane) : Nat → K :=
  gkrPointBlock lane.rowOffset lane.rowLog (fun i => history.getD i 0)

def gkrHistoryLeft (layout : GKRJointLayout) (history : List K) : Nat → K :=
  gkrPointBlock layout.rowCoordinates layout.inputLog (fun i => history.getD i 0)

def gkrHistoryRight (layout : GKRJointLayout) (history : List K) : Nat → K :=
  gkrPointBlock (layout.rowCoordinates+layout.inputLog) layout.inputLog (fun i => history.getD i 0)

def gkrHistoryGamma (layout : GKRJointLayout) (history : List K) : K :=
  history.getD (layout.rowCoordinates+2*layout.inputLog) 0

def gkrHistoryTables (layout : GKRJointLayout) (metadata : List GKRSourceLane)
    (history : List K) : List (Nat → K) :=
  liftedHeterogeneousWeights layout.commonLog layout.inputLog metadata
    (fun lane => gkrPointBlock lane.rowOffset lane.rowLog (fun i => history.getD i 0))
    (gkrPointBlock layout.rowCoordinates layout.inputLog (fun i => history.getD i 0))
    (gkrPointBlock (layout.rowCoordinates+layout.inputLog) layout.inputLog (fun i => history.getD i 0))
    (history.getD (layout.rowCoordinates+2*layout.inputLog) 0)

private theorem block_append (history suffix : List K) (offset size : Nat)
    (fits : offset+size≤history.length) :
    gkrPointBlock offset size (fun i => (history++suffix).getD i 0)=
      gkrPointBlock offset size (fun i => history.getD i 0) := by
  funext i
  unfold gkrPointBlock
  by_cases hi : i<size
  · simp only [hi,ite_true,List.getD,List.getElem?_append_left (show offset+i<history.length by omega)]
  · simp only [hi,ite_false]

/-- Exact coefficient identity after chronological concatenation. Smaller
lanes skip low PCS coordinates; row and GKR blocks cannot read the suffix. -/
theorem gkr_history_joint_coefficients (layout : GKRJointLayout)
    (metadata : List GKRSourceLane) (valid : ∀ lane∈metadata,lane.WellFormed layout)
    (history suffix : List K) (length : history.length=gkrHistoryLength layout) :
    functionalBatchCoefficients layout.commonLog (gkrHistoryTables layout metadata history)
      (fun i => suffix.getD i 0)=
      metadata.map (fun lane => heterogeneousJointBeta layout lane (fun i => (history++suffix).getD i 0)) := by
  have bound : history.length=layout.rowCoordinates+2*layout.inputLog+1 := length
  have left := block_append history suffix layout.rowCoordinates layout.inputLog (by omega)
  have right := block_append history suffix (layout.rowCoordinates+layout.inputLog) layout.inputLog (by omega)
  have gamma : (history++suffix).getD (layout.rowCoordinates+2*layout.inputLog) 0=
      history.getD (layout.rowCoordinates+2*layout.inputLog) 0 := by
    simp only [List.getD,List.getElem?_append_left (show layout.rowCoordinates+2*layout.inputLog<history.length by omega)]
  have tables : gkrHistoryTables layout metadata (history++suffix)=gkrHistoryTables layout metadata history := by
    unfold gkrHistoryTables liftedHeterogeneousWeights
    rw [left,right,gamma]
    apply List.map_congr_left
    intro lane member
    have row := block_append history suffix lane.rowOffset lane.rowLog
      (by have fit := (valid lane member).1; omega)
    simp only [row]
  have pcs : (fun i => (history++suffix).getD (layout.rowCoordinates+2*layout.inputLog+1+i) 0)=
      (fun i => suffix.getD i 0) := by
    funext i
    simp only [List.getD,List.getElem?_append_right (show history.length≤layout.rowCoordinates+2*layout.inputLog+1+i by omega)]
    congr 2
    omega
  have result := heterogeneous_lifted_joint_coefficients layout metadata valid
    (fun i => (history++suffix).getD i 0)
  change functionalBatchCoefficients layout.commonLog (gkrHistoryTables layout metadata (history++suffix))
    (fun i => (history++suffix).getD (layout.rowCoordinates+2*layout.inputLog+1+i) 0)=_ at result
  rwa [tables,pcs] at result

/-- The fixed-history near source is the far source at the concatenated
joint point, with no hypothesis equating the two oracles. -/
theorem gkr_history_joint_oracle (layout : GKRJointLayout)
    (metadata : List GKRSourceLane) (valid : ∀ lane∈metadata,lane.WellFormed layout)
    (sources : List (K → K)) (history suffix : List K)
    (length : history.length=gkrHistoryLength layout) (x : K) :
    weightedVirtualOracle
      (functionalBatchCoefficients layout.commonLog (gkrHistoryTables layout metadata history)
        (fun i => suffix.getD i 0)) sources x=
      jointBetaSource (metadata.map (heterogeneousJointBeta layout)) sources x (history++suffix) := by
  rw [gkr_history_joint_coefficients layout metadata valid history suffix length]
  simp only [jointBetaSource,List.map_map,Function.comp_def]

/-- Inverse mapping for the actual full joint sample vector. This connects
its take/drop experiment directly to the same virtual source oracle. -/
theorem gkr_joint_split_oracle (layout : GKRJointLayout)
    (metadata : List GKRSourceLane) (valid : ∀ lane∈metadata,lane.WellFormed layout)
    (sources : List (K → K)) (point : List K)
    (length : point.length=heterogeneousJointDimension layout) (x : K) :
    weightedVirtualOracle
      (functionalBatchCoefficients layout.commonLog
        (gkrHistoryTables layout metadata (point.take (gkrHistoryLength layout)))
        (fun i => (point.drop (gkrHistoryLength layout)).getD i 0)) sources x=
      jointBetaSource (metadata.map (heterogeneousJointBeta layout)) sources x point := by
  have fits : gkrHistoryLength layout≤point.length := by
    simp only [gkrHistoryLength,heterogeneousJointDimension] at *
    omega
  have result := gkr_history_joint_oracle layout metadata valid sources
    (point.take (gkrHistoryLength layout)) (point.drop (gkrHistoryLength layout))
    (by simp [List.length_take,Nat.min_eq_left fits]) x
  simpa only [List.take_append_drop] using result

/-- Total fixed-length suffix extraction, including malformed/short inputs. -/
def gkrPCSPoint (layout : GKRJointLayout) (point : List K) : List K :=
  (List.range layout.commonLog).map (fun i => point.getD (gkrHistoryLength layout+i) 0)

theorem gkr_pcs_point_length (layout : GKRJointLayout) (point : List K) :
    (gkrPCSPoint layout point).length=layout.commonLog := by
  simp [gkrPCSPoint]

/-- On the actual joint sample space, total extraction is ordinary drop. -/
theorem gkr_pcs_point_eq_drop (layout : GKRJointLayout) (point : List K)
    (length : point.length=heterogeneousJointDimension layout) :
    gkrPCSPoint layout point=point.drop (gkrHistoryLength layout) := by
  have size : point.length=gkrHistoryLength layout+layout.commonLog := length
  apply List.ext_getElem (by simp [gkr_pcs_point_length,List.length_drop,size])
  intro i hi hj
  have bound : i<layout.commonLog := by simpa [gkr_pcs_point_length] using hi
  have index : gkrHistoryLength layout+i<point.length := by omega
  simp only [gkrPCSPoint,List.getElem_map,List.getElem_range,List.getD,
    List.getElem?_eq_getElem index,Option.getD_some,List.getElem_drop]

end NearCompression
