import NearCompression.GKRSlotCertificate
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace NearCompression
/-! Fixed captured fixture only. Compiler-export correspondence is checked by
check_heterogeneous_metadata.py, not proved by this numerical certificate.
Metadata SHA256: 0f2ce239e63497278521b4cabe12139dc876ddeee75f55c98006e7c5d546fe00 -/
def literal193GKRLayout : GKRJointLayout := { rowCoordinates := 16, inputLog := 13, commonLog := 12, privateCapacity := 4096 }
def literal193GKRTables : List GKRTableMetadata := [
{ rowLog := 8, rowOffset := 0, blockOffset := 0, columnCapacity := 1024, sourceWidth := 605, auxiliaryWidth := 12, sourcePackingLog := 4, auxiliaryPackingLog := 0 },
{ rowLog := 8, rowOffset := 8, blockOffset := 2048, columnCapacity := 512, sourceWidth := 198, auxiliaryWidth := 200, sourcePackingLog := 4, auxiliaryPackingLog := 4 }]
def literal193GKRLanes : List GKRSourceLane := literal193GKRTables.flatMap gkrMetadataLanes

theorem literal193_gkr_lanes_well_formed :
    ∀ lane∈literal193GKRLanes,lane.WellFormed literal193GKRLayout := by
  exact checked_metadata_all_lanes literal193GKRLayout literal193GKRTables (by decide)

theorem literal193_gkr_lane_selectors :
    CanonicalLaneSelectors literal193GKRLayout literal193GKRLanes := by
  exact checked_lane_selectors literal193GKRLayout literal193GKRLanes (by decide)
end NearCompression
