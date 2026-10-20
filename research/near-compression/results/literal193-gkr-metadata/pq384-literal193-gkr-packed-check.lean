import NearCompression.GKRMetadataValidity
open NearCompression
def capturedLayout : GKRJointLayout := { rowCoordinates := 16, inputLog := 13, commonLog := 12, privateCapacity := 4096 }
def capturedTables : List GKRTableMetadata := [{ rowLog := 8, rowOffset := 0, blockOffset := 0, columnCapacity := 1024, sourceWidth := 605, auxiliaryWidth := 12, sourcePackingLog := 4, auxiliaryPackingLog := 0 },
{ rowLog := 8, rowOffset := 8, blockOffset := 2048, columnCapacity := 512, sourceWidth := 198, auxiliaryWidth := 200, sourcePackingLog := 4, auxiliaryPackingLog := 4 }]
def main : IO Unit := do
  if !(capturedTables.all (gkrTableMetadataCheck capturedLayout)) then throw (IO.userError "metadata rejected")
  IO.println s!"PASS {capturedTables.length} table certificates"
