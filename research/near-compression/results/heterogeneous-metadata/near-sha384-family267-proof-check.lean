import NearCompression.GKRMetadataValidity
open NearCompression
def capturedLayout : GKRJointLayout := { rowCoordinates := 11, inputLog := 16, commonLog := 15, privateCapacity := 32768 }
def capturedTables : List GKRTableMetadata := [{ rowLog := 8, rowOffset := 0, blockOffset := 0, columnCapacity := 8192, sourceWidth := 5234, auxiliaryWidth := 20, sourcePackingLog := 7, auxiliaryPackingLog := 0 },
{ rowLog := 2, rowOffset := 8, blockOffset := 24576, columnCapacity := 2048, sourceWidth := 1668, auxiliaryWidth := 16, sourcePackingLog := 5, auxiliaryPackingLog := 5 },
{ rowLog := 1, rowOffset := 10, blockOffset := 16384, columnCapacity := 4096, sourceWidth := 2136, auxiliaryWidth := 12, sourcePackingLog := 6, auxiliaryPackingLog := 6 }]
def main : IO Unit := do
  if !(capturedTables.all (gkrTableMetadataCheck capturedLayout)) then throw (IO.userError "metadata rejected")
  IO.println s!"PASS {capturedTables.length} table certificates"
