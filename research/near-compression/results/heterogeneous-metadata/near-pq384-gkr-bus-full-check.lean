import NearCompression.GKRMetadataValidity
open NearCompression
def capturedLayout : GKRJointLayout := { rowCoordinates := 204, inputLog := 15, commonLog := 17, privateCapacity := 16384 }
def capturedTables : List GKRTableMetadata := [{ rowLog := 13, rowOffset := 0, blockOffset := 0, columnCapacity := 1024, sourceWidth := 544, auxiliaryWidth := 68, sourcePackingLog := 4, auxiliaryPackingLog := 3 },
{ rowLog := 10, rowOffset := 13, blockOffset := 2048, columnCapacity := 1024, sourceWidth := 544, auxiliaryWidth := 68, sourcePackingLog := 6, auxiliaryPackingLog := 3 },
{ rowLog := 13, rowOffset := 23, blockOffset := 4096, columnCapacity := 512, sourceWidth := 192, auxiliaryWidth := 104, sourcePackingLog := 4, auxiliaryPackingLog := 3 },
{ rowLog := 7, rowOffset := 36, blockOffset := 10240, columnCapacity := 128, sourceWidth := 73, auxiliaryWidth := 32, sourcePackingLog := 3, auxiliaryPackingLog := 2 },
{ rowLog := 10, rowOffset := 43, blockOffset := 13568, columnCapacity := 64, sourceWidth := 17, auxiliaryWidth := 36, sourcePackingLog := 1, auxiliaryPackingLog := 2 },
{ rowLog := 7, rowOffset := 53, blockOffset := 10496, columnCapacity := 128, sourceWidth := 56, auxiliaryWidth := 24, sourcePackingLog := 3, auxiliaryPackingLog := 1 },
{ rowLog := 10, rowOffset := 60, blockOffset := 10752, columnCapacity := 128, sourceWidth := 56, auxiliaryWidth := 16, sourcePackingLog := 3, auxiliaryPackingLog := 1 },
{ rowLog := 10, rowOffset := 70, blockOffset := 5120, columnCapacity := 512, sourceWidth := 202, auxiliaryWidth := 76, sourcePackingLog := 4, auxiliaryPackingLog := 3 },
{ rowLog := 1, rowOffset := 80, blockOffset := 6144, columnCapacity := 512, sourceWidth := 272, auxiliaryWidth := 16, sourcePackingLog := 6, auxiliaryPackingLog := 6 },
{ rowLog := 1, rowOffset := 81, blockOffset := 8192, columnCapacity := 256, sourceWidth := 158, auxiliaryWidth := 8, sourcePackingLog := 6, auxiliaryPackingLog := 6 },
{ rowLog := 1, rowOffset := 82, blockOffset := 11008, columnCapacity := 128, sourceWidth := 77, auxiliaryWidth := 32, sourcePackingLog := 6, auxiliaryPackingLog := 6 },
{ rowLog := 10, rowOffset := 83, blockOffset := 8704, columnCapacity := 256, sourceWidth := 91, auxiliaryWidth := 64, sourcePackingLog := 3, auxiliaryPackingLog := 3 },
{ rowLog := 10, rowOffset := 93, blockOffset := 9216, columnCapacity := 256, sourceWidth := 119, auxiliaryWidth := 40, sourcePackingLog := 4, auxiliaryPackingLog := 2 },
{ rowLog := 10, rowOffset := 103, blockOffset := 11264, columnCapacity := 128, sourceWidth := 64, auxiliaryWidth := 44, sourcePackingLog := 3, auxiliaryPackingLog := 2 },
{ rowLog := 10, rowOffset := 113, blockOffset := 13696, columnCapacity := 64, sourceWidth := 18, auxiliaryWidth := 16, sourcePackingLog := 1, auxiliaryPackingLog := 1 },
{ rowLog := 10, rowOffset := 123, blockOffset := 13824, columnCapacity := 64, sourceWidth := 33, auxiliaryWidth := 4, sourcePackingLog := 2, auxiliaryPackingLog := 0 },
{ rowLog := 7, rowOffset := 133, blockOffset := 7168, columnCapacity := 512, sourceWidth := 263, auxiliaryWidth := 72, sourcePackingLog := 5, auxiliaryPackingLog := 3 },
{ rowLog := 4, rowOffset := 140, blockOffset := 11520, columnCapacity := 128, sourceWidth := 16, auxiliaryWidth := 52, sourcePackingLog := 3, auxiliaryPackingLog := 3 },
{ rowLog := 1, rowOffset := 144, blockOffset := 14208, columnCapacity := 32, sourceWidth := 7, auxiliaryWidth := 12, sourcePackingLog := 6, auxiliaryPackingLog := 6 },
{ rowLog := 7, rowOffset := 145, blockOffset := 14272, columnCapacity := 32, sourceWidth := 6, auxiliaryWidth := 12, sourcePackingLog := 0, auxiliaryPackingLog := 0 },
{ rowLog := 10, rowOffset := 152, blockOffset := 11776, columnCapacity := 128, sourceWidth := 63, auxiliaryWidth := 20, sourcePackingLog := 3, auxiliaryPackingLog := 1 },
{ rowLog := 4, rowOffset := 162, blockOffset := 12032, columnCapacity := 128, sourceWidth := 57, auxiliaryWidth := 8, sourcePackingLog := 3, auxiliaryPackingLog := 3 },
{ rowLog := 4, rowOffset := 166, blockOffset := 12288, columnCapacity := 128, sourceWidth := 52, auxiliaryWidth := 52, sourcePackingLog := 3, auxiliaryPackingLog := 3 },
{ rowLog := 4, rowOffset := 170, blockOffset := 12544, columnCapacity := 128, sourceWidth := 60, auxiliaryWidth := 20, sourcePackingLog := 3, auxiliaryPackingLog := 3 },
{ rowLog := 1, rowOffset := 174, blockOffset := 13952, columnCapacity := 64, sourceWidth := 49, auxiliaryWidth := 4, sourcePackingLog := 6, auxiliaryPackingLog := 6 },
{ rowLog := 4, rowOffset := 175, blockOffset := 9728, columnCapacity := 256, sourceWidth := 147, auxiliaryWidth := 32, sourcePackingLog := 4, auxiliaryPackingLog := 3 },
{ rowLog := 4, rowOffset := 179, blockOffset := 12800, columnCapacity := 128, sourceWidth := 70, auxiliaryWidth := 32, sourcePackingLog := 3, auxiliaryPackingLog := 3 },
{ rowLog := 10, rowOffset := 183, blockOffset := 14336, columnCapacity := 32, sourceWidth := 15, auxiliaryWidth := 12, sourcePackingLog := 1, auxiliaryPackingLog := 0 },
{ rowLog := 1, rowOffset := 193, blockOffset := 14080, columnCapacity := 64, sourceWidth := 34, auxiliaryWidth := 12, sourcePackingLog := 6, auxiliaryPackingLog := 6 },
{ rowLog := 1, rowOffset := 194, blockOffset := 14400, columnCapacity := 32, sourceWidth := 21, auxiliaryWidth := 8, sourcePackingLog := 6, auxiliaryPackingLog := 6 },
{ rowLog := 7, rowOffset := 195, blockOffset := 13056, columnCapacity := 128, sourceWidth := 58, auxiliaryWidth := 28, sourcePackingLog := 3, auxiliaryPackingLog := 2 },
{ rowLog := 1, rowOffset := 202, blockOffset := 13312, columnCapacity := 128, sourceWidth := 67, auxiliaryWidth := 12, sourcePackingLog := 6, auxiliaryPackingLog := 6 },
{ rowLog := 1, rowOffset := 203, blockOffset := 14464, columnCapacity := 16, sourceWidth := 12, auxiliaryWidth := 4, sourcePackingLog := 6, auxiliaryPackingLog := 6 }]
def main : IO Unit := do
  if !(capturedTables.all (gkrTableMetadataCheck capturedLayout)) then throw (IO.userError "metadata rejected")
  IO.println s!"PASS {capturedTables.length} table certificates"
