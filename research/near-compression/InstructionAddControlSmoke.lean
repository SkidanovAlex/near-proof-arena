import NearCompression.InstructionAddControl
open NearCompression NearSpecV3.Wasm ZkFormal.Algebra

/-- Independent test encoding of the documented control-column layout. -/
def controlTestRow (a b : UInt32) (pc height : Nat) : Nat → Fp :=
  let values : Array Nat := #[pc % 65536, pc / 65536,
    (pc + 1) % 65536, (pc + 1) / 65536, height, height - 1, height - 2]
  fun col =>
    if col < 104 then instructionAdd32RangeWitness a b col
    else if col = 104 then Fp.ofNat 106
    else if col < 109 then Fp.ofNat (values[col - 105]!)
    else if col = 109 then Fp.ofNat ((pc % 65536 + 1) / 65536)
    else if col < 113 then Fp.ofNat (values[col - 106]!)
    else
      let slot := col - 113
      Fp.ofNat (values[slot / 16]! / 2 ^ (slot % 16) % 2)

def checkControl (row : Nat → Fp) : Bool :=
  instructionAdd32ControlTable.constraints.all fun e =>
    decide (e.evalWith (instructionAddEnv row) = 0)

def ensureControl (b : Bool) (label : String) : IO Unit :=
  unless b do throw (IO.userError label)

/-- Mutate a metadata value and all its bits together, preserving its range check. -/
def replaceControlValue (row : Nat → Fp) (slot value : Nat) : Nat → Fp :=
  let col := if slot < 4 then 105 + slot else 106 + slot
  let base := 113 + 16 * slot
  fun i => if i = col then Fp.ofNat value
    else if base ≤ i && i < base + 16 then Fp.ofNat (value / 2 ^ (i - base) % 2)
    else row i

def main : IO Unit := do
  let inputs : List (Nat × Nat × Nat × Nat) := [
    (0,0,0,2),(65535,1,65535,2),(4294967295,1,65536,65535),
    (4294967295,4294967295,4294967294,65535),
    (2147483648,2147483648,123456,3),(305419896,2596069104,1,8192)]
  let mut mutations := 0
  let mut coherent := 0
  for (a,b,pc,height) in inputs do
    let row := controlTestRow (UInt32.ofNat a) (UInt32.ofNat b) pc height
    ensureControl (checkControl row) "honest control row rejected"
    let formal := instructionAdd32ControlWitness (UInt32.ofNat a) (UInt32.ofNat b) pc height
    ensureControl ((List.range 225).all fun col => decide (row col = formal col))
      "independent/formal witness mismatch"
    ensureControl (instructionAddWord row 105 106 == pc) "current PC binding"
    ensureControl (instructionAddWord row 107 108 == pc + 1) "next PC binding"
    ensureControl ((row 110).toNat == height && (row 111).toNat + 1 == height)
      "height binding"
    ensureControl (decide (Num.binop 32 0 a b = some (instructionAddWord row 4 5)))
      "arithmetic binding"
    for col in List.range 225 do
      let bad := fun i => if i = col then row i + (1 : Fp) else row i
      ensureControl (!(checkControl bad)) "column mutation accepted"
      mutations := mutations + 1
    for col in List.range' 113 112 do
      let bad := fun i => if i = col then (1 : Fp) - row i else row i
      ensureControl (!(checkControl bad)) "boolean control-bit flip accepted"
      mutations := mutations + 1
    for slot in [2,3,5,6] do
      let col := if slot < 4 then 105 + slot else 106 + slot
      let changed := ((row col).toNat + 1) % 65536
      ensureControl (!(checkControl (replaceControlValue row slot changed)))
        "coherent control forgery accepted"
      coherent := coherent + 1
  for (pc,height) in [(4294967295,2),(4294967296,2),(0,0),(0,1),(0,65536)] do
    ensureControl (!(checkControl (controlTestRow 1 2 pc height))) "invalid control domain accepted"
  IO.println s!"PASS: {inputs.length} honest control rows, {mutations} mutations, {coherent} coherent control forgeries, 5 invalid-domain cases."
