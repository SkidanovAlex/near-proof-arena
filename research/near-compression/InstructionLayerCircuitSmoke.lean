import NearCompression.InstructionLayerCircuit

open NearCompression ZkFormal.Air ZkFormal.Algebra

def ensureLayer (label : String) (b : Bool) : IO Unit :=
  unless b do throw <| IO.userError label

def main : IO Unit := do
  let mut circuits : List InstructionPackedCircuit := []
  for e in instructionAdd32RangeConstraints do
    match instructionLayerCompile e with
    | none => throw <| IO.userError "addition constraint rejected"
    | some c => circuits := circuits ++ [c]
  let cases : List (UInt32 × UInt32) := [(0,0),(1,2),(65535,1),(65536,65536),
    (4294967295,1),(4294967295,4294967295),(2147483648,2147483648),(305419896,2596069104)]
  let mut parity := 0
  let mut rejected := 0
  for (a,b) in cases do
    let row := instructionAdd32RangeWitness a b
    ensureLayer "honest compiled witness" <| circuits.all fun c => decide (instructionPackedEval row c=0)
    for col in List.range 104 do
      let bad := fun i => if i=col then row i+1 else row i
      for (e,c) in instructionAdd32RangeConstraints.zip circuits do
        ensureLayer "compiled/source evaluation mismatch" <|
          decide (instructionPackedEval bad c=e.evalWith (instructionAddEnv bad))
        parity := parity+1
      ensureLayer "mutation accepted" <| !(circuits.all fun c => decide (instructionPackedEval bad c=0))
      rejected := rejected+1
  let unsupported : List Expr := [.col 0 true,.pub 0,.isFirst,.isLast,.isTransition,
    .add (.const 1) (.pub 0),.mul (.col 0 true) (.const 0),.neg .isFirst]
  for e in unsupported do
    ensureLayer "unsupported input not rejected" (instructionLayerCompile e).isNone
  -- Nested multiplication is legal: local gate degree remains two even when
  -- the composed source polynomial has higher degree.
  let cubic : Expr := .mul (.col 0 false) (.mul (.col 1 false) (.col 2 false))
  match instructionLayerCompile cubic with
  | none => throw <| IO.userError "local cubic rejected"
  | some c =>
    ensureLayer "cubic semantics" <| decide (instructionPackedEval (fun i => Fp.ofNat (i+2)) c=24)
    ensureLayer "root gate degree" <| decide (instructionLayerGateDegree c.2≤2)
  IO.println s!"PASS: {circuits.length} constraints; {cases.length} honest rows; {rejected} mutations; {parity} source/circuit comparisons; {unsupported.length} rejected environment inputs; nested cubic."
