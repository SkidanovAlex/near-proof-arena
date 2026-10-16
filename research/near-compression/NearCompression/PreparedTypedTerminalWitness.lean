import NearCompression.PreparedTypedGasContext
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.V2 NearSpecV3.Wasm

/-- An actual typed execution endpoint before and after interpreter gas
synchronization. The AIR snapshot on exhaustion is not the synchronized gas. -/
structure PreparedTypedTerminalWitness (cfg : NearCfg) (p : Prepared) (tr : Trace Fp)
    (pf : PFunc) (count : Nat) (root : Label) where
  row : Nat
  nonlast : row+1<tr.height 0
  before : St
  frame : Frame
  sp : Nat
  state : PreparedTypedState (tr.cell 0 row) before frame [] sp count root
  func : p.funcs[frame.fn]?=some pf
  context : PreparedWasmGasContext before
  active : tr.cell 0 row 41=0
  raw : St
  final : St
  error : Option String
  terminal : step cfg p before=(match error with | none=>.fin raw | some e=>.abort raw e)
  synced : sync raw=.ok final
  done : tr.cell 0 (row+1) 41=1
  failed : tr.cell 0 (row+1) 42=if error.isSome then 1 else 0

def PreparedTypedTerminalWitness.result {cfg p tr pf count root}
    (w : PreparedTypedTerminalWitness cfg p tr pf count root) : Res :=
  match w.error with | none=>.fin w.raw | some e=>.abort w.raw e
end NearCompression
