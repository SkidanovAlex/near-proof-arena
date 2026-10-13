import ZkFormal.NearV3.Render.Ups.CompactCells

/-! Declarations of `ZkFormal.NearV3.Candidates.CompactHeight` split out (unchanged names and statements) so that
  importers needing only these do not pull in the rest of the module (certificate pruning). -/
namespace ZkFormal.NearV3.Candidates.CompactHeight
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Render
open ZkFormal.NearV3 ZkFormal.NearV3.Render ZkFormal.NearV3.Render.UpsRelay
open ZkFormal.Near.Dsl ZkFormal.NearV3.UpsRows ZkFormal.NearV3.UpsV3


def trace (insts : List UpsInst) : Trace Fp :=
  ⟨fun _=>22,fun _ r c=>(compactCell insts r c : Fp)⟩

end ZkFormal.NearV3.Candidates.CompactHeight
