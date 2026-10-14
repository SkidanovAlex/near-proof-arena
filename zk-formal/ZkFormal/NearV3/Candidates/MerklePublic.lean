import ZkFormal.Near.Tables.Mrk
import ZkFormal.NearV3.Rcpt.Ids
import ZkFormal.Size.Model
import ZkFormal.NearV3.Candidates.MerklePublicDefs

namespace ZkFormal.NearV3.Candidates.MerklePublic
open ZkFormal.Air ZkFormal.Near

/-- Evaluation commutes with the public-field translation, over any carrier.
This identifies exactly the v1 public environment seen by existing Merkle proofs. -/
theorem expression_eval {R : Type} (env : Env R) (e : Expr) :
    (expression e).evalWith env=e.evalWith {env with pub:=fun i => env.pub (publicIndex i)} := by
  induction e <;> simp_all [expression,Expr.evalWith]

theorem count_index (i : Fin 4) : publicIndex (PV_N+i.val)=PH_N+i.val := by
  have hi := i.isLt
  simp [publicIndex,PV_N,PH_N,PV_OUT,PH_OUT,show 149+i.val<153 by omega]

theorem root_index (i : Fin 32) : publicIndex (PV_OUT+i.val)=PH_OUT+i.val := by
  have hi := i.isLt
  simp [publicIndex,PV_N,PH_N,PV_OUT,PH_OUT,show ¬217+i.val<153 by omega,
    show 217+i.val<249 by omega]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem table_wf : table.wf ⟨[table],67,202⟩ 8=true := by decide +kernel

set_option maxRecDepth 32768 in
theorem shape : ZkFormal.Size.shapeOf 2 table=⟨58,3,5,3,19⟩ := by decide +kernel

/-- Bus identities/directions are preserved, while payload public bytes are
translated by the proved environment map. -/
theorem bus_signature : table.interactions.map (fun i => (i.bus,i.send))=
    Mrk.interactions.map (fun i => (i.bus,i.send)) := by
  simp [table,interaction,List.map_map]

end ZkFormal.NearV3.Candidates.MerklePublic
