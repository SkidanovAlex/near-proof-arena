import NearCompression.SHA384DirectRouting
import NearCompression.SHA384DirectPublic

namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2

/-- Every first-row-only send contributes once, independently of trace height.
This is exact natural traffic, not a randomized bus fingerprint. -/
theorem sha384_first_row_traffic (payloads : List (List Expr)) (bus : Nat)
    (tr : Trace Fp) (t r : Nat) (pub : List Fp) (b : Nat) (side : Bool) :
    ZkFormal.Chacha.rowTraffic (payloads.map (fun msg=>⟨bus,[.isFirst],msg,true⟩)) tr t r pub b side=
      if r=0 ∧ bus=b ∧ side=true then payloads.map (fun msg=>msg.map (fun e=>e.eval tr t 0 pub)) else [] := by
  induction payloads with
  | nil => simp [ZkFormal.Chacha.rowTraffic]
  | cons msg rest ih =>
    simp only [List.map_cons,ZkFormal.Chacha.rowTraffic,List.flatMap_cons]
    change (if bus=b ∧ true=side then
      List.replicate (Interaction.multNat ⟨bus,[.isFirst],msg,true⟩ tr t r pub)
        (msg.map (fun e=>e.eval tr t r pub)) else []) ++
      ZkFormal.Chacha.rowTraffic (rest.map (fun msg=>⟨bus,[.isFirst],msg,true⟩)) tr t r pub b side=_
    rw [ih]
    by_cases row:r=0 <;> by_cases busEq:bus=b <;> cases side
    all_goals simp [row,busEq,Interaction.multNat,Interaction.multNat.go,Expr.eval,Expr.evalWith,rowEnv,
      show (0:Fp)≠1 from by decide]

theorem sha384_first_row_count (payloads : List (List Expr)) (bus : Nat)
    (tr : Trace Fp) (t : Nat) (pub : List Fp) (b : Nat) (side : Bool) (message : List Fp) :
    tableBusCount (payloads.map (fun msg=>⟨bus,[.isFirst],msg,true⟩)) tr t pub b side message=
      if bus=b ∧ side=true then
        (payloads.map (fun msg=>msg.map (fun e=>e.eval tr t 0 pub))).count message else 0 := by
  rw [ZkFormal.Chacha.tableBusCount_eq]
  have positive:=Nat.two_pow_pos (tr.log t)
  have shape : tr.height t=(tr.height t-1)+1 := by change 0<tr.height t at positive;omega
  rw [shape,List.range_succ_eq_map,List.flatMap_cons,List.flatMap_map]
  have tail : (List.range (tr.height t-1)).flatMap (fun i=>
      ZkFormal.Chacha.rowTraffic (payloads.map (fun msg=>⟨bus,[.isFirst],msg,true⟩)) tr t (i+1) pub b side)=[] := by
    have empty : ∀ indices:List Nat,indices.flatMap (fun i=>
      ZkFormal.Chacha.rowTraffic (payloads.map (fun msg=>⟨bus,[.isFirst],msg,true⟩)) tr t (i+1) pub b side)=[] := by
      intro indices
      induction indices with
      | nil => rfl
      | cons i rest ih => rw [List.flatMap_cons,sha384_first_row_traffic];simp [ih]
    exact empty _
  change (ZkFormal.Chacha.rowTraffic _ tr t 0 pub b side ++
    (List.range (tr.height t-1)).flatMap (fun i=>ZkFormal.Chacha.rowTraffic _ tr t (i+1) pub b side)).count message=_
  rw [tail,List.append_nil,sha384_first_row_traffic]
  simp only [true_and]
  split <;> rfl

def sha384DirectBlockRecords (n : Nat) (pub : List Fp) (tr : Trace Fp) : List (List Fp) :=
  (List.range (sha384PaddedLength n/128)).map (fun block=>Fp.ofNat block ::
    (List.range 16).flatMap (fun word=>(List.range 4).map (fun limb=>
      (sha384DirectLimb n block word limb).eval tr 2 0 pub)))

theorem sha384_direct_input_count (n : Nat) (fixed : List (Nat × Nat))
    (pub : List Fp) (tr : Trace Fp) (b : Nat) (side : Bool) (message : List Fp) :
    tableBusCount (sha384DirectInputTable n fixed).interactions tr 2 pub b side message=
      if 4=b ∧ side=true then (sha384DirectBlockRecords n pub tr).count message else 0 := by
  let payloads := (List.range (sha384PaddedLength n/128)).map (fun block=>
    Expr.const block :: (List.range 16).flatMap (fun word=>(List.range 4).map (sha384DirectLimb n block word)))
  have shape : (sha384DirectInputTable n fixed).interactions=
      payloads.map (fun msg=>⟨4,[.isFirst],msg,true⟩) := by
    simp only [sha384DirectInputTable,payloads,List.map_map,Function.comp_def]
  rw [shape,sha384_first_row_count]
  have records : payloads.map (fun msg=>msg.map (fun e=>e.eval tr 2 0 pub))=sha384DirectBlockRecords n pub tr := by
    simp only [payloads,sha384DirectBlockRecords,List.map_map,Function.comp_def,List.map_cons,List.map_flatMap]
    rfl
  rw [records]

end NearCompression
