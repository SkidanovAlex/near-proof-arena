import NearCompression.GenericPaddingLocal
import ZkFormal.NearV3.Candidates.MerkleRender.Honest
import ZkFormal.NearV3.Render.PaddedCongr

/-! Shorten the actual nonempty Merkle renderer's constant suffix. Its
inverse-count padding column is retained. Traffic and Rust refinement remain
separate obligations. The local theorem uses existing honest completeness. -/
set_option autoImplicit false
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Render
open ZkFormal.NearV3.Candidates ZkFormal.NearV3.Candidates.MerkleRender

noncomputable def merklePad (n : Nat) (lv : List (List MNode)) (pub : List Fp) : Nat → Fp :=
  fun c => if c = MerkleEmpty.inverseCol then
    (MerkleEmpty.countE.eval (trace n lv) T_MRK 0 pub)⁻¹ else 0
noncomputable def merklePrefix (n : Nat) (lv : List (List MNode)) (pub : List Fp) : Nat → Nat → Fp :=
  (MerkleEmpty.liftTrace (trace n lv) T_MRK pub).cell T_MRK
noncomputable def merkleTraceAtLog (n : Nat) (lv : List (List MNode)) (pub : List Fp)
    (logSize : Nat) : Trace Fp :=
  genericPaddingTrace (merklePrefix n lv pub) ((MrkGen.recs n).length+1)
    (merklePad n lv pub) logSize

theorem merkle_old_cells (n : Nat) (lv : List (List MNode)) (pub : List Fp) (r c : Nat) :
    (MerkleEmpty.liftTrace (trace n lv) T_MRK pub).cell T_MRK r c =
      (merkleTraceAtLog n lv pub 19).cell T_MRK r c := by
  by_cases hr : r < (MrkGen.recs n).length+1
  · simp only [merkleTraceAtLog,genericPaddingTrace,genericPaddingRow,ite_eq_left hr,merklePrefix]
  · have r0 : r≠0 := by omega
    have rr : ¬r-1<(MrkGen.recs n).length := by omega
    simp only [merkleTraceAtLog,genericPaddingTrace,genericPaddingRow,ite_eq_right hr,
      merklePad,MerkleEmpty.liftTrace,ite_true,MerkleEmpty.emptyCol,MerkleEmpty.inverseCol]
    by_cases c58 : c=58 <;> by_cases c59 : c=59 <;>
      simp [c58,c59,trace,MrkGen.cell,r0,rr] <;> rfl

theorem padding_expr_property_shrink (e : Expr) (Q : Fp → Prop)
    (prefixRows : Nat → Nat → Fp) (length : Nat) (pad : Nat → Fp)
    (pub : List Fp) (oldLog newLog t : Nat)
    (padding : length<2^newLog) (shrink : 2^newLog≤2^oldLog) (heightBound : 2≤2^newLog)
    (oldHolds : ∀ r,r<2^oldLog → Q (e.eval (genericPaddingTrace prefixRows length pad oldLog) t r pub))
    (r : Nat) (hr : r<2^newLog) :
    Q (e.eval (genericPaddingTrace prefixRows length pad newLog) t r pub) := by
  rw [Expr.eval,generic_padding_row_env]
  apply generic_padding_shrink_local (fun a b first last transition =>
    Q (e.evalWith (genericPaddingEnv a b pub first last transition)))
    prefixRows length (2^newLog) (2^oldLog) pad padding shrink heightBound _ r hr
  intro oldRow bound
  have h := oldHolds oldRow bound
  rw [Expr.eval,generic_padding_row_env] at h
  exact h

/-- Both local constraints and natural-multiplicity bit legality, using only
capacity and existing honest count hypotheses; no new-validity premise. -/
theorem merkle_shrink_local (n : Nat) (lv : List (List MNode)) (pub : List Fp)
    (hn1 : 1≤n) (hn : n≤4481)
    (hp : ∀ i<4,pub.getD (ZkFormal.NearV3.PH_N+i) 0=Fp.ofNat (n/256^i%256))
    (newLog : Nat) (hlog1 : 1≤newLog) (hlog19 : newLog≤19)
    (padding : (MrkGen.recs n).length+1<2^newLog) :
    TableLocal MerkleEmpty.table (merkleTraceAtLog n lv pub newLog) T_MRK pub := by
  have old := honest_local n lv pub hn hp (fun h => by omega)
  rw [MerkleRender.honestTrace,ite_eq_right (show n≠0 by omega)] at old
  have oldG : TableLocal MerkleEmpty.table (merkleTraceAtLog n lv pub 19) T_MRK pub :=
    ZkFormal.NearV3.Render.tableLocal_congr_rows
      (tr₁ := MerkleEmpty.liftTrace (trace n lv) T_MRK pub)
      (tr₂ := merkleTraceAtLog n lv pub 19) rfl
      (fun r _ c => merkle_old_cells n lv pub r c) old
  have shrink : 2^newLog≤2^19 := Nat.pow_le_pow_right (by decide) hlog19
  have heightBound : 2≤2^newLog := by
    simpa using (Nat.pow_le_pow_right (show 0<2 by decide) hlog1)
  refine ⟨hlog1,?_,?_,?_⟩
  · exact Nat.le_trans hlog19 oldG.log_le
  · intro r hr e he
    exact padding_expr_property_shrink e (fun x => x=0) _ _ _ pub 19 newLog T_MRK
      padding shrink heightBound (fun q hq => oldG.constr q hq e he) r hr
  · intro r hr i hi b hb
    exact padding_expr_property_shrink b (fun x => x=0 ∨ x=1) _ _ _ pub 19 newLog T_MRK
      padding shrink heightBound (fun q hq => oldG.bits q hq i hi b hb) r hr
end NearCompression
