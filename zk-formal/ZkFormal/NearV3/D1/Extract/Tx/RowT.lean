import ZkFormal.NearV3.D1.Extract.Tx.Flags

/-!
# `ZkFormal.NearV3.D1.Extract.Tx.RowT` — the bus traffic of one `txV3` row
-/

namespace ZkFormal.NearV3.D1.TxProof

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.D1
  ZkFormal.NearV3.D1.TxV3

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}

theorem multNat1 (x : Nat) (q : Nat) :
    Interaction.multNat.go tr tt q pub [c x] 0 = if tr.cell tt q x = 1 then 1 else 0 := by
  simp only [Interaction.multNat.go, eval_c]
  by_cases h : tr.cell tt q x = 1 <;> simp [h]

/-- The traffic of row `q`, interaction by interaction. -/
theorem rowT (q bb : Nat) (sd : Bool) :
    rowTraffic TxV3.interactions tr tt q pub bb sd =
      (if bb = B_TXP ∧ sd = false ∧ tr.cell tt q act = 1 then
        [[tr.cell tt q g, tr.cell tt q kind, tr.cell tt q strict, tr.cell tt q okP, tr.cell tt q tov,
          tr.cell tt q stage, tr.cell tt q cok, tr.cell tt q xN, tr.cell tt q xB, tr.cell tt q xC]] else []) ++
      (if bb = B_SIG ∧ sd = false ∧ tr.cell tt q lf = 1 then [[tr.cell tt q op, tr.cell tt q valid]] else []) ++
      (if bb = B_FINAL ∧ sd = false ∧ tr.cell tt q fW = 1 then
        [[((W_TX : Nat) : Fp) + ((2 : Nat) : Fp) * tr.cell tt q op, ((0 : Nat) : Fp),
          1 - tr.cell tt q s1, tr.cell tt q vidA]] else []) ++
      (if bb = B_FINAL ∧ sd = false ∧ tr.cell tt q fK = 1 then
        [[((W_TX : Nat) : Fp) + (((2 : Nat) : Fp) * tr.cell tt q op + (((1 : Nat) : Fp) + 0)),
          ((0 : Nat) : Fp), 1 - tr.cell tt q s2, tr.cell tt q vidK]] else []) ++
      (if bb = B_MEM ∧ sd = false ∧ tr.cell tt q s1 = 1 then
        [[tr.cell tt q vidA, tr.cell tt q tpA, tr.cell tt q lane, tr.cell tt q amt, tr.cell tt q lk,
          tr.cell tt q st]] else []) ++
      (if bb = B_MEM ∧ sd = true ∧ tr.cell tt q s1 = 1 then
        [[tr.cell tt q vidA, tr.cell tt q op + ((1 : Nat) : Fp), tr.cell tt q lane, tr.cell tt q mo,
          tr.cell tt q lk, tr.cell tt q st]] else []) ++
      (if bb = B_AKMEM ∧ sd = false ∧ tr.cell tt q gA = 1 then
        [[tr.cell tt q vidK, tr.cell tt q tpK, tr.cell tt q lane, tr.cell tt q kn, tr.cell tt q fa]] else []) ++
      (if bb = B_AKMEM ∧ sd = true ∧ tr.cell tt q gA = 1 then
        [[tr.cell tt q vidK, tr.cell tt q op + ((1 : Nat) : Fp), tr.cell tt q lane, tr.cell tt q nk,
          tr.cell tt q fa]] else []) := by
  simp only [rowTraffic, TxV3.interactions, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    Dsl.recv, Dsl.send, Interaction.multNat, multNat1, Interaction.msgVal, List.map_cons,
    List.map_nil, eval_c, eval_k, eval_add, eval_smul, eval_not, eval_sum_cons, eval_sum_nil, wA, wK, tE,
    List.append_assoc]
  have ap : ∀ {a b c d : List (List Fp)}, a = b → c = d → a ++ c = b ++ d := by
    intro a b c d h1 h2; rw [h1, h2]
  refine ap ?_ (ap ?_ (ap ?_ (ap ?_ (ap ?_ (ap ?_ (ap ?_ ?_)))))) <;>
    (split <;> split <;> simp_all [eq_comm]) <;> first | rfl | grind

end ZkFormal.NearV3.D1.TxProof
