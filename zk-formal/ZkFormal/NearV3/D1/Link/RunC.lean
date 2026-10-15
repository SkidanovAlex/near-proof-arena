import ZkFormal.NearV3.Rcpt.Link.RunModel
import NearSpecV3.RuntimeD1

/-!
# `ZkFormal.NearV3.D1.Link.RunC` — the receipt ledger after the transactions (L1, the run)

Lane `v3-d1-phase2`, item L1 (next step 2 of checkpoint 11, "the run").  In D1,
`applyNewChunkD1` applies the local receipts and then the incoming ones with
`applyReceiptsC`, starting from the accumulator the transactions leave
(`⟨st.trie, [], [], st.gas, st.tokens⟩`, compute `st.gas`), not from D0a's `⟨mid, [], [], 0, 0⟩`
at index `0`.  This module is the spec-level part, record-free:

* `applyReceiptsC_of_ledger`: D0a's `applyReceipts_of_ledger` for `applyReceiptsC` (the compute
  guard on the running compute `comp + i·G`; the result carries the final compute);
* `applyReceiptsC_append`: the two `applyReceiptsC` calls of `applyNewChunkD1` are one run over
  `locals ++ incoming`;
* `RunModelC`: D0a's `RunModel` with an initial accumulator (`outs0`, `rf0`, `gas0`, `tok0`);
  `accAtC`, `RcptOkC` (D0a's `RcptOk3` with the token bound shifted by `tok0`), **`stepC`** and
  **`ledgerAllC_eq`**: `ledgerAll ctx (accAtC 0) rs = some (accAtC |rs|)`.
-/

namespace ZkFormal.NearV3.D1.Link

open NearSpec NearSpec.TransferV1 NearSpecV3 ZkFormal.NearV3.RcptLink ZkFormal.NearV3.Assembly ZkFormal.Near

/-! ## `applyReceiptsC` from its parts -/

/-- **`applyReceiptsC` from its three parts** (D0a's `applyReceipts_of_ledger` with the running
compute): a ledger run, the compute guard `comp + (|rs| − 1)·G < gas_limit` and the forwarding
of the generated refunds. -/
theorem applyReceiptsC_of_ledger (ctx : ApplyCtx) :
    ∀ (rs : List Receipt) (comp : Nat) (acc acc' : Acc) (ls ls' : List Limit),
      ledgerAll ctx acc rs = some acc' →
      (rs = [] ∨ comp + (rs.length - 1) * Params.G < ctx.gasLimit) →
      forwardRun ctx ls (acc'.refunds.drop acc.refunds.length) = .ok ls' →
      applyReceiptsC ctx comp (acc, ls) rs = .ok (acc', ls', comp + rs.length * Params.G)
  | [], comp, acc, acc', ls, ls', hl, _, hf => by
    simp only [ledgerAll, Option.some.injEq] at hl
    subst hl
    simp only [List.drop_length] at hf
    cases hf
    simp [applyReceiptsC]
  | r :: rs, comp, acc, acc', ls, ls', hl, hc, hf => by
    have hc' : comp + rs.length * Params.G < ctx.gasLimit := by
      rcases hc with h | h
      · cases h
      · simpa only [List.length_cons, Nat.add_sub_cancel] using h
    have hi : ¬ (comp ≥ ctx.gasLimit) := by omega
    have hct : rs = [] ∨ comp + Params.G + (rs.length - 1) * Params.G < ctx.gasLimit := by
      cases rs with
      | nil => exact Or.inl rfl
      | cons _ t =>
        right
        simp only [List.length_cons, Nat.add_sub_cancel] at hc' ⊢
        rw [Nat.add_mul, Nat.one_mul] at hc'
        omega
    have hfin : comp + Params.G + rs.length * Params.G = comp + (r :: rs).length * Params.G := by
      simp only [List.length_cons, Nat.add_mul, Nat.one_mul]; omega
    simp only [ledgerAll] at hl
    split at hl
    · cases hl
    rename_i a1 h1
    obtain ⟨y, hy⟩ := ledgerAll_refunds ctx rs a1 acc' hl
    simp only [applyReceiptsC, hi, ↓reduceIte]
    unfold ledgerStep at h1
    split at h1
    · rename_i hsys
      cases ha : applySystemReceipt acc r with
      | error e => simp only [ha] at h1; cases h1
      | ok a =>
        simp only [ha, Option.some.injEq] at h1
        subst h1
        simp only [hsys, ↓reduceIte, bind, Except.bind]
        rw [← hfin]
        refine applyReceiptsC_of_ledger ctx rs (comp + Params.G) a acc' ls ls' hl hct ?_
        rw [ZkFormal.V3.applySystemReceipt_refunds ha]
        exact hf
    · rename_i hsys
      obtain ⟨x, hx⟩ := applyReceipt_refunds h1
      have hsys' : (r.predecessorId == AccountId.system) = false := by simpa using hsys
      simp only [hsys', Bool.false_eq_true, ↓reduceIte, h1]
      rw [hy, hx, List.append_assoc, List.drop_left] at hf
      obtain ⟨ls1, hf1, hf2⟩ := forwardRun_append_ok hf
      have hn : (a1.refunds.drop acc.refunds.length).foldlM (fun ls rf =>
          match tryForward ctx ls rf with
          | some ls' => Except.ok ls'
          | none => Except.error "out of domain (e.forwarded): generated receipt buffered") ls =
          Except.ok ls1 := by
        rw [hx, List.drop_left]; exact hf1
      simp only [bind, Except.bind]
      split
      · rename_i err heq
        exact absurd (heq.symm.trans hn) (by simp)
      rename_i v heq
      obtain rfl : v = ls1 := by simpa using heq.symm.trans hn
      rw [← hfin]
      refine applyReceiptsC_of_ledger ctx rs (comp + Params.G) a1 acc' v ls' hl hct ?_
      rw [hy, List.drop_left]
      exact hf2

/-- The two `applyReceiptsC` runs of `applyNewChunkD1` (local, then incoming receipts) are one
run over the concatenation. -/
theorem applyReceiptsC_append (ctx : ApplyCtx) (ys : List Receipt) :
    ∀ (xs : List Receipt) (comp : Nat) (acc : Acc) (ls : List Limit),
      applyReceiptsC ctx comp (acc, ls) (xs ++ ys) =
        (applyReceiptsC ctx comp (acc, ls) xs >>= fun x => applyReceiptsC ctx x.2.2 (x.1, x.2.1) ys)
  | [], comp, acc, ls => by
    simp [applyReceiptsC, bind, Except.bind]
  | r :: xs, comp, acc, ls => by
    simp only [List.cons_append, applyReceiptsC]
    split
    · rfl
    split
    · cases applySystemReceipt acc r with
      | error e => rfl
      | ok a => exact applyReceiptsC_append ctx ys xs _ _ _
    · split
      · split <;> rfl
      · simp only [bind, Except.bind]
        split
        · rfl
        · exact applyReceiptsC_append ctx ys xs _ _ _

/-! ## The ledger from an initial accumulator -/

/-- D0a's `RunModel` with an initial accumulator: the receipts start after `outs0` / `rf0`,
with `gas0` gas and `tok0` tokens burnt (the transactions'). -/
structure RunModelC extends RunModel where
  outs0 : List Outcome
  rf0 : List Receipt
  gas0 : Nat
  tok0 : Nat

namespace RunModelC

variable (M : RunModelC) (ctx : ApplyCtx)

/-- The accumulator before receipt `r`. -/
def accAtC (r : Nat) : Acc :=
  ⟨M.T (M.valsAt r), M.outs0 ++ (List.range r).map (M.outcomeOf ctx),
   M.rf0 ++ (List.range r).flatMap (M.refundOf ctx), M.gas0 + r * Params.G, M.tok0 + M.tokAt ctx r⟩

/-- Per-receipt arithmetic (D0a's `RcptOk3`, the token bound shifted by `tok0`). -/
structure RcptOkC (r : Nat) : Prop where
  dec : ∃ raw, Account.decode raw = some (M.acc0 (M.slot r))
  amt_lt : M.amtAt (M.slot r) r + (M.rc r).deposit < Params.u128Max
  tot_lt : M.amtAt (M.slot r) r + (M.rc r).deposit + (M.acc0 (M.slot r)).locked < Params.two128
  stake : Params.storageAmountPerByte * (M.acc0 (M.slot r)).storageUsage ≤
            M.amtAt (M.slot r) r + (M.rc r).deposit + (M.acc0 (M.slot r)).locked ∨
          (M.acc0 (M.slot r)).storageUsage ≤ Params.zeroBalanceStorageLimit
  burnt_lt : M.isSys r = false → burntOf ctx.gasPrice (M.rc r) < Params.two128
  surplus_lt : M.isSys r = false → surplusOf ctx.gasPrice (M.rc r) < Params.two128
  tok_lt : M.isSys r = false → M.tok0 + M.tokAt ctx r + burntOf ctx.gasPrice (M.rc r) < Params.two128

theorem dec_valsAtC {r : Nat} (hr : r < M.rs.length) (hok : M.RcptOkC ctx r) :
    Account.decode (M.valsAt r (M.slot r)) =
      some { M.acc0 (M.slot r) with amount := M.amtAt (M.slot r) r } := by
  simp only [RunModel.valsAt, M.written_slot hr, ↓reduceIte]
  obtain ⟨raw, hA⟩ := hok.dec
  obtain ⟨_, hl, hch, hsu, _⟩ := ZkFormal.Near.Sound.decode_wf hA
  exact ZkFormal.Near.Sound.decode_encode _ (by have := hok.amt_lt; simp only; omega) hl hch hsu

theorem accAtC_succ (r : Nat) : M.accAtC ctx (r + 1) =
    ⟨M.T (M.valsAt (r + 1)), (M.outs0 ++ (List.range r).map (M.outcomeOf ctx)) ++ [M.outcomeOf ctx r],
     (M.rf0 ++ (List.range r).flatMap (M.refundOf ctx)) ++ M.refundOf ctx r,
     (M.gas0 + r * Params.G) + Params.G, (M.tok0 + M.tokAt ctx r) + M.burnt ctx r⟩ := by
  simp only [accAtC, List.range_succ, List.map_append, List.map_cons, List.map_nil,
    List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, Nat.succ_mul,
    RunModel.tokAt, List.append_assoc, Nat.add_assoc]

/-- **One receipt** (D0a's `RunModel.step` from the shifted accumulator). -/
theorem stepC (hT : M.TrieOk) {r : Nat} (hr : r < M.rs.length) (hok : M.RcptOkC ctx r) :
    ledgerStep ctx (M.accAtC ctx r) (M.rc r) = some (M.accAtC ctx (r + 1)) := by
  have hdec := M.dec_valsAtC ctx hr hok
  have h1 := hok.amt_lt
  have h2 := hok.tot_lt
  have h3 := hok.stake
  have hs : (decide (M.amtAt (M.slot r) r + (M.rc r).deposit + (M.acc0 (M.slot r)).locked ≥
      Params.storageAmountPerByte * (M.acc0 (M.slot r)).storageUsage) ||
      decide ((M.acc0 (M.slot r)).storageUsage ≤ Params.zeroBalanceStorageLimit)) = true := by
    rcases h3 with h3 | h3 <;> simp [h3]
  have hset := hT.set r hr (M.valsAt r) (M.valsAt_lenPres r)
    (Account.encode { M.acc0 (M.slot r) with amount := M.amtAt (M.slot r) r + (M.rc r).deposit })
    (by simp [RunModel.valsAt, M.written_slot hr, Account.encode, u128, u64, leN_length])
  rw [← RunModel.valsAt_succ _ hr] at hset
  rw [accAtC_succ]
  unfold ledgerStep
  by_cases hsys : M.isSys r = true
  · have hsys' : ((M.rc r).predecessorId == AccountId.system) = true := hsys
    have hb : M.burnt ctx r = 0 := by simp [RunModel.burnt, hsys]
    have hrf : M.refundOf ctx r = [] := by simp [RunModel.refundOf, hsys]
    simp only [hsys', ↓reduceIte, hb, hrf, Nat.add_zero, List.append_nil]
    have hout : M.outcomeOf ctx r = (⟨(M.rc r).receiptId, [], Params.G, 0, (M.rc r).receiverId⟩ : Outcome) := by
      simp [RunModel.outcomeOf, hrf, hb]
    rw [hout]
    dsimp only at hset hdec
    have hfind := hT.find r hr (M.valsAt r) (M.valsAt_lenPres r)
    unfold applySystemReceipt
    by_cases he : (M.rc r).signerId = (M.rc r).receiverId
    · obtain ⟨o, ho, hoo⟩ := hT.ak r hr hsys he
      rcases hoo with rfl | ⟨ak, rfl, hl9, h81⟩
      · simp [accAtC, hfind, hdec, Nat.not_le.mpr h1, Nat.not_le.mpr h2, hs, he, ho, hset, bind,
          Except.bind, pure, Except.pure]
      · have h8 : ak[8]'(by omega) = 1 := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)] at h81
          simpa using h81
        simp [accAtC, hfind, hdec, Nat.not_le.mpr h1, Nat.not_le.mpr h2, hs, he, ho, hset, bind,
          Except.bind, pure, Except.pure, hl9, h8]
    · simp [accAtC, hfind, hdec, Nat.not_le.mpr h1, Nat.not_le.mpr h2, hs, he, hset, bind,
        Except.bind, pure, Except.pure]
  · have hns : M.isSys r = false := by simpa using hsys
    have hsys' : ((M.rc r).predecessorId == AccountId.system) = false := hns
    have h4 := hok.burnt_lt hns
    have h5 := hok.surplus_lt hns
    have h6 := hok.tok_lt hns
    have hb : M.burnt ctx r = burntOf ctx.gasPrice (M.rc r) := by simp [RunModel.burnt, hns]
    simp only [hsys', Bool.false_eq_true, ↓reduceIte, hb]
    dsimp only at hset hdec
    have hget := hT.get r hr (M.valsAt r) (M.valsAt_lenPres r)
    simp only [burntOf, surplusOf, burnPrice] at h4 h5 h6
    simp only [applyReceipt, accAtC, hget, hdec]
    simp only [Nat.not_le.mpr h1, Nat.not_le.mpr h2, ↓reduceIte]
    simp only [hs, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Nat.not_le.mpr h6]
    rw [hset]
    split
    · rename_i hc
      exact absurd hc (by
        simp only [Bool.or_eq_true, not_or]; exact ⟨by simpa using h4, by simpa using h5⟩)
    simp only [Option.some.injEq]
    simp [RunModel.outcomeOf, RunModel.refundOf, hns, burntOf, surplusOf, burnPrice, hb]
    by_cases hz : Params.G * ((M.rc r).gasPrice - min (M.rc r).gasPrice ctx.gasPrice) = 0 <;>
      simp [hz]

/-- **The ledger run** from `accAtC r` over the remaining receipts. -/
theorem ledgerAllC_from (hT : M.TrieOk) (hok : ∀ r, r < M.rs.length → M.RcptOkC ctx r) :
    ∀ m r, r + m = M.rs.length →
      ledgerAll ctx (M.accAtC ctx r) (M.rs.drop r) = some (M.accAtC ctx M.rs.length)
  | 0, r, h => by
    simp only [Nat.add_zero] at h; subst h; simp [ledgerAll]
  | m + 1, r, h => by
    have hr : r < M.rs.length := by omega
    rw [List.drop_eq_getElem_cons hr, ← M.rc_getElem hr]
    simp only [ledgerAll, M.stepC ctx hT hr (hok r hr)]
    exact ledgerAllC_from hT hok m (r + 1) (by omega)

/-- **The ledger run of all receipts** from the initial accumulator. -/
theorem ledgerAllC_eq (hT : M.TrieOk) (hok : ∀ r, r < M.rs.length → M.RcptOkC ctx r) :
    ledgerAll ctx (M.accAtC ctx 0) M.rs = some (M.accAtC ctx M.rs.length) := by
  simpa using M.ledgerAllC_from ctx hT hok M.rs.length 0 (by omega)

theorem accAtC_zero : M.accAtC ctx 0 = ⟨M.T (M.valsAt 0), M.outs0, M.rf0, M.gas0, M.tok0⟩ := by
  simp [accAtC, RunModel.tokAt]

end RunModelC

end ZkFormal.NearV3.D1.Link
