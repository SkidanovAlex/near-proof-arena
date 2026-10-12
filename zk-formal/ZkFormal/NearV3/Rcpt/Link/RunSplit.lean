import ZkFormal.NearV3.Assembly.Forward

/-!
# ZkFormal.NearV3.Rcpt.Link.RunSplit — `applyReceipts` = ledger run + compute guard + forwarding

`NearSpecV3.applyReceipts` interleaves three independent checks per receipt: the compute guard
`i·G < gas_limit` (class H, native in `prepBody`), the per-receipt ledger
(`applySystemReceipt` / v1 `applyReceipt`, class W, the AIR), and the forwarding of the freshly
generated refunds (`tryForward`, class H, native over the hint body).  Soundness assembles them
the other way round:

* `ledgerStep` / `ledgerAll` — the ledger alone (no compute guard, no forwarding);
* `ledgerAll_refunds` — the ledger only appends refunds;
* **`applyReceipts_of_ledger`** — a successful ledger run, the compute guard for every index,
  and a successful forwarding run (`Assembly.forwardRun`) over all the refunds it generated give
  `applyReceipts ctx i (acc, ls) rs = .ok (acc', ls')`.
-/

namespace ZkFormal.NearV3.RcptLink

open NearSpec NearSpec.TransferV1 NearSpecV3 ZkFormal.NearV3.Assembly

/-- One receipt of `applyReceipts` without the compute guard and without forwarding. -/
def ledgerStep (ctx : ApplyCtx) (acc : Acc) (r : Receipt) : Option Acc :=
  if r.predecessorId == AccountId.system then
    match applySystemReceipt acc r with
    | .ok a => some a
    | .error _ => none
  else applyReceipt ⟨ctx.height, ctx.gasPrice⟩ acc r

/-- The ledger over a receipt list. -/
def ledgerAll (ctx : ApplyCtx) : Acc → List Receipt → Option Acc
  | acc, [] => some acc
  | acc, r :: rs =>
    match ledgerStep ctx acc r with
    | none => none
    | some acc' => ledgerAll ctx acc' rs

theorem applyReceipt_refunds {c : Ctx} {st st' : Acc} {r : Receipt}
    (h : applyReceipt c st r = some st') : ∃ added, st'.refunds = st.refunds ++ added := by
  unfold applyReceipt at h
  repeat' (first | (cases h; done) | (split at h) | (dsimp only at h))
  all_goals (cases h; exact ⟨_, rfl⟩)

theorem ledgerStep_refunds {ctx : ApplyCtx} {acc acc' : Acc} {r : Receipt}
    (h : ledgerStep ctx acc r = some acc') : ∃ added, acc'.refunds = acc.refunds ++ added := by
  unfold ledgerStep at h
  split at h
  · split at h
    · rename_i a ha
      cases h
      exact ⟨[], by rw [ZkFormal.V3.applySystemReceipt_refunds ha, List.append_nil]⟩
    · cases h
  · exact applyReceipt_refunds h

theorem ledgerAll_refunds (ctx : ApplyCtx) :
    ∀ (rs : List Receipt) (acc acc' : Acc), ledgerAll ctx acc rs = some acc' →
      ∃ added, acc'.refunds = acc.refunds ++ added
  | [], acc, acc', h => by cases h; exact ⟨[], by simp⟩
  | r :: rs, acc, acc', h => by
    simp only [ledgerAll] at h
    split at h
    · cases h
    · rename_i a1 h1
      obtain ⟨x, hx⟩ := ledgerStep_refunds h1
      obtain ⟨y, hy⟩ := ledgerAll_refunds ctx rs a1 acc' h
      exact ⟨x ++ y, by rw [hy, hx, List.append_assoc]⟩

theorem forwardRun_append_ok {ctx : ApplyCtx} {ls ls' : List Limit} {xs ys : List Receipt}
    (h : forwardRun ctx ls (xs ++ ys) = .ok ls') :
    ∃ ls1, forwardRun ctx ls xs = .ok ls1 ∧ forwardRun ctx ls1 ys = .ok ls' := by
  rw [forwardRun_append] at h
  cases h1 : forwardRun ctx ls xs with
  | error e => rw [h1] at h; cases h
  | ok ls1 => rw [h1] at h; exact ⟨ls1, rfl, h⟩

/-- **`applyReceipts` from its three parts.**  The compute guard is the native one of
`prepBody` (`n = 0 ∨ (n − 1)·G < gas_limit`), shifted to the start index `i`. -/
theorem applyReceipts_of_ledger (ctx : ApplyCtx) :
    ∀ (rs : List Receipt) (i : Nat) (acc acc' : Acc) (ls ls' : List Limit),
      ledgerAll ctx acc rs = some acc' →
      (rs = [] ∨ (i + rs.length - 1) * Params.G < ctx.gasLimit) →
      forwardRun ctx ls (acc'.refunds.drop acc.refunds.length) = .ok ls' →
      applyReceipts ctx i (acc, ls) rs = .ok (acc', ls')
  | [], i, acc, acc', ls, ls', hl, _, hf => by
    simp only [ledgerAll, Option.some.injEq] at hl
    subst hl
    simp only [List.drop_length] at hf
    cases hf
    rfl
  | r :: rs, i, acc, acc', ls, ls', hl, hc, hf => by
    have hc' : (i + rs.length) * Params.G < ctx.gasLimit := by
      rcases hc with h | h
      · cases h
      · simpa only [List.length_cons, Nat.add_succ_sub_one] using h
    have hi : ¬ (i * Params.G ≥ ctx.gasLimit) := by
      have : i * Params.G ≤ (i + rs.length) * Params.G := Nat.mul_le_mul_right _ (Nat.le_add_right _ _)
      omega
    have hct : rs = [] ∨ (i + 1 + rs.length - 1) * Params.G < ctx.gasLimit := by
      cases rs with
      | nil => exact Or.inl rfl
      | cons _ t =>
        right
        have e : i + 1 + (t.length + 1) - 1 = i + (t.length + 1) := by omega
        simp only [List.length_cons] at hc' ⊢
        rw [e]; exact hc'
    simp only [ledgerAll] at hl
    split at hl
    · cases hl
    rename_i a1 h1
    obtain ⟨y, hy⟩ := ledgerAll_refunds ctx rs a1 acc' hl
    simp only [applyReceipts, hi, ↓reduceIte]
    unfold ledgerStep at h1
    split at h1
    · rename_i hsys
      cases ha : applySystemReceipt acc r with
      | error e => simp only [ha] at h1; cases h1
      | ok a =>
        simp only [ha, Option.some.injEq] at h1
        subst h1
        simp only [hsys, ↓reduceIte, bind, Except.bind]
        refine applyReceipts_of_ledger ctx rs (i + 1) a acc' ls ls' hl hct ?_
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
      refine applyReceipts_of_ledger ctx rs (i + 1) a1 acc' v ls' hl hct ?_
      rw [hy, List.drop_left]
      exact hf2

end ZkFormal.NearV3.RcptLink
