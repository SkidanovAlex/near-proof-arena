import ZkFormal.NearV3.D1.PrepD1Lemmas

/-!
# `ZkFormal.NearV3.D1.Prep.TxNative` — `PrepTxNativeStmt`

Lane `v3-d1-phase2` (milestone P1).  With honest verdict bytes (`stage | ok << 2`: `0` no state
read / signer absent, `1` access key absent, `2` verdict failure, `6` success), the native
`prepTxs` reproduces `processTxs`'s outcome leaves, local and forwarded receipts, gas and
tokens.  Proof: a step simulation `Sim` (`prepTx_step`) and an induction (`prepTxs_sim`).
-/

namespace ZkFormal.NearV3.D1

open NearSpec NearSpec.TransferV1 NearSpecV3

/-- The native accumulator tracks the spec state. -/
structure Sim (acc : TxAcc) (st : TxSt) : Prop where
  seen : acc.seen = st.seen
  leaves : acc.leaves = st.outs.map OutD1.leaf
  locals : acc.locals = st.locals
  fwd : acc.fwd = st.fwd
  gas : acc.gas = st.gas
  tokens : acc.tokens = st.tokens

/-- A transaction past step 2 that fails (verdict byte `b ∈ {0, 1, 2}`, `0` unless it is a
candidate): `prepTx` records the failed outcome. -/
theorem prepTx_fail (ctx : ApplyCtx) (acc : TxAcc) (t : Tx) (b : UInt8) (rest : Bytes)
    (hseen : ¬ acc.seen.contains t.hash = true) (hb : b.toNat ≤ 2)
    (hc : (t.valid && (txCost t ctx.gasPrice).isSome) = true ∨ b.toNat = 0) :
    ∃ acc', prepTx ctx { acc with bits := b :: rest } t true = .ok acc' ∧ acc'.bits = rest ∧
      acc'.seen = t.hash :: acc.seen ∧ acc'.leaves = acc.leaves ++ [(failedOutcome t).leaf] ∧
      acc'.locals = acc.locals ∧ acc'.fwd = acc.fwd ∧ acc'.gas = acc.gas ∧ acc'.tokens = acc.tokens := by
  unfold prepTx
  simp only [hseen, Bool.false_eq_true, ite_false, Bool.not_true]
  have h4 : b.toNat / 4 = 0 := by omega
  have h8 : b.toNat % 4 = b.toNat := by omega
  simp only [bind, Except.bind, pure, Except.pure, check, h4, h8, hb, show b.toNat < 8 by omega,
    decide_true, Bool.and_self, ite_true]
  have hc' : (t.valid && (txCost t ctx.gasPrice).isSome || b.toNat == 0) = true := by
    rcases hc with hc | hc <;> simp [hc]
  simp only [hc', ite_true, beq_self_eq_true, Bool.true_or]
  split
  · rename_i hm; exact absurd hm (by simp)
  · exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The receipt of a successful transaction (`Receipt::from_tx`). -/
def txReceipt (ctx : ApplyCtx) (t : Tx) (c : TxCost) : Receipt :=
  { predecessorId := t.signerId, receiverId := t.receiverId, receiptId := receiptIdFrom t.hash ctx.height 0,
    signerId := t.signerId, signerPk := t.pkKey, gasPrice := c.receiptGasPrice, deposit := t.deposit }

/-- The outcome of a successful transaction. -/
def txOut (ctx : ApplyCtx) (t : Tx) (c : TxCost) : OutD1 :=
  { o := { id := t.hash, receiptIds := [receiptIdFrom t.hash ctx.height 0], gasBurnt := c.gasBurnt,
           tokensBurnt := c.burntAmount, executorId := t.signerId },
    status := .receipt (receiptIdFrom t.hash ctx.height 0) }

/-- A successful transaction (verdict byte `6`: stage 2, ok). -/
theorem prepTx_ok (ctx : ApplyCtx) (acc : TxAcc) (t : Tx) (c : TxCost) (rest : Bytes)
    (hseen : ¬ acc.seen.contains t.hash = true) (hv : t.valid = true)
    (hc : txCost t ctx.gasPrice = some c)
    (hg : ¬ acc.tokens + c.burntAmount ≥ Params.two128 → acc.gas + c.gasBurnt < Params.two64) :
    ∃ acc', prepTx ctx { acc with bits := 6 :: rest } t true = .ok acc' ∧ acc'.bits = rest ∧
      acc'.seen = t.hash :: acc.seen ∧
      acc'.locals = (if t.receiverId == t.signerId then acc.locals ++ [txReceipt ctx t c] else acc.locals) ∧
      acc'.fwd = (if t.receiverId == t.signerId then acc.fwd else acc.fwd ++ [txReceipt ctx t c]) ∧
      (if acc.tokens + c.burntAmount ≥ Params.two128 then
        acc'.leaves = acc.leaves ∧ acc'.gas = acc.gas ∧ acc'.tokens = acc.tokens
      else acc'.leaves = acc.leaves ++ [(txOut ctx t c).leaf] ∧ acc'.gas = acc.gas + c.gasBurnt ∧
        acc'.tokens = acc.tokens + c.burntAmount) := by
  unfold prepTx
  simp only [hseen, Bool.false_eq_true, ite_false, Bool.not_true]
  simp only [bind, Except.bind, pure, Except.pure, check, hc, hv, Option.isSome_some,
    Bool.and_self, Bool.true_or, ite_true, show (6 : UInt8).toNat = 6 from rfl,
    show 6 % 4 = 2 from rfl, show 6 / 4 = 1 from rfl, decide_true, Nat.reduceLT, Nat.reduceLeDiff,
    show (1 == 0 || 2 == 2) = true from rfl]
  by_cases hrs : (t.receiverId == t.signerId) = true <;>
    by_cases ho : acc.tokens + c.burntAmount ≥ Params.two128 <;>
    simp only [hrs, ho, ite_true, ite_false, Bool.false_eq_true]
  · exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · simp only [show acc.gas + c.gasBurnt < Params.two64 from hg ho, decide_true, ite_true]
    exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · simp only [show acc.gas + c.gasBurnt < Params.two64 from hg ho, decide_true, ite_true]
    exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem prepTx_seen (ctx : ApplyCtx) (acc : TxAcc) (t : Tx) (f : Bool)
    (hseen : acc.seen.contains t.hash = true) : prepTx ctx acc t f = .ok acc := by
  unfold prepTx; simp only [hseen, ite_true]; rfl

theorem prepTx_noflag (ctx : ApplyCtx) (acc : TxAcc) (t : Tx)
    (hseen : ¬ acc.seen.contains t.hash = true) :
    prepTx ctx acc t false =
      .ok { acc with seen := t.hash :: acc.seen, leaves := acc.leaves ++ [(failedOutcome t).leaf] } := by
  unfold prepTx; simp only [hseen, Bool.false_eq_true, ite_false, Bool.not_false, ite_true]; rfl

/-- The failed-outcome step of the spec, in the simulation. -/
theorem sim_fail {acc : TxAcc} {st : TxSt} (hs : Sim acc st) (t : Tx) (rest : Bytes) (b : UInt8)
    (ctx : ApplyCtx) (hseen : ¬ st.seen.contains t.hash = true) (hb : b.toNat ≤ 2)
    (hc : (t.valid && (txCost t ctx.gasPrice).isSome) = true ∨ b.toNat = 0) :
    ∃ acc', prepTx ctx { acc with bits := [b] ++ rest } t true = .ok acc' ∧ acc'.bits = rest ∧
      Sim acc' { st with seen := t.hash :: st.seen, outs := st.outs ++ [failedOutcome t] } := by
  obtain ⟨acc', h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
    prepTx_fail ctx acc t b rest (by rw [hs.seen]; exact hseen) hb hc
  refine ⟨acc', h1, h2, ⟨by rw [h3, hs.seen], ?_, by rw [h5, hs.locals], by rw [h6, hs.fwd],
    by rw [h7, hs.gas], by rw [h8, hs.tokens]⟩⟩
  rw [h4, hs.leaves]; simp

/-- **Step simulation**: the verdict bytes depend on the spec state only. -/
theorem prepTx_step (ctx : ApplyCtx) (st st' : TxSt) (t : Tx) (f : Bool)
    (h : processTx ctx st t f = .ok st') :
    ∃ bs : Bytes, ∀ (acc : TxAcc) (rest : Bytes), Sim acc st →
      ∃ acc', prepTx ctx { acc with bits := bs ++ rest } t f = .ok acc' ∧
        acc'.bits = rest ∧ Sim acc' st' := by
  by_cases hseen : st.seen.contains t.hash = true
  · unfold processTx at h
    simp only [hseen, ite_true, pure, Except.pure] at h
    injection h with h; subst h
    refine ⟨[], fun acc rest hs => ⟨_, prepTx_seen ctx _ t f (by rw [hs.seen]; exact hseen), rfl, ?_⟩⟩
    exact ⟨hs.seen, hs.leaves, hs.locals, hs.fwd, hs.gas, hs.tokens⟩
  cases f
  · unfold processTx at h
    simp only [hseen, Bool.false_eq_true, ite_false, Bool.not_false, ite_true, pure,
      Except.pure] at h
    injection h with h; subst h
    refine ⟨[], fun acc rest hs => ⟨_, prepTx_noflag ctx _ t (by rw [hs.seen]; exact hseen), rfl, ?_⟩⟩
    exact ⟨by simp [hs.seen], by simp [hs.leaves], hs.locals, hs.fwd, hs.gas, hs.tokens⟩
  by_cases hv : t.valid = false
  · unfold processTx at h
    simp only [hseen, hv, Bool.false_eq_true, ite_false, Bool.not_false, Bool.not_true, ite_true,
      pure, Except.pure] at h
    injection h with h; subst h
    exact ⟨[0], fun acc rest hs => sim_fail hs t rest 0 ctx hseen (by decide) (Or.inr rfl)⟩
  have hv : t.valid = true := by simpa using hv
  cases hc : txCost t ctx.gasPrice with
  | none =>
    unfold processTx at h
    simp only [hseen, hv, hc, Bool.false_eq_true, ite_false, Bool.not_true, pure, Except.pure] at h
    injection h with h; subst h
    exact ⟨[0], fun acc rest hs => sim_fail hs t rest 0 ctx hseen (by decide) (Or.inr rfl)⟩
  | some c =>
    have hcand : (t.valid && (txCost t ctx.gasPrice).isSome) = true := by simp [hv, hc]
    unfold processTx at h
    simp only [hseen, hv, hc, Bool.false_eq_true, ite_false, Bool.not_true] at h
    cases hr : st.trie.find (accountKeyPath t.signerId) with
    | none => simp [readKey, hr, bind, Except.bind] at h
    | some ov =>
      cases ov with
      | none =>
        simp only [readKey, hr, bind, Except.bind, pure, Except.pure] at h
        injection h with h; subst h
        exact ⟨[0], fun acc rest hs => sim_fail hs t rest 0 ctx hseen (by decide) (Or.inr rfl)⟩
      | some araw =>
        simp only [readKey, hr, bind, Except.bind, pure, Except.pure] at h
        cases hd : decodeSigner araw with
        | error e => simp [hd] at h
        | ok a =>
          simp only [hd] at h
          cases hk : st.trie.find (keyAccessKey t.signerId t.pkKey) with
          | none => simp [hk] at h
          | some ok' =>
            cases ok' with
            | none =>
              simp only [hk] at h
              injection h with h; subst h
              exact ⟨[1], fun acc rest hs => sim_fail hs t rest 1 ctx hseen (by decide) (Or.inl hcand)⟩
            | some kraw =>
              simp only [hk] at h
              cases hdk : decodeAccessKey kraw with
              | none => simp [hdk, throw, throwThe, MonadExceptOf.throw] at h
              | some k =>
                simp only [hdk] at h
                cases hvc : verifyAndCharge a k t c ctx.height with
                | none =>
                  simp only [hvc] at h
                  injection h with h; subst h
                  exact ⟨[2], fun acc rest hs => sim_fail hs t rest 2 ctx hseen (by decide) (Or.inl hcand)⟩
                | some nA =>
                  simp only [hvc] at h
                  refine ⟨[6], fun acc rest hs => ?_⟩
                  have hseen' : ¬ acc.seen.contains t.hash = true := by rw [hs.seen]; exact hseen
                  have hTok : acc.tokens = st.tokens := hs.tokens
                  have hGas : acc.gas = st.gas := hs.gas
                  by_cases ho : st.tokens + c.burntAmount ≥ Params.two128
                  · obtain ⟨acc', e1, e2, e3, e4, e5, e6⟩ :=
                      prepTx_ok ctx acc t c rest hseen' hv hc (fun h' => absurd (hTok ▸ ho) h')
                    simp only [hTok, ho, ite_true] at e6
                    refine ⟨acc', e1, e2, ?_⟩
                    by_cases hrs : (t.receiverId == t.signerId) = true
                    · simp only [hrs, ho, ite_true] at h e4 e5
                      injection h with h; subst h
                      exact ⟨by rw [e3, hs.seen], by rw [e6.1, hs.leaves], by rw [e4, hs.locals]; rfl,
                        by rw [e5, hs.fwd], by rw [e6.2.1, hs.gas], by rw [e6.2.2]⟩
                    · simp only [hrs, ho, ite_true, ite_false, Bool.false_eq_true] at h e4 e5
                      split at h
                      · try simp only [ho, ite_true] at h
                        injection h with h; subst h
                        exact ⟨by rw [e3, hs.seen], by rw [e6.1, hs.leaves], by rw [e4, hs.locals],
                          by rw [e5, hs.fwd]; rfl, by rw [e6.2.1, hs.gas], by rw [e6.2.2]⟩
                      · simp [throw, throwThe, MonadExceptOf.throw] at h
                  · by_cases hg : st.gas + c.gasBurnt ≥ Params.two64
                    · exfalso
                      by_cases hrs : (t.receiverId == t.signerId) = true
                      · simp [hrs, ho, hg, throw, throwThe, MonadExceptOf.throw] at h
                      · simp only [hrs, Bool.false_eq_true, ite_false] at h
                        split at h
                        · simp [ho, hg, throw, throwThe, MonadExceptOf.throw] at h
                        · simp [throw, throwThe, MonadExceptOf.throw] at h
                    obtain ⟨acc', e1, e2, e3, e4, e5, e6⟩ :=
                      prepTx_ok ctx acc t c rest hseen' hv hc (fun _ => by omega)
                    simp only [hTok, ho, ite_false] at e6
                    refine ⟨acc', e1, e2, ?_⟩
                    by_cases hrs : (t.receiverId == t.signerId) = true
                    · simp only [hrs, ho, hg, ite_true, ite_false] at h e4 e5
                      split at h
                      · split at h
                        · injection h with h; subst h
                          exact ⟨by rw [e3, hs.seen], by rw [e6.1, hs.leaves]; simp [txOut],
                            by rw [e4, hs.locals]; rfl, by rw [e5, hs.fwd],
                            by rw [e6.2.1, hs.gas], by rw [e6.2.2]⟩
                        · simp [throw, throwThe, MonadExceptOf.throw] at h
                      · simp [throw, throwThe, MonadExceptOf.throw] at h
                    · simp only [hrs, Bool.false_eq_true, ite_false] at h e4 e5
                      split at h
                      · try simp only [ho, hg, ite_false] at h
                        split at h
                        · split at h
                          · injection h with h; subst h
                            exact ⟨by rw [e3, hs.seen], by rw [e6.1, hs.leaves]; simp [txOut],
                              by rw [e4, hs.locals], by rw [e5, hs.fwd]; rfl,
                              by rw [e6.2.1, hs.gas], by rw [e6.2.2]⟩
                          · simp [throw, throwThe, MonadExceptOf.throw] at h
                        · simp [throw, throwThe, MonadExceptOf.throw] at h
                      · simp [throw, throwThe, MonadExceptOf.throw] at h

/-- **Run simulation.** -/
theorem prepTxs_sim (ctx : ApplyCtx) : ∀ (txs : List (Tx × Bool)) (st st' : TxSt),
    processTxs ctx st txs = .ok st' →
    ∃ bs : Bytes, ∀ (acc : TxAcc) (rest : Bytes), Sim acc st →
      ∃ acc', prepTxs ctx { acc with bits := bs ++ rest } txs = .ok acc' ∧
        acc'.bits = rest ∧ Sim acc' st'
  | [], st, st', h => by
    simp only [processTxs] at h
    injection h with h; subst h
    exact ⟨[], fun acc rest hs => ⟨_, rfl, rfl, ⟨hs.seen, hs.leaves, hs.locals, hs.fwd, hs.gas, hs.tokens⟩⟩⟩
  | (t, f) :: txs, st, st', h => by
    simp only [processTxs, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i st1 h1
      obtain ⟨bs1, hb1⟩ := prepTx_step ctx st st1 t f h1
      obtain ⟨bs2, hb2⟩ := prepTxs_sim ctx txs st1 st' h
      refine ⟨bs1 ++ bs2, fun acc rest hs => ?_⟩
      obtain ⟨acc1, e1, e2, s1⟩ := hb1 acc (bs2 ++ rest) hs
      have hacc1 : acc1 = { acc1 with bits := bs2 ++ rest } := by
        cases acc1; simp only at e2; subst e2; rfl
      obtain ⟨acc2, f1, f2, s2⟩ := hb2 acc1 rest s1
      refine ⟨acc2, ?_, f2, s2⟩
      simp only [prepTxs, bind, Except.bind]
      rw [List.append_assoc, e1]
      rw [hacc1]; exact f1

/-- **`PrepTxNativeStmt`.** -/
theorem prepTxNative : PrepTxNativeStmt := by
  intro ctx st0 txs st h hs0 ho0 hl0 hf0 hg0 ht0
  obtain ⟨bs, hb⟩ := prepTxs_sim ctx txs st0 st h
  obtain ⟨acc, e1, e2, s⟩ := hb {} [] ⟨hs0.symm, by simp [ho0], hl0.symm, hf0.symm, hg0.symm, ht0.symm⟩
  refine ⟨bs, acc, ?_, e2, s.leaves, s.locals, s.fwd, s.gas, s.tokens⟩
  simpa using e1

end ZkFormal.NearV3.D1
