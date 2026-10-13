import ZkFormal.V3.RefundCodec

/-!
# Compact hint-body codec for refund receipts (STATUS-V3-SIZE lever 2)

The native hint body `B = u32 0 ‖ encodeReceipts refunds` spends 289 B on the
largest refund (SECP256K1 gas refund to a 64-character implicit account;
`Size.V3.bodyMax_eq`: `bodyMax = 8 + 4481 · 289 = 1,295,017` under A1).  Every
refund the D0 runtime ever generates is `gasRefundReceipt`-shaped —
`TransferV1.applyReceipt` emits exactly `[gasRefundReceipt r height surplus]`
when the price surplus is nonzero — so every hint refund satisfies:
predecessor `system`, `signerId = receiverId`, `gasPrice = 0`, and a
well-formed signer key (ED25519/SECP256K1, never ML-DSA).

The compact wire format drops exactly the fields the decoder reconstructs:

* predecessor `system`, the receipt tag `0`, the three zero vector counts and
  the transfer action tag — constants of the refund shape;
* `signerId` — always the receiver;
* `gasPrice` — always 0.

Wire: `compactHintOf rs = u32 n ‖ borshBytes (compactBodyOf rs)` with
`compactBodyOf rs = u32 1 ‖ u32 n ‖ refunds` and, per refund,
`borshBytes receiverId ‖ receiptId ‖ signerPk.encode ‖ u128 deposit`
(≤ 181 B against the native 289 B).  The hint budget drops from the proved
native `|Hint.encode| ≤ 1,295,025` (`accepted_native_body_bound`) to
`≤ 16 + 181 · 4481 = 811,077`, freeing 483,948 B of the 8 MiB artifact —
headroom for qvV3 and later tables at unchanged protocol parameters.

Everything mirrors `ZkFormal.V3.RefundCodec`: the compact decoder reconstructs
the *same* `Receipt` values, so every downstream consumer (`prepBody`, the
runtime refund application, the receipt SHA family) is unchanged.  No verifier
change, no protocol-parameter change, no new assumption: this is a wire codec
for the prover-carried hint bytes inside the existing ROM admission framework.
-/

namespace ZkFormal.V3

open NearSpec NearSpec.TransferV1 NearSpecV3 ReexecV3D0

/-! ## The canonical refund invariant -/

/-- What the compact codec may assume (and reconstruct): a refund-shaped
receipt whose signer is the receiver and whose gas price is 0. -/
def refundCanonical (r : Receipt) : Bool :=
  refundShape r && r.signerId == r.receiverId && r.gasPrice == 0

theorem gasRefundReceipt_canonical (parent : Receipt) (height refund : Nat)
    (hp : parent.wf = true) (hr : refund < Params.two128) :
    refundCanonical (gasRefundReceipt parent height refund) = true := by
  have h1 := gasRefundReceipt_shape parent height refund hp hr
  simp only [refundCanonical, gasRefundReceipt, Bool.and_eq_true, beq_iff_eq] at h1 ⊢
  exact ⟨⟨h1, trivial⟩, trivial⟩

/-- Strengthened refund invariant of one receipt application: every *new*
refund is canonical.  Mirrors `applyReceipt_refunds_shape`. -/
theorem applyReceipt_refunds_canonical {ctx : Ctx} {st st' : Acc} {r : Receipt}
    (h : applyReceipt ctx st r = some st') (hr : r.wf = true) :
    ∃ l : List Receipt, st'.refunds = st.refunds ++ l ∧ l.length ≤ 1 ∧
      ∀ x ∈ l, refundCanonical x = true := by
  unfold applyReceipt at h
  dsimp only at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  rename_i hle
  split at h
  · cases h
  rename_i hb
  split at h
  · cases h
  split at h
  · cases h
  cases h
  refine ⟨_, rfl, ?_, ?_⟩
  · split <;> simp
  · intro x hx
    split at hx
    · simp at hx
    · simp only [List.mem_singleton] at hx
      subst hx
      apply gasRefundReceipt_canonical _ _ _ hr
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at hb
      exact Nat.lt_of_not_le hb.2

/-- The canonical invariant threads through receipt application, mirroring
`applyReceipts_refunds_shape`. -/
theorem applyReceipts_refunds_canonical (ctx : ApplyCtx) :
    ∀ (rs : List Receipt) (i : Nat) (acc : Acc) (ls : List Limit) (out : Acc × List Limit),
      applyReceipts ctx i (acc, ls) rs = .ok out → (∀ r ∈ rs, r.wf = true) →
      (∀ x ∈ acc.refunds, refundCanonical x = true) →
      (∀ x ∈ out.1.refunds, refundCanonical x = true) ∧
        out.1.refunds.length ≤ acc.refunds.length + rs.length
  | [], i, acc, ls, out, h, _, hacc => by
    simp only [applyReceipts, Except.ok.injEq] at h
    subst h
    exact ⟨hacc, by simp⟩
  | r :: rs, i, acc, ls, out, h, hw, hacc => by
    have hwr : r.wf = true := hw r List.mem_cons_self
    have hws : ∀ r ∈ rs, r.wf = true := fun r' hr' => hw r' (List.mem_cons_of_mem _ hr')
    simp only [applyReceipts] at h
    split at h
    · cases h
    split at h
    · obtain ⟨acc', h1, h⟩ := bind_ok' h
      have e := applySystemReceipt_refunds h1
      have ih := applyReceipts_refunds_canonical ctx rs (i + 1) acc' ls out h hws
        (by rw [e]; exact hacc)
      rw [e] at ih
      exact ⟨ih.1, by simp only [List.length_cons] at *; omega⟩
    · split at h
      · split at h <;> cases h
      · rename_i acc' ha
        obtain ⟨ls', -, h⟩ := bind_ok' h
        obtain ⟨l, el, _, hl⟩ := applyReceipt_refunds_canonical ha hwr
        have hacc' : ∀ x ∈ acc'.refunds, refundCanonical x = true := by
          intro x hx
          rw [el, List.mem_append] at hx
          rcases hx with hx | hx
          · exact hacc x hx
          · exact hl x hx
        have ih := applyReceipts_refunds_canonical ctx rs (i + 1) acc' ls' out h hws hacc'
        refine ⟨ih.1, ?_⟩
        have := ih.2
        rw [el, List.length_append] at this
        simp only [List.length_cons]
        omega

/-- The assembled chunk's outgoing refunds are canonical, mirroring
`applyNewChunk_refunds_shape`. -/
theorem applyNewChunk_outgoing_canonical (prims : Prims) (ctx : ApplyCtx) (t : PTrie)
    (rs : List Receipt) (out : MainOut) (h : applyNewChunk prims ctx t rs = .ok out)
    (hw : ∀ r ∈ rs, r.wf = true) :
    ∀ x ∈ out.outgoing, refundCanonical x = true := by
  obtain ⟨t0, ls, out', ha, e⟩ := applyNewChunk_outgoing prims ctx t rs out h
  rw [e]
  exact (applyReceipts_refunds_canonical ctx rs 0 _ ls out' ha hw (by simp)).1

/-! ## Byte lengths -/

theorem leN_length : ∀ (w x : Nat), (NearSpec.leN w x).length = w
  | 0, _ => rfl
  | w + 1, x => by
    simp only [NearSpec.leN, List.length_cons]
    exact congrArg (fun n => n + 1) (leN_length w (x / 256))

theorem borshBytes_length (b : Bytes) : (borshBytes b).length = 4 + b.length := by
  simp only [borshBytes, NearSpec.u32, List.length_append, leN_length]

theorem u128_length (x : Nat) : (u128 x).length = 16 := leN_length 16 x

theorem pkEncode_length_le (k : PublicKey) (h : k.wf = true) : k.encode.length ≤ 65 := by
  obtain ⟨t, d⟩ := k
  simp only [PublicKey.encode, List.length_append, u8, leN_length]
  simp only [PublicKey.wf, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h
  rcases h with ⟨rfl, hd⟩ | ⟨rfl, hd⟩ <;> omega

theorem acctBorsh_length_le (a : Bytes) (h : AccountId.valid a = true) :
    (borshBytes a).length ≤ 68 := by
  simp only [AccountId.valid, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [borshBytes_length]
  omega

/-! ## The compact codec -/

/-- Compact wire encoding of one refund: receiver, receipt id, signer key,
deposit.  At most 181 bytes for a canonical, well-formed refund, against the
native 289. -/
def compactRefund (r : Receipt) : Bytes :=
  borshBytes r.receiverId ++ r.receiptId ++ r.signerPk.encode ++ u128 r.deposit

def compactReceipts (rs : List Receipt) : Bytes :=
  u32 rs.length ++ concatAll (rs.map compactRefund)

/-- Compact hint body: version tag 1 (the native body's first u32 is the
always-zero transaction count), then the refunds. -/
def compactBodyOf (rs : List Receipt) : Bytes := u32 1 ++ compactReceipts rs

/-- The compact hint on the wire: `u32 n ‖ borshBytes body` — the framing of
`ZkFormal.NearV3.Assembly.Hint.encode`, restated locally to keep this module
off the Assembly dependency chain. -/
def compactHintOf (rs : List Receipt) : Bytes :=
  NearSpec.u32 rs.length ++ borshBytes (compactBodyOf rs)

theorem compactHintOf_length (rs : List Receipt) :
    (compactHintOf rs).length = 8 + (compactBodyOf rs).length := by
  show (NearSpec.u32 rs.length ++ borshBytes (compactBodyOf rs)).length = _
  rw [List.length_append, borshBytes_length]
  simp only [NearSpec.u32, leN_length]
  omega

/-- Decode one compact refund, reconstructing the dropped fields (`system`
predecessor, signer = receiver, gas price 0). -/
def pCRefund : P Receipt := fun bs => do
  let (recv, bs) ← pAccountId "receiver_id" bs
  let (rid, bs) ← pHash "receipt_id" bs
  let (pk, bs) ← pPublicKey "signer_public_key" bs
  if pk.tag == 2 then throw "invalid hint: refund ML-DSA signer key"
  let (dep, bs) ← pU128 "deposit" bs
  pure ({ predecessorId := AccountId.system, receiverId := recv, receiptId := rid,
          signerId := recv, signerPk := pk, gasPrice := 0, deposit := dep }, bs)

/-- Parse the compact body (no trailing bytes). -/
def decodeBodyC (b : Bytes) : Except String (List Receipt) := do
  let (v, b) ← pU32 "version" b
  if v != 1 then throw "invalid hint: body version"
  let (rs, b) ← pVec "refunds" pCRefund b
  if !b.isEmpty then throw "invalid hint: trailing bytes in body"
  pure rs

theorem compactRefund_encode (r : Receipt) (h : refundCanonical r = true) (rest : Bytes) :
    pCRefund (compactRefund r ++ rest) = .ok (r, rest) := by
  obtain ⟨pred, recv, rid, signer, pk, gp, dep⟩ := r
  simp only [refundCanonical, refundShape, Receipt.wf, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  subst h8
  subst h9
  subst h10
  have hk : pk.tag ≠ 2 := by
    simp only [PublicKey.wf, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h4; omega
  simp only [compactRefund, List.append_assoc]
  simp only [pCRefund, pAccountId_ok _ _ _ h2, pHash_ok _ _ _ h5,
    pPublicKey_ok _ _ _ (pkWf3_of_wf _ h4), pU128_ok _ _ _ h7, bind, Except.bind,
    ↓reduceIte, beq_iff_eq, hk, pure, Except.pure]

theorem decodeBodyC_compactBodyOf (rs : List Receipt) (h : ∀ r ∈ rs, refundCanonical r = true)
    (hn : rs.length < 4294967296) : decodeBodyC (compactBodyOf rs) = .ok rs := by
  have hv := pVec_ok "refunds" pCRefund compactRefund rs [] hn
    (fun r hr rest => compactRefund_encode r (h r hr) rest)
  have hv2 : pVec "refunds" pCRefund (compactReceipts rs) = .ok (rs, []) := by
    simpa only [compactReceipts, encList, concatAll, List.append_nil] using hv
  simp only [compactBodyOf, decodeBodyC,
    pU32_ok _ _ _ (by decide : (1:Nat) < 4294967296), bind, Except.bind,
    bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hv2, List.isEmpty_nil, Bool.not_true,
    pure, Except.pure]

/-! ## Length bounds and the freed budget -/

theorem compactRefund_length_le (r : Receipt) (h : refundCanonical r = true) :
    (compactRefund r).length ≤ 181 := by
  obtain ⟨pred, recv, rid, signer, pk, gp, dep⟩ := r
  simp only [refundCanonical, refundShape, Receipt.wf, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, _h8⟩, h9⟩, _h10⟩ := h
  have e1 := acctBorsh_length_le recv h2
  have e2 : rid.length = 32 := h5
  have e3 := pkEncode_length_le pk h4
  have e4 := u128_length dep
  calc (compactRefund ⟨pred, recv, rid, signer, pk, gp, dep⟩).length
      = (borshBytes recv).length + rid.length + pk.encode.length + 16 := by
        simp only [compactRefund, List.append_assoc, List.length_append, borshBytes_length,
          u128_length]
        omega
    _ ≤ 68 + 32 + 65 + 16 := by omega
    _ = 181 := rfl

theorem compactReceipts_length_le (rs : List Receipt)
    (h : ∀ r ∈ rs, refundCanonical r = true) :
    (compactReceipts rs).length ≤ 4 + 181 * rs.length := by
  induction rs with
  | nil =>
    simp only [compactReceipts, concatAll, List.map_nil, NearSpec.u32, List.length_append,
      List.length_nil, leN_length]
    omega
  | cons r rs ih =>
    have hr : refundCanonical r = true := h r List.mem_cons_self
    have hrs : ∀ r' ∈ rs, refundCanonical r' = true :=
      fun r' hr' => h r' (List.mem_cons_of_mem _ hr')
    have e1 := compactRefund_length_le r hr
    have e2 := ih hrs
    simp only [compactReceipts, concatAll, List.map_cons, List.map_nil, List.length_append,
      List.length_cons, NearSpec.u32, leN_length] at e1 e2 ⊢
    omega

theorem compactBodyOf_length_le (rs : List Receipt)
    (h : ∀ r ∈ rs, refundCanonical r = true) :
    (compactBodyOf rs).length ≤ 8 + 181 * rs.length := by
  have e1 := compactReceipts_length_le rs h
  simp only [compactBodyOf, compactReceipts, NearSpec.u32, List.length_append,
    List.length_cons, leN_length] at e1 ⊢
  omega

/-- Wire length of the compact hint: the hint's `u32 n` and borsh framing (8)
plus the body's version tag and count (8) plus at most 181 bytes per refund.
`hn` is A1's receipt bound (`max_receipts`). -/
theorem compactHint_length_le (rs : List Receipt) (hn : rs.length ≤ 4481)
    (h : ∀ r ∈ rs, refundCanonical r = true) :
    (compactHintOf rs).length ≤ 16 + 181 * 4481 := by
  have e1 := compactBodyOf_length_le rs h
  rw [compactHintOf_length]
  omega

/-- Kernel-checked: the compact hint budget for the A1-max refund list. -/
theorem compactHint_max_eq : 16 + 181 * 4481 = 811077 := by decide

/-- Kernel-checked: the compact hint frees this many bytes of the artifact
against the proved native bound `|Hint.encode| ≤ 8 + bodyMax = 1,295,025`
(`accepted_native_body_bound`; `Size.V3.bodyMax_eq = 8 + 4481 · 289`). -/
theorem compact_freed_eq : 8 + (8 + 4481 * 289) - (16 + 181 * 4481) = 483948 := by decide

end ZkFormal.V3
