import NearSpecV3.PrepD0
import NearSpecV3.ClaimV3Props

/-!
# Compact hint-body codec for refund receipts (STATUS-V3-SIZE lever 2)

The native hint body `B = u32 0 ‖ encodeReceipts refunds` spends 289 B on the
largest refund (SECP256K1 gas refund to a 64-character implicit account;
`Size.V3.bodyMax_eq`: `bodyMax = 8 + 4481 · 289 = 1,295,017` under A1).  Every
refund the D0 runtime emits satisfies `refundCanonicalWf` below — predecessor
`system`, `signerId = receiverId`, `gasPrice = 0` (proved in
`ZkFormal.V3.HintCompact`, mirroring `RefundCodec`) — so the wire may carry,
per refund, only

    borshBytes receiverId ‖ receiptId ‖ signerPk.encode ‖ u128 deposit

(≤ 181 B) and reconstruct the dropped fields.  `pCRefund`/`decodeBodyC`
produce the *same* `Receipt` values, and the header's `encodedMerkleRoot`
commitment stays over the rebuilt native bucket `bodyOf refunds`
(`compact_bodyOf_is_native` direction: decoding is deterministic, so
rebuilding is exact).  Kernel budgets: body ≤ `8 + 181·4481 = 811,069`,
freeing **483,948 B** of the 8 MiB artifact (`compact_freed_eq`).

No verifier or protocol-parameter change, no new assumption: a wire codec for
the prover-carried hint bytes inside the existing ROM admission framework.
-/

namespace NearSpecV3

open NearSpec

/-! ## Parser inversion (ported from `ZkFormal.V3.EncodeWitness`, spec parsers) -/

theorem pTake_ok (n : Nat) (w : String) (b rest : Bytes) (hl : b.length = n) :
    pTake n w (b ++ rest) = .ok (b, rest) := by
  subst hl; exact lift_ok (takeT_append b rest)

def pkWf3 (k : PublicKey) : Bool :=
  (k.tag == 0 && k.data.length == 32) || (k.tag == 1 && k.data.length == 64) ||
  (k.tag == 2 && k.data.length == 1952)

theorem pAccountId_ok (w : String) (a rest : Bytes) (h : AccountId.valid a = true) :
    pAccountId w (borshBytes a ++ rest) = .ok (a, rest) := by
  have hl : a.length < 4294967296 := by
    simp only [AccountId.valid, Bool.and_eq_true, decide_eq_true_eq] at h; omega
  simp only [pAccountId, pBytes_ok _ _ _ hl, bind, Except.bind, h, ↓reduceIte, pure,
    Except.pure]

theorem pPublicKey_ok (w : String) (k : PublicKey) (rest : Bytes) (h : pkWf3 k = true) :
    pPublicKey w (k.encode ++ rest) = .ok (k, rest) := by
  obtain ⟨t, d⟩ := k
  simp only [pkWf3, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  simp only [PublicKey.encode, List.append_assoc]
  rcases h with (⟨rfl, hd⟩ | ⟨rfl, hd⟩) | ⟨rfl, hd⟩ <;>
  simp only [pPublicKey, pU8_ok _ _ _ (by decide : (0:Nat) < 256),
    pU8_ok _ _ _ (by decide : (1:Nat) < 256), pU8_ok _ _ _ (by decide : (2:Nat) < 256),
    bind, Except.bind, pure, Except.pure, pTake_ok _ _ _ _ hd]

theorem pkWf3_of_wf (k : PublicKey) (h : k.wf = true) : pkWf3 k = true := by
  simp only [PublicKey.wf, Bool.or_eq_true] at h
  simp only [pkWf3, Bool.or_eq_true, h, true_or]

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

/-- The canonical-refund premise, flattened.  `ZkFormal.V3.refundCanonical`
implies this (`.canonical_flat` there). -/
def refundCanonicalWf (r : Receipt) : Prop :=
  r.predecessorId = AccountId.system ∧ r.signerId = r.receiverId ∧
    r.gasPrice = 0 ∧ r.wf = true ∧ r.signerPk.tag ≠ 2

theorem compactRefund_encode (r : Receipt) (rest : Bytes) (h : refundCanonicalWf r) :
    pCRefund (compactRefund r ++ rest) = .ok (r, rest) := by
  obtain ⟨hc, _hs, hg, hw, hk⟩ := h
  obtain ⟨pred, recv, rid, signer, pk, gp, dep⟩ := r
  have hc' : pred = AccountId.system := hc
  have hg' : gp = 0 := hg
  have hs' : signer = recv := _hs
  subst hc'; subst hg'
  rw [hs'] at hw
  rw [hs']
  simp only [Receipt.wf, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hw
  have hrecv : AccountId.valid recv = true := hw.1.1.1.1.1.2
  have hpk : pk.wf = true := hw.1.1.1.2
  have hrid : rid.length = 32 := hw.1.1.2
  have hdep : dep < Params.two128 := hw.2
  simp only [compactRefund, List.append_assoc]
  simp only [pCRefund, pAccountId_ok _ _ _ hrecv, pHash_ok _ _ _ hrid,
    pPublicKey_ok _ _ _ (pkWf3_of_wf _ hpk), pU128_ok _ _ _ hdep, bind, Except.bind,
    ↓reduceIte, beq_iff_eq, hk, pure, Except.pure]

/-- Round trip: the compact decoder reconstructs the same receipts. -/
theorem decodeBodyC_compactBodyOf (rs : List Receipt)
    (h : ∀ r ∈ rs, refundCanonicalWf r) (hn : rs.length < 4294967296) :
    decodeBodyC (compactBodyOf rs) = .ok rs := by
  have hv := pVec_ok "refunds" pCRefund compactRefund rs [] hn
    (fun r hr rest => compactRefund_encode r rest (h r hr))
  have hv2 : pVec "refunds" pCRefund (compactReceipts rs) = .ok (rs, []) := by
    simpa only [compactReceipts, encList, concatAll, List.append_nil] using hv
  simp only [compactBodyOf, decodeBodyC,
    pU32_ok _ _ _ (by decide : (1:Nat) < 4294967296), bind, Except.bind,
    bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hv2, List.isEmpty_nil,
    Bool.not_true, pure, Except.pure]

/-! ## Length bounds and the freed budget -/

theorem compactRefund_length_le (r : Receipt) (hw : r.wf = true) :
    (compactRefund r).length ≤ 181 := by
  obtain ⟨pred, recv, rid, signer, pk, gp, dep⟩ := r
  simp only [Receipt.wf, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hw
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := hw
  have e1 := acctBorsh_length_le recv h2
  have e2 : rid.length = 32 := h5
  have e3 := pkEncode_length_le pk h4
  have e4 := u128_length dep
  calc (compactRefund ⟨pred, recv, rid, signer, pk, gp, dep⟩).length
      = (borshBytes recv).length + rid.length + pk.encode.length + 16 := by
        simp only [compactRefund, List.append_assoc, List.length_append,
          borshBytes_length, u128_length]
        omega
    _ ≤ 68 + 32 + 65 + 16 := by omega
    _ = 181 := rfl

theorem compactReceipts_length_le (rs : List Receipt)
    (hw : ∀ r ∈ rs, r.wf = true) :
    (compactReceipts rs).length ≤ 4 + 181 * rs.length := by
  induction rs with
  | nil =>
    simp only [compactReceipts, concatAll, List.map_nil, NearSpec.u32, List.length_append,
      List.length_nil, leN_length]
    omega
  | cons r rs ih =>
    have hrs : ∀ r' ∈ rs, r'.wf = true :=
      fun r' hr' => hw r' (List.mem_cons_of_mem _ hr')
    have e1 := compactRefund_length_le r (hw r List.mem_cons_self)
    have e2 := ih hrs
    simp only [compactReceipts, concatAll, List.map_cons, List.map_nil, List.length_append,
      List.length_cons, NearSpec.u32, leN_length] at e1 e2 ⊢
    omega

theorem compactBodyOf_length_le (rs : List Receipt) (hw : ∀ r ∈ rs, r.wf = true) :
    (compactBodyOf rs).length ≤ 8 + 181 * rs.length := by
  have e1 := compactReceipts_length_le rs hw
  simp only [compactBodyOf, compactReceipts, NearSpec.u32, List.length_append,
    List.length_cons, leN_length] at e1 ⊢
  omega

/-- Kernel-checked: compact body budget at the A1 receipt cap. -/
theorem compactBody_max_eq : 8 + 181 * 4481 = 811069 := by decide

/-- Kernel-checked: the compact hint frees this many bytes of the artifact
against the proved native bound `|Hint.encode| ≤ 8 + bodyMax = 1,295,025`
(`accepted_native_body_bound`; `Size.V3.bodyMax_eq = 8 + 4481 · 289`). -/
theorem compact_freed_eq : 8 + (8 + 4481 * 289) - (16 + 181 * 4481) = 483948 := by decide

end NearSpecV3
