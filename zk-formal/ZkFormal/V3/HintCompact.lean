import NearSpecV3.HintCompact
import ZkFormal.V3.RefundCodec

/-!
# Canonical refunds and the compact hint body (STATUS-V3-SIZE lever 2)

The compact wire codec (`compactRefund`, `compactBodyOf`, `pCRefund`,
`decodeBodyC`) and its wire/length lemmas live in `NearSpecV3.PrepD0` (spec,
next to `pRefund`/`decodeBody`).  This module adds what only the candidate
side needs:

* **The canonicality invariant**: every refund the D0 runtime emits satisfies
  `refundCanonical` — refund-shaped (predecessor `system`, well-formed), with
  `signerId = receiverId` and `gasPrice = 0`.  `TransferV1.applyReceipt` emits
  exactly `[gasRefundReceipt r height surplus]`, and `gasRefundReceipt` is
  canonical by construction.  Mirrors `RefundCodec`'s shape invariants.
* **The bridge to the wire**: `decodeBodyC_outgoing` — the compact round trip
  on a chunk's actual outgoing refunds — and the full-hint wire length
  (framing of `Assembly.HintCodec`, restated locally).
* Kernel-checked budgets: hint ≤ `16 + 181·4481 = 811,077` against the proved
  native `≤ 1,295,025` (`accepted_native_body_bound`), freeing **483,948 B**
  of the 8 MiB artifact.

Everything is proved inside the existing ROM admission framework: no verifier
or parameter change, no new assumption.  The Good-semantics amendment that
puts the compact body on the wire (`HeaderSemanticsV3.body`, rebuilt-native
EMR) is tracked in `docs/logs/v3-sizeopt-2026-10.md`.
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

/-! ## The bridge to the compact wire -/

/-- The zk-side canonical invariant implies the spec-side flattened premise
(`NearSpecV3.refundCanonicalWf`). -/
theorem canonical_flat {r : Receipt} (h : refundCanonical r = true) :
    NearSpecV3.refundCanonicalWf r := by
  obtain ⟨pred, recv, rid, signer, pk, gp, dep⟩ := r
  simp only [refundCanonical, refundShape, Receipt.wf, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  have hk : pk.tag ≠ 2 := by
    simp only [PublicKey.wf, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h4; omega
  refine ⟨h8, h9, h10, ?_, hk⟩
  simp only [Receipt.wf, h1, h2, h3, h4, h5, h6, h7, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq]
  trivial

/-- Compact round trip on a chunk's actual outgoing refunds. -/
theorem decodeBodyC_outgoing (prims : Prims) (ctx : ApplyCtx) (t : PTrie)
    (rs : List Receipt) (out : MainOut) (h : applyNewChunk prims ctx t rs = .ok out)
    (hw : ∀ r ∈ rs, r.wf = true) (hn : out.outgoing.length < 4294967296) :
    NearSpecV3.decodeBodyC (NearSpecV3.compactBodyOf out.outgoing) = .ok out.outgoing := by
  refine NearSpecV3.decodeBodyC_compactBodyOf _ ?_ hn
  intro x hx
  exact canonical_flat (applyNewChunk_outgoing_canonical prims ctx t rs out h hw x hx)

/-! ## Full-hint wire length and the freed budget -/

theorem leN_length : ∀ (w x : Nat), (NearSpec.leN w x).length = w
  | 0, _ => rfl
  | w + 1, x => by
    simp only [NearSpec.leN, List.length_cons]
    exact congrArg (fun n => n + 1) (leN_length w (x / 256))

theorem borshBytes_length (b : Bytes) : (borshBytes b).length = 4 + b.length := by
  simp only [borshBytes, NearSpec.u32, List.length_append, leN_length]

/-- The compact hint on the wire: `u32 n ‖ borshBytes body` — the framing of
`ZkFormal.NearV3.Assembly.Hint.encode`, restated locally to keep this module
off the Assembly dependency chain. -/
def compactHintOf (rs : List Receipt) : Bytes :=
  NearSpec.u32 rs.length ++ borshBytes (NearSpecV3.compactBodyOf rs)

theorem compactHintOf_length (rs : List Receipt) :
    (compactHintOf rs).length = 8 + (compactBodyOf rs).length := by
  show (NearSpec.u32 rs.length ++ borshBytes (NearSpecV3.compactBodyOf rs)).length = _
  rw [List.length_append, borshBytes_length]
  simp only [NearSpec.u32, leN_length]
  omega

/-- Wire length of the compact hint.  `hn` is A1's receipt bound
(`max_receipts`). -/
theorem compactHint_length_le (rs : List Receipt) (hn : rs.length ≤ 4481)
    (hw : ∀ r ∈ rs, r.wf = true) :
    (compactHintOf rs).length ≤ 16 + 181 * 4481 := by
  have e1 := NearSpecV3.compactBodyOf_length_le rs hw
  rw [compactHintOf_length]
  omega

/-- Kernel-checked: the compact hint budget for the A1-max refund list. -/
theorem compactHint_max_eq : 16 + 181 * 4481 = 811077 := by decide

/-- Kernel-checked: the compact hint frees this many bytes of the artifact
against the proved native bound `|Hint.encode| ≤ 8 + bodyMax = 1,295,025`
(`accepted_native_body_bound`; `Size.V3.bodyMax_eq = 8 + 4481 · 289`). -/
theorem compact_freed_eq : 8 + (8 + 4481 * 289) - (16 + 181 * 4481) = 483948 := by decide

end ZkFormal.V3
