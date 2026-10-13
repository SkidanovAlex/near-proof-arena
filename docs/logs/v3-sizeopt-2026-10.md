# lane/v3-size-opt — proof-size optimization without new assumptions (2026-10-13)

Goal: shrink the v3 artifact as far as possible with **no new assumptions** (ROM
framework unchanged, no protocol-parameter change), ahead of the signed
`near-chunk-v3` challenge.

## Where the size stands (measured, main @ d6725367/c6330302)

Real honest proofs accepted by the deployed Lean verifier
(`docs/logs/v3-prover-prove-2026-10.md`):

| case | proof B (hint B) |
|---|---|
| 00-h10004-s3 | 5,256,829 (16) |
| 00-h10035-s3 | 5,674,156 (155) |
| 01-h10009-s1 | 5,618,528 (155) |

Honest-admission constants (`NearV3/Assembly/NearAdmission.lean`):
`v3MaxInner = 6,435,489` (= `nearV3_sizeMaxAligned`, roll-in alignment landed),
`v3MaxHintBytes = 1,953,115`, and `4 + v3MaxHintBytes + v3MaxInner = 8,388,608`
**exactly** — the artifact is at zero slack against the 8 MiB cap, so any inner
growth (qvV3 ≈ +75–112 KB) re-opens the cap.

## What landed in this lane

`zk-formal/ZkFormal/V3/HintCompact.lean` — the compact hint-body codec
(STATUS-V3-SIZE §4 lever 2), proved end to end:

* **Invariant.** Every refund the D0 runtime emits is canonical:
  `refundCanonical = refundShape ∧ signerId = receiverId ∧ gasPrice = 0`
  (`applyReceipt_refunds_canonical`, `applyNewChunk_outgoing_canonical`;
  `TransferV1.applyReceipt` emits exactly `[gasRefundReceipt …]`).  This is
  what lets the wire drop predecessor `system`, the receipt tag, the three
  zero vector counts, the transfer action tag, `signerId` (= receiver) and
  `gasPrice` (= 0) — the decoder reconstructs all of them, producing the
  **same `Receipt` values**, so `prepBody`, the runtime refund application and
  the receipt SHA family are untouched.
* **Wire.** `compactHintOf rs = u32 n ‖ borshBytes (compactBodyOf rs)`,
  `compactBodyOf rs = u32 1 ‖ u32 n ‖ refunds`, per refund
  `borshBytes receiverId ‖ receiptId ‖ signerPk.encode ‖ u128 deposit`.
* **Bounds (kernel-checked).** ≤ 181 B/refund against the native 289;
  `compactHint_max_eq : 16 + 181·4481 = 811,077` (A1 max) against the proved
  native `≤ 1,295,025`; `compact_freed_eq : freed = 483,948` bytes.
* **Round trip.** `compactRefund_encode`, `decodeBodyC_compactBodyOf`
  (`decodeBodyC (compactBodyOf rs) = .ok rs` for canonical `rs`).
* Axioms of every theorem ⊆ {propext, Classical.choice, Quot.sound}
  (`#print axioms` checked); no `sorry`/`axiom`/`native_decide`.

Effect if wired in: artifact bound
`4 + 811,077 + 6,435,489 = 7,246,570 ≤ 8,388,608` — **+1,142,038 B of slack**
(was 0), which covers qvV3 (+75–112 KB) many times over.

## Blocked: the hint body is pinned by the Good semantics (found during integration)

Wiring the compact body into `hintOfE`/`prepBody` is **not a wire codec**: the
hint body is protocol-committed data.

* `Good.lean:54` (`HeaderSemanticsV3.body`): `h.body = u32 0 ++
  encodeReceipts m.result.outgoing`, and `HeaderSemanticsV3.encoded`
  (`Good.lean:56`) pins `encodedMerkleRoot … h.body = (H.encodedMerkleRoot,
  H.encodedLength)` — the chunk header's receipts-bucket commitment, computed
  by nearcore over the *native* borsh bytes.  A compact body would fail the
  EMR check for every honest claim.
* The rebuild route (hint carries compact refunds; `prepBody` rebuilds the
  native bucket via `bodyOf ∘ decodeBodyC` — decode determinism is exactly
  what `HintCompact` proves, and EMR-over-rebuilt is a strict refinement of
  EMR-over-raw, so soundness is preserved) requires amending
  `HeaderSemanticsV3` and re-proof through the whole Link chain
  (`Link{Main,Fwd,Witness,Hdr,Claim,Implicit,Exec}`, `Rcpt/Link/*` — 13
  soundness-critical files).
* Measured hints on real fixtures are 16–155 B; the bound term matters only
  for adversarial A1-max claims.  Amending the soundness chain days before
  signing for a bound-side saving is the wrong risk trade.

**Disposition.** `HintCompact.lean` stays as proved machinery — the canonical
refund invariants, decode determinism and exact length accounting are the
prerequisite for the future `GoodV3` amendment (compact hint + rebuilt-native
EMR), which the assembly/link lane can take up with lead sign-off, ideally
post-signing.  This lane does **not** change `GoodV3`, `prepBody` or
`hintOfE`.

## Integration checklist (the future GoodV3 amendment; for the assembly lane)

1. Amend `HeaderSemanticsV3` (`Good.lean`): `body : h.body = compactBodyOf
   m.result.outgoing`; keep `encoded` over the **rebuilt native** bytes
   `bodyOf (decodeBodyC h.body) = …` (well-defined by decode determinism;
   equals the native bucket by `compactRefund_encode`/`decodeBodyC_compactBodyOf`).
2. Spec: move `compactRefund`/`compactBodyOf`/`pCRefund`/`decodeBodyC` next to
   `pRefund`/`decodeBody` in `PrepD0.lean`; `hintOfE` emits compact;
   `prepBody` parses compact and rebuilds native for the EMR/`Prep.body`.
   Redefine `Hint.empty := ⟨0, compactBodyOf []⟩`.
3. `ReceiptWellformed.lean`: `NativeValid.body_decodes` → compact variant via
   `applyNewChunk_outgoing_canonical`.
4. `PrepBodyComplete.nativeHint` → `⟨n, compactBodyOf outgoing⟩`.
5. `NativePreparedBody.accepted_native_body_bound` → `≤ 8 + 181·4481 = 811,069`
   via `compactReceipts_length_le` + the receipt bound.
6. `RenderV3Header.nativeHint_bounds`, `NearAdmission.v3MaxHintBytes := 811,077`.
7. Rust `hint.rs`/`prep.rs`; re-record proofs; full negative suite.

Explicitly out of scope here (need protocol/numerics work or other lanes):
digest width 64→32 B (MMCS/Bcs format change, ROM-binding stays perfect —
candidate post-signing), P6 Johnson-regime queries (blocked on
correlated-agreement formalization), width cuts / table merges (AIR lanes,
quantified in STATUS-V3-SIZE §4 lever 4/5), arity 16 after alignment
(parameter change + L7 numerics).
