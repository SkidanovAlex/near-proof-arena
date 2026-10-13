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

Effect once wired into the admission: artifact bound
`4 + 811,077 + 6,435,489 = 7,246,570 ≤ 8,388,608` — **+1,142,038 B of slack**
(was 0), which covers qvV3 (+75–112 KB) many times over.

## Integration checklist (next commit of this lane; no assumption changes)

1. `spec/lean/v3/NearSpecV3/PrepD0.lean`: move `compactRefund`/`compactBodyOf`/
   `pCRefund`/`decodeBodyC` next to `pRefund`/`decodeBody` (spec is where
   `prepBody` lives); `hintOfE` emits `compactBodyOf` (native `bodyOf` stays
   for reference); `prepBody` parses with `decodeBodyC`.
2. `zk-formal/ZkFormal/NearV3/Rcpt/Candidates/NativePreparedBody.lean`:
   `accepted_native_body_bound` → compact variant via
   `HintCompact.compactHint_length_le` (canonical premise supplied by
   `applyNewChunk_outgoing_canonical`, already imported there transitively).
3. `zk-formal/ZkFormal/NearV3/Assembly/RenderV3Header.lean`:
   `nativeHint_bounds` re-instantiated on the compact hint.
4. `zk-formal/ZkFormal/NearV3/Assembly/NearAdmission.lean`:
   `v3MaxHintBytes` → `811,077` (the `decide` re-checks); certificate
   specialization unchanged otherwise.
5. Rust: `examples/np-udr-stark-v2/src/v3/{hint.rs,prep.rs}` emit/parse the
   compact body; `conformance/run-v2.sh` §5 byte-diffs against the Lean dump.
6. Re-record the three real proofs (`PROVE_V3=1`, ~750 s each under the
   wrapper) and re-run `np-lean-verify-v3` + negatives; `cargo fmt/clippy/test`;
   `make pin-check`.

Explicitly out of scope here (need protocol/numerics work or other lanes):
digest width 64→32 B (MMCS/Bcs format change, ROM-binding stays perfect —
candidate post-signing), P6 Johnson-regime queries (blocked on
correlated-agreement formalization), width cuts / table merges (AIR lanes,
quantified in STATUS-V3-SIZE §4 lever 4/5), arity 16 after alignment
(parameter change + L7 numerics).
