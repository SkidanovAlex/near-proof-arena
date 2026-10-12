import ZkFormal.NearV3.Assembly.RenderV3RcptTrieSide
import ZkFormal.NearV3.Assembly.RcptNativeShaLengths
import ZkFormal.NearV3.Assembly.Compute
import ZkFormal.NearV3.Assembly.ReceiptWellformed
import ZkFormal.NearV3.Assembly.PrepFacts

/-!
# `TrieSide.SizeBudget A` holds for every accepted witness

The size table (`sizeV3`, table 21) checks `OVH + x_0 + x_1 + x_2 ≤ 8,388,608` with
`x_0` / `x_1` the honest non-duplicate node / value bytes and `x_2 = srcpSize (blocksOfProofs A.srcps)`,
every prepared source occurrence charged `L + 33·|path|`, duplicates included.

`L = |u64 to_shard ‖ borsh(receipts)| = 12 + Σ_r |r.encode|`, so (`srcpSize_eq`)

  `x_2 = Σ_occ (12 + 33·|path|) + Σ_{r ∈ appliedReceipts} |r.encode|`

because the occurrences' receipt lists are exactly the applied lists (`acceptedSrcp_rcl`,
`lists_applied`; A2 makes the routing filter the identity).  Hence (`srcpSize_le`)

  `x_2 ≤ 1984·(12 + 33·32) + 4481·347 = 2,118,912 + 1,554,907 = 3,673,819`

(`≤ 1984` occurrences, A10 paths `≤ 32`, `≤ 4481` applied receipts by the A1 compute bound, every
well-formed receipt `≤ 347` bytes).  With `OVH = 0` (`A.pub` packs overhead 0) and
`x_0 + x_1 ≤ 2,000,000` (the premise of `SizeBudget`) the total is `≤ 5,673,819 < 8,388,608`
(`sizeBudget`), so `rcpt_trie_side A A.sizeBudget` has no size premise left.
No witness accounting is needed: duplicate occurrences carry no receipts' worth of bytes beyond
the applied receipts themselves (each applied receipt is charged once per occurrence that lists it,
and the applied list is the concatenation of the occurrences' lists).
-/

namespace ZkFormal.NearV3.Assembly.AcceptedV3
open NearSpec NearSpecV3 ZkFormal.Near Render Render.SrcpGen

variable {cb wb : Bytes} (A : AcceptedV3 cb wb)

/-- The source-table size charge of one compiled proof. -/
theorem blockOfProof_size (root : Bytes) (dup : Bool) (j q : Nat) (e : ProofEntry) :
    (blockOfProof root dup j q e).L + 33 * (blockOfProof root dup j q e).path.length =
      12 + 33 * e.proof.path.length + (e.receipts.map fun r => r.encode.length).sum := by
  simp only [blockOfProof, proofItems_length, List.length_append, Render.encodeReceipts_length]
  simp [u64, leN]
  omega

theorem srcpSize_eq (xs : List ProofInput) :
    srcpSize (blocksOfProofs xs) =
      (xs.map fun x => 12 + 33 * x.entry.proof.path.length).sum +
        ((xs.map fun x => x.entry.receipts).flatten.map fun r => r.encode.length).sum := by
  have hm : (blocksOfProofs xs).map (fun B => B.L + 33 * B.path.length) =
      xs.map fun x => 12 + 33 * x.entry.proof.path.length + (x.entry.receipts.map fun r => r.encode.length).sum := by
    apply List.ext_getElem (by simp [blocksOfProofs])
    intro i h1 h2
    simp only [blocksOfProofs, List.getElem_map, List.getElem_ofFn]
    exact blockOfProof_size _ _ _ _ _
  unfold srcpSize
  rw [hm, List.map_flatten]
  clear hm
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, List.flatten_cons, List.sum_append] at ih ⊢; omega

/-- The occurrences' receipt lists are the applied receipts. -/
theorem srcps_receipts : (A.srcps.map fun x => x.entry.receipts).flatten = appliedReceipts A.k A.w := by
  rw [← A.lists_applied]
  have h := acceptedSrcp_rcl A.p A.w (A.m.ctx A.k)
  unfold AcceptedV3.srcps
  rw [h, ← List.map_flatten]
  rfl

/-- **The source table's size charge** (duplicates included) is at most `3,673,819`. -/
theorem srcpSize_le : srcpSize (blocksOfProofs A.srcps) ≤ 1984 * (12 + 33 * 32) + 4481 * 347 := by
  rw [srcpSize_eq, srcps_receipts]
  have hn : A.srcps.length ≤ 1984 := by
    have h := (Rcpt.Candidates.DedupCompile.relD0a_inputs A.rel A.hp A.hf A.hd).2.1
    rw [A.srcps_length]
    simpa using h
  have h1 : (A.srcps.map fun x => 12 + 33 * x.entry.proof.path.length).sum ≤ A.srcps.length * (12 + 33 * 32) :=
    TrieShaTwo.sum_map_le_mul _ _ _ (fun x hx => by have := A.srcpDepth x hx; unfold Dp0 at this; omega)
  have hwf := appliedReceipts_wf (k := A.k) A.hd
  have h2 : ((appliedReceipts A.k A.w).map fun r => r.encode.length).sum ≤
      (appliedReceipts A.k A.w).length * 347 :=
    TrieShaTwo.sum_map_le_mul _ _ _ (fun r hr => RcptSkeleton.native_receipt_encoded_bound r (hwf r hr))
  have hg : A.k.slotB2.gasLimit ≤ maxGasLimitD0 := by
    simpa only [a1, A.hk, decide_eq_true_eq] using A.rel.2.1
  have h3 : (appliedReceipts A.k A.w).length ≤ 4481 := applyNewChunk_receipt_bound A.hm.run hg
  have h4 := Nat.mul_le_mul_right (12 + 33 * 32) hn
  have h5 := Nat.mul_le_mul_right 347 h3
  omega

/-- `A.pub` packs witness overhead `0`. -/
theorem pub_ovhNat : ovhNat A.pub = 0 :=
  Public.prepared_ovhNat A.p 0 (prepD0_roots A.hp) (by decide)

/-- **`SizeBudget A` holds for every accepted witness.** -/
theorem sizeBudget : TrieSide.SizeBudget A := by
  apply TrieSide.sizeBudget_of_coarse
  have h := A.srcpSize_le
  rw [A.pub_ovhNat]
  omega

end ZkFormal.NearV3.Assembly.AcceptedV3
