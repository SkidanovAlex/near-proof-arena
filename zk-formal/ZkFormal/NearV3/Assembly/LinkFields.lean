import ZkFormal.NearV3.Assembly.LinkV3
import ZkFormal.NearV3.Rcpt.Extract.V.PreparedRanges

/-!
# ZkFormal.NearV3.Assembly.LinkFields — view-level `GoodV3` fields from the records

Each lemma closes one field of `ExtFieldsV3` (`LinkCoreV3Stmt`) for the reconstruction whose
receipts are the receipt view's lists (`x.receipts = r.lists`).

* `receiptCount_of_records` — `h.n = x.applied.length`: the receipt view counts its receipts
  against the packed header's `n` (`RcptV3Wf.count`), which is the hint's `n` (`prepD0`).
-/

namespace ZkFormal.NearV3.Assembly

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 NearSpec NearSpecV3

/-- Public elements of a packed byte statement are bytes. -/
theorem pubNat_pubOf_lt (bs : List UInt8) (i : Nat) :
    ZkFormal.Near.pubNat (ZkFormal.Udr.pubOf Fp bs) i < 256 := by
  unfold ZkFormal.Near.pubNat
  rw [ZkFormal.NearV3.Public.pub_getD]
  change (Fp.ofNat (bs.getD i 0).toNat).toNat < 256
  rw [Fp.toNat_ofNat, Nat.mod_eq_of_lt (by have := (bs.getD i 0).toNat_lt; unfold ZkFormal.Algebra.P; omega)]
  exact (bs.getD i 0).toNat_lt

/-- **`receiptCount`.** -/
theorem receiptCount_of_records {cb : Bytes} {h : Hint} {p : Prep} {oh : Nat}
    {ls : ZkFormal.NearV3.RcptV3Vs} (hp : prepD0 cb h = .ok p)
    (hw : ZkFormal.NearV3.RcptV3Wf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) ls)
    (x : ExtV3) (hx : x.receipts = ls) :
    h.n = x.applied.length := by
  have hc := hw.count (fun i _ => pubNat_pubOf_lt _ _)
  rw [ZkFormal.NearV3.RcptV3Proof.prepared_receipt_count hp oh (prepD0_roots hp)] at hc
  obtain ⟨pc, -, hb⟩ := ZkFormal.NearV3.Sched.bind_ok hp
  have hn := (ZkFormal.NearV3.RcptV3Proof.prepBody_count_guard hb).1
  rw [← hn, ← hc]
  simp only [ExtV3.applied, hx, ZkFormal.NearV3.flatR, List.length_flatMap, List.length_map]

end ZkFormal.NearV3.Assembly
