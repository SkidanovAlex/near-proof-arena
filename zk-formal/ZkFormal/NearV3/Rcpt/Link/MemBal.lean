import ZkFormal.NearV3.Assembly.LinkRids
import ZkFormal.Near.Link.MemBus

/-!
# ZkFormal.NearV3.Rcpt.Link.MemBal — the `MEM` bus of `nearAirV3` in record form

`MEM` users are `rcptV3` (16) and `acctV3` (17) only (`RcptViewV3.nearAir_mem_tables`), and no
prepared public segment uses it.  With v1's message shapes (`Near.Link.wrMsg`/`rdMsg`/`awMsg`/
`arMsg`) over the flattened receipts `flatR ls` (global index `r`):

* `rcptSends3_mem`, `rcptRecvs3_mem` — the receipt view's `MEM` traffic;
* **`mem_bal`** — `memW3 ~ memR3` as `Fp` images, from `HoldsP` and the exact traffic.
-/

namespace ZkFormal.NearV3.RcptLink

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.NearV3.Assembly

open ZkFormal.Near.Link (wrMsg rdMsg awMsg arMsg)

/-- Writes: receipt `r` writes `(kslot, r + 1)`, every acct record opens `(k, 0)`. -/
def memW3 (ls : RcptV3Vs) (as : List AcctV) : List Msg :=
  ((flatR ls).zipIdx.flatMap fun p => (List.range 16).map (wrMsg p.1.toRcptV p.2)) ++
    as.flatMap fun a => (List.range 16).map (awMsg a)

/-- Reads: receipt `r` reads `(kslot, tprev)`, every acct record closes `(k, tlast)`. -/
def memR3 (ls : RcptV3Vs) (as : List AcctV) : List Msg :=
  ((flatR ls).zipIdx.flatMap fun p => (List.range 16).map (rdMsg p.1.toRcptV)) ++
    as.flatMap fun a => (List.range 16).map (arMsg a)

theorem rcptSends3_mem (pub : List Fp) (ls : RcptV3Vs) :
    rcptSends3 pub ls B_MEM =
      (flatR ls).zipIdx.flatMap fun p => (List.range 16).map (wrMsg p.1.toRcptV p.2) := by
  simp only [rcptSends3, show B_MEM ≠ B_BYTES by decide, show B_MEM ≠ B_RCL by decide,
    ite_false, List.nil_append]
  have hs : ∀ (j : Nat) (p : Nat × Nat × RcptE), rSends pub (flatR ls) j p.1 p.2.1 p.2.2 B_MEM =
      (List.range 16).map (wrMsg p.2.2.toRcptV p.1) := by
    intro j p
    simp [rSends, B_MEM, B_BYTES, B_KEYNIB, wrMsg]
  simp only [hs]
  exact LinkRids.located_flat ls (fun r x => (List.range 16).map (wrMsg x.toRcptV r))

theorem rcptRecvs3_mem (ls : RcptV3Vs) :
    rcptRecvs3 ls B_MEM =
      (flatR ls).zipIdx.flatMap fun p => (List.range 16).map (rdMsg p.1.toRcptV) := by
  simp only [rcptRecvs3]
  have hs : ∀ (p : Nat × Nat × RcptE), rRecvs p.1 p.2.2 B_MEM =
      (List.range 16).map (rdMsg p.2.2.toRcptV) := by
    intro p
    simp [rRecvs, B_MEM, B_DIGEST, B_FINAL, rdMsg]
  simp only [hs]
  exact LinkRids.located_flat ls (fun _ x => (List.range 16).map (rdMsg x.toRcptV))

theorem acctV3Sends_mem (as : List AcctV) :
    acctV3Sends as B_MEM = as.flatMap fun a => (List.range 16).map (awMsg a) := by
  simp [acctV3Sends, B_MEM, B_VBYTES, B_BYTES]; rfl

theorem acctRecvs_mem' (as : List AcctV) :
    acctRecvs as B_MEM = as.flatMap fun a => (List.range 16).map (arMsg a) := by
  simp [acctRecvs]; rfl

/-- **The `MEM` balance** in record form. -/
theorem mem_bal {pub : List Fp} {tr : Trace Fp} {r : V3Records} (hH : HoldsP nearAirV3 pub tr)
    (T : V3RecordsTraffic pub tr r) :
    ((memW3 r.lists r.accts).map Msg.toFp).Perm ((memR3 r.lists r.accts).map Msg.toFp) := by
  apply List.perm_iff_count.mpr
  intro m
  have h := bal_users hH (b := B_MEM) (U := [Assembly.T_RCPT, Assembly.T_ACCT]) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) m
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at h
  rw [show isAt Assembly.T_RCPT = RcptV3.interactions from rfl, tcnt_of_traffic T.lists,
    tcnt_of_traffic T.lists, show isAt Assembly.T_ACCT = AcctV3.interactions from rfl,
    tcnt_of_traffic T.accts, tcnt_of_traffic T.accts] at h
  simp only [tcnt, ite_true, Bool.false_eq_true, ite_false, rcptTraffic3, acctV3Traffic] at h
  rw [rcptSends3_mem, rcptRecvs3_mem, acctV3Sends_mem, acctRecvs_mem'] at h
  simpa only [memW3, memR3, List.map_append, List.count_append] using h

end ZkFormal.NearV3.RcptLink
