import ZkFormal.NearV3.Rcpt.Link.RcptCore
import ZkFormal.NearV3.Rcpt.Link.AcctSlots
import ZkFormal.NearV3.Rcpt.Link.GasPub
import ZkFormal.NearV3.Assembly.LinkRidBytes
import ZkFormal.NearV3.Assembly.LinkFields

/-!
# ZkFormal.NearV3.Rcpt.Link.RcptHolds — `mainRun_of_records` with the trace-derivable premises discharged

From the hypotheses of `LinkCoreV3Stmt` (`prepD0`, the size bound, `HoldsP nearAirV3`, the
records' well-formedness and exact traffic) and the receipt count, **`mainRun_of_holdsP`**
discharges in `mainRun_of_records`: the `MEM` chain (`memHyp_of'`), the receipt-encoding and
public gas-price byte facts, the gas-price identity (`gasPrice_pub`) and the native
forwarding / compute facts (`prepBody_fwd`).  What remains is quantified explicitly:

* `RecBytes` — three byte facts (acct pre bytes, burnt amounts, refund amounts);
* the trie / scheduler interface `MainTrieLink` at `ctx = pc.ctxB2`, the queue reads, the refund
  identity and the per-shard demand check against the scheduler grants.
-/

namespace ZkFormal.NearV3.RcptLink

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2 ZkFormal.Near ZkFormal.Near.Link NearSpec
  NearSpec.TransferV1 NearSpecV3 ZkFormal.NearV3.Assembly

/-- The byte facts of `RecHyp` not yet derived from the trace. -/
structure RecBytes (ls : RcptV3Vs) (as : List AcctV) : Prop where
  preB : ∀ a ∈ as, Bytes8 a.pre
  burntB : ∀ x ∈ flatR ls, Bytes8 x.burnt
  ramtB : ∀ x ∈ flatR ls, x.hr = true → Bytes8 x.ramt

/-- **The receipt core of `m.Valid.run` from the trace.** -/
theorem mainRun_of_holdsP {cb : Bytes} {h : Hint} {p : Prep} {oh : Nat} {tr : Trace Fp}
    {r : V3Records} (hp : prepD0 cb h = .ok p)
    (hsz : (ZkFormal.NearV3.Public.preparedBytes p oh).length < ZkFormal.Algebra.P)
    (hH : HoldsP nearAirV3 (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr)
    (T : V3RecordsTraffic (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) tr r)
    (W : V3RecordsWf (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) r)
    (hn : h.n = (flatR r.lists).length) (B : RecBytes r.lists r.accts) :
    ∃ pc refunds, prepClaim cb = .ok pc ∧ decodeBody h.body = .ok refunds ∧
      ∀ (base : Nat → Bytes) (Tf : (Nat → Bytes) → PTrie) (pre mid : PTrie) (so : SchedOut)
        (v : Qv.MainValues),
        MainTrieLink r.lists r.accts base Tf pc.ctxB2 pre mid so →
        v.Valid →
        v.Reads pre mid (Tf ((recModel r.lists r.accts base Tf).valsAt (flatR r.lists).length)) →
        ((recModel r.lists r.accts base Tf).accAt pc.ctxB2 (flatR r.lists).length).refunds = refunds →
        (∀ s ∈ statusShards pc.ctxB2, demand pc.ctxB2 refunds s ≤ so.grant pc.ctxB2.own s) →
        applyNewChunk prims pc.ctxB2 pre ((rv r.lists).map RcptV.toReceipt) =
          .ok ((recModel r.lists r.accts base Tf).mainOut pc.ctxB2) := by
  obtain ⟨pc, hc, hb, hgp⟩ := gasPrice_pub oh hp
  obtain ⟨refunds, F⟩ := prepBody_fwd hb
  refine ⟨pc, refunds, hc, F.body, ?_⟩
  intro base Tf pre mid so v L hv hR hrf hdem
  have H : RecHyp _ r.lists r.accts :=
    { mem := memHyp_of' hH T W
      wf := W.lists
      acct := W.accts
      preB := B.preB
      encB := LinkRidBytes.encBytes hp hsz hH T W
      burntB := B.burntB
      ramtB := B.ramtB
      bgpB := fun y hy => by
        simp only [pubBytes, List.mem_map, List.mem_range] at hy
        obtain ⟨i, -, rfl⟩ := hy
        exact pubNat_pubOf_lt _ _ }
  exact mainRun_of_records H hgp L hv hR F hn hrf hdem

end ZkFormal.NearV3.RcptLink
