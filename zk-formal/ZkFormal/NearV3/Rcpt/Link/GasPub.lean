import ZkFormal.NearV3.Rcpt.Link.PrepFwd
import ZkFormal.NearV3.Assembly.RcptGasPriceBound
import ZkFormal.Near.Link.EncLemmas

/-!
# ZkFormal.NearV3.Rcpt.Link.GasPub — the public gas-price bytes are the context's gas price

`prepD0` publishes `u128 p.hdr.gasPrice` at `PH_GP` and `p.hdr.gasPrice = pc.ctxB2.gasPrice
< 2^128` (`RcptSkeleton.prepared_gasPrice_byte`, `prepClaim_gasPrice`, `prepBody_gasPrice`,
`prepClaim_gasPrice_bound`).  **`gasPrice_pub`**: `pc.ctxB2.gasPrice = leN' (pubBytes pub PH_GP 16)`
(the `hgp` premise of `mainRun_of_records`), and the public gas-price bytes are bytes.
-/

namespace ZkFormal.NearV3.RcptLink

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near NearSpec NearSpecV3 ZkFormal.NearV3.Sched
  ZkFormal.NearV3.Assembly.RcptSkeleton

theorem pubNat_prepared (p : Prep) (oh : Nat) (i : Nat) :
    pubNat (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) i =
      ((ZkFormal.NearV3.Public.preparedBytes p oh).getD i 0).toNat := by
  unfold pubNat
  rw [ZkFormal.NearV3.Public.pub_getD]
  change (Fp.ofNat (_ : UInt8).toNat).toNat = _
  rw [Fp.toNat_ofNat, Nat.mod_eq_of_lt (by
    have := ((ZkFormal.NearV3.Public.preparedBytes p oh).getD i 0).toNat_lt
    unfold ZkFormal.Algebra.P; omega)]

/-- **The public gas price.** -/
theorem gasPrice_pub {cb : Bytes} {h : Hint} {p : Prep} (oh : Nat) (hp : prepD0 cb h = .ok p) :
    ∃ pc, prepClaim cb = .ok pc ∧ prepBody pc h = .ok p ∧
      pc.ctxB2.gasPrice =
        leN' (pubBytes (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) PH_GP 16) := by
  obtain ⟨pc, hc, hb⟩ := bind_ok hp
  refine ⟨pc, hc, hb, ?_⟩
  have hroots := ZkFormal.NearV3.Assembly.prepD0_roots hp
  have hg : p.hdr.gasPrice = pc.ctxB2.gasPrice := by
    rw [prepBody_gasPrice hb, prepClaim_gasPrice hc]
  have hlt := prepD0_gasPrice_bound hp
  have hpb : pubBytes (ZkFormal.Udr.pubOf Fp (ZkFormal.NearV3.Public.preparedBytes p oh)) PH_GP 16 =
      (u128 p.hdr.gasPrice).map UInt8.toNat := by
    apply List.ext_getElem (by simp [pubBytes, u128, leN_length])
    intro i h1 h2
    have hi : i < 16 := by simpa [pubBytes] using h1
    simp only [pubBytes, List.getElem_map, List.getElem_range]
    rw [pubNat_prepared, prepared_gasPrice_byte p oh i hroots hi,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa [u128, leN_length] using hi)]
    rfl
  rw [hpb, ← hg, ZkFormal.Near.Link.leN'_eq]
  have : toBytes ((u128 p.hdr.gasPrice).map UInt8.toNat) = u128 p.hdr.gasPrice := by
    simp [toBytes, List.map_map, Function.comp_def]
  rw [this, u128, NearSpec.leNat_leN 16 _ hlt]

end ZkFormal.NearV3.RcptLink
