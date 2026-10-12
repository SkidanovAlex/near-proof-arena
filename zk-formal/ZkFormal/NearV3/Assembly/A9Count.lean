import ZkFormal.NearV3.Assembly.ExtractV3
import ZkFormal.Chacha.Rng.WordCount
import ZkFormal.Chacha.Link

/-!
# ZkFormal.NearV3.Assembly.A9Count — the A9 word counter of `nearAirV3` (soundness view)

Table 9 of `nearAirV3` is `Rng.Table.table22`, which carries the running count of its active
rows and the last-row range check of `W0 − count` (`Rng.Table.cW0`).

* **`rngActive_le_W0`**: every trace accepted by `nearAirV3` has at most `W0 = 770,000` active
  rows in table 9 (one per drawn ChaCha word, `Rng.activeRows_le`).
* `chachaWords_le_of_link`: A9 (`chachaWords cb w ≤ NearSpecV3.W0`) from the link
  "native draws ≤ active rows of table 9" (`A9Link`, open).
-/

namespace ZkFormal.NearV3.Assembly

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2

theorem W0_eq_spec : ZkFormal.Chacha.Rng.Table.W0 = NearSpecV3.W0 := rfl

theorem rng_tab : nearAirV3.tables[T_RNG]! =
    ZkFormal.Chacha.Rng.Table.table22 ZkFormal.NearV3.Sched.B_SCHACHA ZkFormal.NearV3.Sched.B_SGEN := rfl

theorem rng_lt : T_RNG < nearAirV3.tables.length := by decide

/-- **A9 in `nearAirV3`**: at most `W0` active rows (drawn words) in table 9. -/
theorem rngActive_le_W0 {pub : List Fp} {tr : Trace Fp} (hH : HoldsP nearAirV3 pub tr) :
    ZkFormal.Chacha.Rng.activeRows tr T_RNG ≤ NearSpecV3.W0 := by
  have hL := ZkFormal.Chacha.local_of_holdsP hH rng_lt
  rw [rng_tab] at hL
  have hb := hH.logBound T_RNG rng_lt
  rw [← ZkFormal.Chacha.tables_get rng_lt, rng_tab] at hb
  have h22 : tr.height T_RNG ≤ 2 ^ 22 := Nat.pow_le_pow_right (by decide) hb.2
  have h1 : 1 ≤ tr.height T_RNG := Nat.one_le_two_pow
  exact ZkFormal.Chacha.Rng.activeRows_le hL h22 h1

/-- **The remaining A9 link** (open): the words drawn by all native scheduler runs of the
reconstruction are at most the active rows of table 9. -/
def A9Link (cb : NearSpec.Bytes) (w : NearSpec.Bytes) (tr : Trace Fp) : Prop :=
  NearSpecV3.chachaWords cb w ≤ ZkFormal.Chacha.Rng.activeRows tr T_RNG

/-- **`RestFieldsV3.chachaWords` from the link.** -/
theorem chachaWords_le_of_link {pub : List Fp} {tr : Trace Fp} (hH : HoldsP nearAirV3 pub tr)
    {cb w : NearSpec.Bytes} (hl : A9Link cb w tr) : NearSpecV3.chachaWords cb w ≤ NearSpecV3.W0 :=
  Nat.le_trans hl (rngActive_le_W0 hH)

end ZkFormal.NearV3.Assembly
