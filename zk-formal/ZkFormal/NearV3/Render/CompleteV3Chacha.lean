import ZkFormal.NearV3.Render.CompleteV3
import ZkFormal.NearV3.Render.ChachaBusBalance

/-!
# ZkFormal.NearV3.Render.CompleteV3Chacha — `ChachaSideV3` proved, `CompleteV3Stmt` unconditional

`ChachaSideV3` (`Render/CompleteV3.lean`, lane v3-render-sched) from lane v3-render-chacha's
`chacha_buses_balanced` (`Render/ChachaBusBalance.lean`): its renders `r8 r9 r10` and the balance of
buses 45–50 for every bundle carrying them with table 13 = `procTraceV3 (bs.map NativeBlock.run)`.
`ChachaSideV3`'s extra premises (`GrantWit`, `NatRes`, the instance-0 forwarding pin) are not needed.

* **`chachaSideV3 : ChachaSideV3`**;
* **`completeV3 : CompleteV3Stmt`** (`completeV3_of_chacha chachaSideV3`).
-/
set_option autoImplicit false
namespace ZkFormal.NearV3.Assembly

/-- **The ChaCha side of the honest render, proved.** -/
theorem chachaSideV3 : ChachaSideV3 := by
  intro cb wb A bs hc _ _ hctx _
  obtain ⟨_, r8, r9, r10, _, _, _, _, _, _, hbal⟩ := chacha_buses_balanced A hc hctx
  exact ⟨r8, r9, r10, hbal⟩

/-- **The completeness obligation of the D0a certificate, proved.** -/
theorem completeV3 : CompleteV3Stmt := completeV3_of_chacha chachaSideV3

end ZkFormal.NearV3.Assembly
