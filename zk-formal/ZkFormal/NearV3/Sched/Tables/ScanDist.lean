import ZkFormal.Chacha.Local
import ZkFormal.NearV3.Sched.Tables.Scan
import ZkFormal.NearV3.Sched.Tables.ScanDistDefs

/-!
# ZkFormal.NearV3.Sched.Tables.ScanDist — `ssdV3`: the scan and distribute rows in one table

Width cut B (STATUS-V3-SCHED §12). Row kinds (one-hot, `act = kP + kS + kSh + kGH + kC`):
scan param rows `kP` and request rows `kS` (`Tables/Scan.lean`), distribute shard rows `kSh`,
grid headers `kGH` and cells `kC` (`Tables/Dist.lean`). Sections: every scan section (per τ
with requests: a param row, 20 rows per request), then every distribute section (per τ: 2n
shard rows, then n × (header + n cells)), then zero padding. Row 0, when active, is a param row
or a sender shard row; a scan row is followed by a scan row, a sender shard row with
`pos = kp = 0`, or padding; a distribute row by a distribute row or padding.

Columns: the physical layout is `Tables/Dist.lean`'s (width 119); the scan names point into it.

Interactions (10):

| # | bus | mult | message |
|---|---|---|---|
| 0 | `SPAR` recv | `kP + fQ + kSh + kC` | `(τ, kP + 2kS + 3kSh + 4kC, f₀ … f₈)` — tags 1 (scan params), 2 (raw request), 3 (shard), 4 (link) |
| 1, 2 | `SINC` send | `us0`, `us1` | scan increases |
| 3 | `SPUSH` send | `re` | scan initial push |
| 4 | `SOP` send | `re + kSh` | `(τ·2^14 + link/adr, cid + kS, kS, key, key + bvz, 0, 0, 0)` — scan READ, distribute INIT |
| 5 | `SFIN` recv | `kSh` | budget final |
| 6 | `SCMP` send | `cg` | distribute comparisons |
| 7, 8 | `SDLX` send / recv | `dlsg`, `dlrg` | grid endpoints |
| 9 | `SDG` send | `kC` | grid grants |

`scan_sub`, `dist_sub`: each family's constraint list is contained in the merged one, so the
row views (`View/Scan*`, `View/Dist`) are stated for the family lists and apply to `ssdV3`.
-/

namespace ZkFormal.NearV3.Sched.ScanDist

open ZkFormal.Air ZkFormal.Chacha.Table.E
open ZkFormal.Chacha.Table (boolC)

/-! ## The family constraint lists are contained in the merged list -/

theorem sharedBool_sub : ∀ x ∈ Scan.sharedBool, x ∈ Dist.boolCols := by decide

theorem shared_sub : ∀ e ∈ Scan.shared, e ∈ Dist.constraints := by
  intro e he
  unfold Scan.shared at he
  simp only [List.mem_append, List.mem_map] at he
  unfold Dist.constraints Dist.cKind
  rcases he with (⟨x, hx, rfl⟩ | h) | h
  · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem (sharedBool_sub x hx))))))
  · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_right _ h))))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · exact List.mem_append_right _ (List.mem_cons_self ..)
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))

theorem scan_sub : ∀ e ∈ Scan.constraints, e ∈ constraints := by
  intro e he
  unfold Scan.constraints at he
  rcases List.mem_append.1 he with h | h
  · exact List.mem_append_left _ (shared_sub e h)
  · exact List.mem_append_right _ h

theorem dist_sub : ∀ e ∈ Dist.constraints, e ∈ constraints :=
  fun _ h => List.mem_append_left _ h

open ZkFormal.Chacha in
theorem local_scan {tr : Trace ZkFormal.Algebra.Fp} {t : Nat} {pub : List ZkFormal.Algebra.Fp}
    (h : Local constraints tr t pub) : Local Scan.constraints tr t pub :=
  fun r hr e he => h r hr e (scan_sub e he)

open ZkFormal.Chacha in
theorem local_dist {tr : Trace ZkFormal.Algebra.Fp} {t : Nat} {pub : List ZkFormal.Algebra.Fp}
    (h : Local constraints tr t pub) : Local Dist.constraints tr t pub :=
  fun r hr e he => h r hr e (dist_sub e he)

end ZkFormal.NearV3.Sched.ScanDist
