import ZkFormal.NearV3.Render.Padded
import ZkFormal.NearV3.Rcpt.Render.AcctRender
import ZkFormal.NearV3.Rcpt.Render.SizeRender

/-!
# Concrete aligned generators for the small receipt-side tables (`acctV3`, `sizeV3`)

As `Render/Padded.lean`: an array-backed trace at the roll-aligned height
`padLog22 (logOf rows)`, with local constraints, the exact view traffic and the
`log % 3 = 1` residue.

Both tables need a rounded cap (`STATUS-V3-ASSEMBLY` §2, option 1):
* `acctV3`: up to `4481` accounts (A1, `max_receipts`) give `16 · 4481 = 71,696 > 2^16`
  rows, so the natural cap `17` rounds to `19`;
* `sizeV3`: four rows, natural cap `2` rounds to `4`.
The views are cap-parametric (`acctV3_view_at`, `size_view_at`), so these are the caps
`nearAirV3` uses for tables 17 and 21.
-/
namespace ZkFormal.NearV3.Render
open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Air ZkFormal.Algebra ZkFormal.Size

/-- The roll-aligned cap of `acctV3` in `nearAirV3`. -/
def acctCapV3 : Nat := 19

/-- The roll-aligned cap of `sizeV3` in `nearAirV3`. -/
def sizeCapV3 : Nat := 4

def acctTraceAligned (as : List AcctV) : Trace Fp :=
  let log := padLog22 (logOf (16 * as.length))
  rowsTrace log (mkTab (2 ^ log) AcctV3.width (AcctV3Gen.cell as))

/-- **Account table completeness at the rounded height** (cap `17` rounds to `19`).
`AcctV3Ok` is what an honest witness satisfies: at least one account, `16·|as| ≤ 2^17`,
72 pre bytes `< 256` with a non-`u128::MAX` amount, 16 canonical post values, canonical
`k`/`tlast` (`acctV3Ok_wf` shows it implies the view's `AcctV3Wf`). -/
theorem acct_aligned_complete (as : List AcctV) (ok : AcctV3Ok as) (t : Nat) (pub : List Fp) :
    TableLocal { AcctV3.table with maxLog := acctCapV3 } (acctTraceAligned as) t pub ∧
    TableTraffic AcctV3.interactions (acctTraceAligned as) t pub (acctV3Traffic as) ∧
    (acctTraceAligned as).log t % 3 = 1 := by
  have hh := padded_log_fits (16 * as.length) (Nat.le_trans ok.rows (by decide))
  have hl := padded_log_le (16 * as.length) acctCapV3 (by decide) (by decide)
    (Nat.le_trans ok.rows (by decide))
  have hc : ∀ r x, r < (acctTraceAligned as).height t → x < AcctV3.width →
      (acctTraceAligned as).cell t r x = Fp.ofNat (AcctV3Gen.cell as r x) := by
    intro r x hr hx
    exact rowsTrace_mkTab _ _ _ t r x hr hx
  exact ⟨acctV3_render_local_at as ok _ t pub acctCapV3 ⟨hh.2.1, hl⟩ hh.1 hc,
    acctV3_render_traffic_at as ok _ t pub ⟨hh.2.1, hh.2.2.1⟩ hh.1 hc, hh.2.2.2⟩

/-- The honest-side hypothesis is the view's well-formedness plus byte ranges. -/
theorem acctV3Ok_wf {as : List AcctV} (ok : AcctV3Ok as) : AcctV3Wf as := by
  refine ⟨⟨fun h => by have := ok.len_pos; rw [h] at this; exact absurd this (by decide),
    fun a ha => ⟨(ok.pre a ha).1, (ok.post a ha).1, (ok.canon a ha).1, (ok.canon a ha).2⟩,
    fun a ha _ => (ok.pre a ha).2.2, fun a ha x hx => ?_⟩, ok.rows⟩
  rcases List.mem_append.1 hx with hx | hx
  · have := (ok.pre a ha).2.1 x hx; unfold ZkFormal.Algebra.P; omega
  · exact (ok.post a ha).2 x hx

def sizeTraceAligned (pub : List Fp) (v : SizeV) : Trace Fp :=
  rowsTrace sizeCapV3 (mkTab (2 ^ sizeCapV3) SizeV3.width (SizeGen.cell pub v))

/-- **Size table completeness at the rounded height** (cap `2` rounds to `4`: rows `0..2`
carry the three totals, rows `3..15` are padding).  `SizeOk` is the pair of natural size
bounds `checkD0` enforces (`x₀ + x₁ ≤ 3,000,000`, `OVH + Σ x ≤ 8,388,608`). -/
theorem size_aligned_complete (pub : List Fp) (v : SizeV) (ok : SizeOk pub v) (t : Nat) :
    TableLocal { SizeV3.table with maxLog := sizeCapV3 } (sizeTraceAligned pub v) t pub ∧
    TableTraffic SizeV3.interactions (sizeTraceAligned pub v) t pub (sizeTraffic v) ∧
    (sizeTraceAligned pub v).log t % 3 = 1 := by
  have hc : ∀ r x, r < (sizeTraceAligned pub v).height t → x < SizeV3.width →
      (sizeTraceAligned pub v).cell t r x = Fp.ofNat (SizeGen.cell pub v r x) := by
    intro r x hr hx
    exact rowsTrace_mkTab _ _ _ t r x hr hx
  have hlog : (sizeTraceAligned pub v).log t = 4 := rfl
  have hH : 4 ≤ (sizeTraceAligned pub v).height t := by unfold Trace.height; rw [hlog]; decide
  exact ⟨size_render_local_at pub v ok _ t sizeCapV3 ⟨by rw [hlog]; decide, by rw [hlog]; decide⟩ hc,
    size_render_traffic_at pub v _ t hH hc, by rw [hlog]⟩

end ZkFormal.NearV3.Render
