import ZkFormal.NearV3.Render.PaddedCongr
import ZkFormal.Chacha.Complete.All
import ZkFormal.Chacha.Rng.Complete.All
import ZkFormal.Chacha.Shuffle.Complete.All
import ZkFormal.NearV3.Sched.Ids

/-!
# Aligned ChaCha-lane generators (`nearAirV3` tables 8 `chachaV3`, 9 `rngV3`, 10 `shufV3`)

Array-backed honest traces of the lane-`v3-chacha` generators (`Chacha.Gen`,
`Chacha.Rng.Gen`, `Chacha.Shuffle.Gen`) at the rounded height `padLog22 (logOf rows)`.
Entries are exactly those of the ChaCha completeness/soundness statements (`Gen.Req`,
`Rng.Gen.Call`, `Shuffle.Gen.SInst`); the traffic is the exact honest traffic of
`Chacha/*/Complete` as natural-number messages (`natMsgs`, exact on `Fp`).

**Caps.** The aligned height is `≡ 1 (mod 3)`, so under the current caps of `nearAirV3`
(`chacha` 21, `rng` 20, `shuf` 20) an aligned honest table fits iff its rows are `≤ 2^19`.
At the A9 word bound `W0 = 770,000` the honest rows exceed `2^19` (`Sched.Complete.lane_W0`:
`chachaRows < 2^22`, `genRows < 2^20`, `shufRows < 2^22`), so

* `chacha_aligned_complete` / `rng_aligned_complete` / `shuf_aligned_complete` hold at the exact
  `nearAirV3` tables under the explicit condition `rows ≤ 2^19`;
* `chacha_aligned_complete22` / `rng_aligned_complete22` hold for every honest instance that
  fits `2^22` (which A9 gives), at the table with `maxLog := 22` — the cap these two tables
  need in `nearAirV3`;
* the shuffle has no `22` variant: its completeness (and soundness, `Shuffle.Contract`) is
  proved for heights `≤ 2^20` only (the row counter and timestamps are 20-bit).
-/
namespace ZkFormal.NearV3.Render
open ZkFormal.Near ZkFormal.Near.Render ZkFormal.Air ZkFormal.Algebra ZkFormal.Size
open ZkFormal.NearV3.Sched

/-- `TableLocal` from its four parts at an explicit cap. -/
theorem tableLocal_mk {T : ZkFormal.Air.Table} {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (h1 : 1 ≤ tr.log t) (h2 : tr.log t ≤ T.maxLog)
    (hc : ∀ r, r < tr.height t → ∀ e ∈ T.constraints, e.eval tr t r pub = 0)
    (hb : ∀ r, r < tr.height t → ∀ i ∈ T.interactions, ∀ b ∈ i.mult,
      b.eval tr t r pub = 0 ∨ b.eval tr t r pub = 1) : TableLocal T tr t pub :=
  ⟨h1, h2, hc, hb⟩

/-! ## `chachaV3` (table 8) -/

theorem chacha_cell_ge (reqs : List Chacha.Gen.Req) (r c : Nat) (hc : Chacha.Table.width ≤ c) :
    Chacha.Gen.honestCell reqs r c = 0 := by
  simp only [Chacha.Table.width] at hc
  unfold Chacha.Gen.honestCell Chacha.Gen.rowCell
  repeat rw [if_neg (by omega)]

def chachaTraceAligned (reqs : List Chacha.Gen.Req) : Trace Fp :=
  let log := padLog22 (logOf (86 * reqs.length))
  rowsTrace log (mkTab (2 ^ log) Chacha.Table.width (Chacha.Gen.honestCell reqs))

/-- The `chachaV3` traffic: provides `expected reqs` on `B_SCHACHA`, receives nothing. -/
def chachaTraffic (reqs : List Chacha.Gen.Req) : Traffic :=
  ⟨fun b => if b = B_SCHACHA then natMsgs (Chacha.Gen.expected reqs) else [], fun _ => []⟩

/-- Core: the aligned ChaCha trace is locally legal at every cap `≥` its height, with the
honest traffic.  Needs only the honest-request condition and `86·n ≤ 2^22`. -/
theorem chacha_aligned_core (reqs : List Chacha.Gen.Req) (hok : ∀ R ∈ reqs, Chacha.Gen.ReqOk R)
    (hrows : 86 * reqs.length ≤ 2 ^ 22) (cap : Nat)
    (hcap : padLog22 (logOf (86 * reqs.length)) ≤ cap) (t : Nat) (pub : List Fp) :
    TableLocal { Chacha.Table.table B_SCHACHA with maxLog := cap } (chachaTraceAligned reqs) t pub ∧
    TableTraffic (Chacha.Table.table B_SCHACHA).interactions (chachaTraceAligned reqs) t pub
      (chachaTraffic reqs) ∧
    (chachaTraceAligned reqs).log t % 3 = 1 := by
  have hh := padded_log_fits (86 * reqs.length) hrows
  generalize hL : padLog22 (logOf (86 * reqs.length)) = L at hh hcap
  have hlog : (chachaTraceAligned reqs).log t = L := by
    show padLog22 (logOf (86 * reqs.length)) = L; exact hL
  have hc := Chacha.Complete.chacha_completeL reqs hok hh.1 B_SCHACHA
  have hl : (Chacha.Gen.traceAt reqs L).log t = (chachaTraceAligned reqs).log t := hlog.symm
  have hcell : ∀ r, r < (Chacha.Gen.traceAt reqs L).height t → ∀ c,
      (Chacha.Gen.traceAt reqs L).cell t r c = (chachaTraceAligned reqs).cell t r c := by
    intro r hr c
    have hr' : r < 2 ^ L := hr
    unfold chachaTraceAligned
    simp only [hL]
    rw [rowsTrace_cells L _ _ (fun r c h => chacha_cell_ge reqs r c h) t r hr' c]
    rfl
  refine ⟨tableLocal_congr_rows hl hcell
      (tableLocal_mk (show 1 ≤ L by omega) (show L ≤ cap from hcap)
        (fun r hr e he => hc.1 t pub r hr e he) (fun r hr i hi b hb => hc.2.1 t pub r hr i hi b hb)),
    tableTraffic_congr_rows hl hcell ?_, by rw [hlog]; exact hh.2.2.2⟩
  intro b m
  by_cases hb : b = B_SCHACHA
  · subst hb
    obtain ⟨h1, h2⟩ := hc.2.2 t pub m
    refine ⟨?_, ?_⟩
    · simp only [chachaTraffic, if_true, natMsgs_toFp]
      exact h1
    · exact h2
  · have hoff : ∀ i ∈ (Chacha.Table.table B_SCHACHA).interactions, i.bus ≠ b := by
      intro i hi
      obtain ⟨kk, -, rfl⟩ := List.mem_map.mp hi
      exact fun h => hb h.symm
    refine ⟨?_, ?_⟩
    · rw [tableBusCount_off_bus _ _ _ _ _ _ _ hoff,
        show (chachaTraffic reqs).sends b = [] from if_neg hb]; rfl
    · rw [tableBusCount_off_bus _ _ _ _ _ _ _ hoff]; rfl

/-- **`chachaV3` aligned completeness at the current `nearAirV3` cap (21)**, for honest
requests with at most `2^19` rows (the largest aligned height `≤ 21`). -/
theorem chacha_aligned_complete (reqs : List Chacha.Gen.Req) (hok : ∀ R ∈ reqs, Chacha.Gen.ReqOk R)
    (hrows : 86 * reqs.length ≤ 2 ^ 19) (t : Nat) (pub : List Fp) :
    TableLocal (Chacha.Table.table B_SCHACHA) (chachaTraceAligned reqs) t pub ∧
    TableTraffic (Chacha.Table.table B_SCHACHA).interactions (chachaTraceAligned reqs) t pub
      (chachaTraffic reqs) ∧
    (chachaTraceAligned reqs).log t % 3 = 1 :=
  chacha_aligned_core reqs hok (Nat.le_trans hrows (by decide)) 21
    (Nat.le_trans (padded_log_le _ 19 (by decide) (by decide) hrows) (by decide)) t pub

/-- **`chachaV3` aligned completeness at cap 22** (the cap the A9 lane needs): every honest
request list with at most `2^22` rows. -/
theorem chacha_aligned_complete22 (reqs : List Chacha.Gen.Req) (hok : ∀ R ∈ reqs, Chacha.Gen.ReqOk R)
    (hrows : 86 * reqs.length ≤ 2 ^ 22) (t : Nat) (pub : List Fp) :
    TableLocal { Chacha.Table.table B_SCHACHA with maxLog := 22 } (chachaTraceAligned reqs) t pub ∧
    TableTraffic (Chacha.Table.table B_SCHACHA).interactions (chachaTraceAligned reqs) t pub
      (chachaTraffic reqs) ∧
    (chachaTraceAligned reqs).log t % 3 = 1 :=
  chacha_aligned_core reqs hok hrows 22 (padded_log_fits _ hrows).2.2.1 t pub

/-! ## `rngV3` (table 9) -/

theorem rng_cell_ge (calls : List Chacha.Rng.Gen.Call) (r c : Nat) (hc : Chacha.Rng.Table.width ≤ c) :
    Chacha.Rng.Gen.honestCell calls r c = 0 := by
  simp only [Chacha.Rng.Table.width] at hc
  unfold Chacha.Rng.Gen.honestCell
  generalize (Chacha.Rng.Gen.honestRows calls).getD r .pad = X
  cases X with
  | pad => rfl
  | draw C d =>
    simp only [Chacha.Rng.Gen.rowCell, Chacha.Rng.Gen.drawCell]
    repeat rw [if_neg (by omega)]

def rngRows (calls : List Chacha.Rng.Gen.Call) : Nat := (Chacha.Rng.Gen.honestRows calls).length

def rngTraceAligned (calls : List Chacha.Rng.Gen.Call) : Trace Fp :=
  let log := padLog22 (logOf (rngRows calls))
  rowsTrace log (mkTab (2 ^ log) Chacha.Rng.Table.width (Chacha.Rng.Gen.honestCell calls))

/-- The `rngV3` traffic: receives the drawn words on `B_SCHACHA`, provides one `gen_index`
result per call on `B_SGEN`. -/
def rngTraffic (calls : List Chacha.Rng.Gen.Call) : Traffic :=
  ⟨fun b => if b = B_SGEN then natMsgs (Chacha.Rng.Gen.expectedGen calls) else [],
   fun b => if b = B_SCHACHA then natMsgs (Chacha.Rng.Gen.expectedWords calls) else []⟩

theorem rng_aligned_core (calls : List Chacha.Rng.Gen.Call)
    (hok : ∀ C ∈ calls, Chacha.Rng.Gen.CallOk C)
    (hrows : rngRows calls ≤ 2 ^ 22) (cap : Nat)
    (hcap : padLog22 (logOf (rngRows calls)) ≤ cap) (t : Nat) (pub : List Fp) :
    TableLocal { Chacha.Rng.Table.table B_SCHACHA B_SGEN with maxLog := cap }
      (rngTraceAligned calls) t pub ∧
    TableTraffic (Chacha.Rng.Table.table B_SCHACHA B_SGEN).interactions (rngTraceAligned calls) t pub
      (rngTraffic calls) ∧
    (rngTraceAligned calls).log t % 3 = 1 := by
  have hh := padded_log_fits (rngRows calls) hrows
  generalize hL : padLog22 (logOf (rngRows calls)) = L at hh hcap
  have hlog : (rngTraceAligned calls).log t = L := by
    show padLog22 (logOf (rngRows calls)) = L; exact hL
  have hne : B_SCHACHA ≠ B_SGEN := by decide
  have hc := Chacha.Rng.Complete.gen_completeL calls hok hh.1 B_SCHACHA B_SGEN hne
  have hl : (Chacha.Rng.Gen.traceAt calls L).log t = (rngTraceAligned calls).log t := hlog.symm
  have hcell : ∀ r, r < (Chacha.Rng.Gen.traceAt calls L).height t → ∀ c,
      (Chacha.Rng.Gen.traceAt calls L).cell t r c = (rngTraceAligned calls).cell t r c := by
    intro r hr c
    have hr' : r < 2 ^ L := hr
    unfold rngTraceAligned
    simp only [hL]
    rw [rowsTrace_cells L _ _ (fun r c h => rng_cell_ge calls r c h) t r hr' c]
    rfl
  refine ⟨tableLocal_congr_rows hl hcell
      (tableLocal_mk (show 1 ≤ L by omega) (show L ≤ cap from hcap)
        (fun r hr e he => hc.1 t pub r hr e he) (fun r hr i hi b hb => hc.2.1 t pub r hr i hi b hb)),
    tableTraffic_congr_rows hl hcell ?_, by rw [hlog]; exact hh.2.2.2⟩
  intro b m
  have hcount := Chacha.Rng.Complete.count_rows calls hok hh.1 B_SCHACHA B_SGEN t pub b
  simp only [show (Chacha.Rng.Table.table B_SCHACHA B_SGEN).interactions =
    Chacha.Rng.Table.interactions B_SCHACHA B_SGEN from rfl]
  refine ⟨?_, ?_⟩
  · rw [hcount true m]
    by_cases hb : b = B_SGEN
    · subst hb
      simp [rngTraffic, natMsgs_toFp, hne]
    · simp only [rngTraffic, if_neg hb]
      simp [Ne.symm hb]
  · rw [hcount false m]
    by_cases hb : b = B_SCHACHA
    · subst hb
      simp [rngTraffic, natMsgs_toFp, hne]
    · simp only [rngTraffic, if_neg hb]
      simp [Ne.symm hb]

/-- **`rngV3` aligned completeness at the current `nearAirV3` cap (20)**, for honest calls with at
most `2^19` rows. -/
theorem rng_aligned_complete (calls : List Chacha.Rng.Gen.Call)
    (hok : ∀ C ∈ calls, Chacha.Rng.Gen.CallOk C) (hrows : rngRows calls ≤ 2 ^ 19) (t : Nat)
    (pub : List Fp) :
    TableLocal (Chacha.Rng.Table.table B_SCHACHA B_SGEN) (rngTraceAligned calls) t pub ∧
    TableTraffic (Chacha.Rng.Table.table B_SCHACHA B_SGEN).interactions (rngTraceAligned calls) t pub
      (rngTraffic calls) ∧
    (rngTraceAligned calls).log t % 3 = 1 :=
  rng_aligned_core calls hok (Nat.le_trans hrows (by decide)) 20
    (Nat.le_trans (padded_log_le _ 19 (by decide) (by decide) hrows) (by decide)) t pub

/-- **`rngV3` aligned completeness at cap 22**: every honest call list with at most `2^22`
rows (A9 gives `< 2^20`). -/
theorem rng_aligned_complete22 (calls : List Chacha.Rng.Gen.Call)
    (hok : ∀ C ∈ calls, Chacha.Rng.Gen.CallOk C) (hrows : rngRows calls ≤ 2 ^ 22) (t : Nat)
    (pub : List Fp) :
    TableLocal { Chacha.Rng.Table.table B_SCHACHA B_SGEN with maxLog := 22 } (rngTraceAligned calls) t pub ∧
    TableTraffic (Chacha.Rng.Table.table B_SCHACHA B_SGEN).interactions (rngTraceAligned calls) t pub
      (rngTraffic calls) ∧
    (rngTraceAligned calls).log t % 3 = 1 :=
  rng_aligned_core calls hok hrows 22 (padded_log_fits _ hrows).2.2.1 t pub

/-! ## `shufV3` (table 10) -/

open ZkFormal.Chacha.Shuffle.Complete in
theorem shuf_cell_ge (insts : List Chacha.Shuffle.Gen.SInst) (r c : Nat)
    (hc : Chacha.Shuffle.Table.width ≤ c) : Chacha.Shuffle.Gen.honestCell insts r c = 0 := by
  simp only [Chacha.Shuffle.Table.width] at hc
  unfold Chacha.Shuffle.Gen.honestCell
  generalize (Chacha.Shuffle.Gen.honestRows insts).getD r .pad = X
  cases X with
  | pad =>
    show (if c = Chacha.Shuffle.Table.colRc then r else 0) = 0
    rw [if_neg (by simp only [Chacha.Shuffle.Table.colRc]; omega)]
  | pos I s q => exact c_high I s r q (by omega)

def shufRows (insts : List Chacha.Shuffle.Gen.SInst) : Nat :=
  (Chacha.Shuffle.Gen.honestRows insts).length

def shufTraceAligned (insts : List Chacha.Shuffle.Gen.SInst) : Trace Fp :=
  let log := padLog22 (logOf (shufRows insts))
  rowsTrace log (mkTab (2 ^ log) Chacha.Shuffle.Table.width (Chacha.Shuffle.Gen.honestCell insts))

/-- The `shufV3` buses of `nearAirV3`. -/
def shufBuses : Chacha.Shuffle.Buses := ⟨B_SSIN, B_SSOUT, B_SSMEM, B_SGEN, B_SSHUF⟩

open ZkFormal.Chacha.Shuffle.Complete in
/-- The `shufV3` traffic: receives the inputs (`B_SSIN`) and the `gen_index` results (`B_SGEN`),
provides the outputs (`B_SSOUT`) and the instance messages (`B_SSHUF`); its private memory bus
`B_SSMEM` carries the writes `memSends` and the reads `memRecvs` (a permutation of each other). -/
def shufTraffic (insts : List Chacha.Shuffle.Gen.SInst) : Traffic :=
  ⟨fun b => if b = B_SSOUT then natMsgs (expectedOut insts)
      else if b = B_SSMEM then natMsgs (memSends insts)
      else if b = B_SSHUF then natMsgs (expectedShuf insts) else [],
   fun b => if b = B_SSIN then natMsgs (expectedIn insts)
      else if b = B_SSMEM then natMsgs (memRecvs insts)
      else if b = B_SGEN then natMsgs (expectedGen insts) else []⟩

open ZkFormal.Chacha.Shuffle.Complete in
/-- **`shufV3` aligned completeness at the `nearAirV3` cap (20)**, for honest instances with at
most `2^19` rows. -/
theorem shuf_aligned_complete (insts : List Chacha.Shuffle.Gen.SInst) (hok : ∀ I ∈ insts, InstOk I)
    (hrows : shufRows insts ≤ 2 ^ 19) (t : Nat) (pub : List Fp) :
    TableLocal (Chacha.Shuffle.Table.table B_SSIN B_SSOUT B_SSMEM B_SGEN B_SSHUF)
      (shufTraceAligned insts) t pub ∧
    TableTraffic (Chacha.Shuffle.Table.table B_SSIN B_SSOUT B_SSMEM B_SGEN B_SSHUF).interactions
      (shufTraceAligned insts) t pub (shufTraffic insts) ∧
    (shufTraceAligned insts).log t % 3 = 1 := by
  have h22 : shufRows insts ≤ 2 ^ 22 := Nat.le_trans hrows (by decide)
  have hh := padded_log_fits (shufRows insts) h22
  have h19 := padded_log_le _ 19 (by decide) (by decide) hrows
  generalize hL : padLog22 (logOf (shufRows insts)) = L at hh h19
  have hlog : (shufTraceAligned insts).log t = L := by
    show padLog22 (logOf (shufRows insts)) = L; exact hL
  have hB : shufBuses.ok := by
    simp only [shufBuses, Chacha.Shuffle.Buses.ok, B_SSIN, B_SSOUT, B_SSMEM, B_SGEN, B_SSHUF]
    decide
  have hc := shuffle_completeL insts hok hh.1 (by omega) shufBuses hB
  have hl : (Chacha.Shuffle.Gen.traceAt insts L).log t = (shufTraceAligned insts).log t := hlog.symm
  have hcell : ∀ r, r < (Chacha.Shuffle.Gen.traceAt insts L).height t → ∀ c,
      (Chacha.Shuffle.Gen.traceAt insts L).cell t r c = (shufTraceAligned insts).cell t r c := by
    intro r hr c
    have hr' : r < 2 ^ L := hr
    unfold shufTraceAligned
    simp only [hL]
    rw [rowsTrace_cells L _ _ (fun r c h => shuf_cell_ge insts r c h) t r hr' c]
    rfl
  refine ⟨tableLocal_congr_rows hl hcell
      (tableLocal_mk (show 1 ≤ L by omega) (show L ≤ 20 by omega)
        (fun r hr e he => hc.1 t pub r hr e he) (fun r hr i hi b hb => hc.2.1 t pub r hr i hi b hb)),
    tableTraffic_congr_rows hl hcell ?_, by rw [hlog]; exact hh.2.2.2⟩
  intro b m
  have hcount := count_rows insts hok hh.1 (by omega) shufBuses t pub b
  simp only [show (Chacha.Shuffle.Table.table B_SSIN B_SSOUT B_SSMEM B_SGEN B_SSHUF).interactions =
    shufBuses.is from rfl]
  rw [hcount true m, hcount false m]
  simp only [shufBuses, shufTraffic]
  by_cases h1 : b = B_SSIN
  · subst h1; simp [natMsgs_toFp, B_SSIN, B_SSOUT, B_SSMEM, B_SGEN, B_SSHUF]
  by_cases h2 : b = B_SSOUT
  · subst h2; simp [natMsgs_toFp, B_SSIN, B_SSOUT, B_SSMEM, B_SGEN, B_SSHUF]
  by_cases h3 : b = B_SSMEM
  · subst h3; simp [natMsgs_toFp, B_SSIN, B_SSOUT, B_SSMEM, B_SGEN, B_SSHUF]
  by_cases h4 : b = B_SGEN
  · subst h4; simp [natMsgs_toFp, B_SSIN, B_SSOUT, B_SSMEM, B_SGEN, B_SSHUF]
  by_cases h5 : b = B_SSHUF
  · subst h5; simp [natMsgs_toFp, B_SSIN, B_SSOUT, B_SSMEM, B_SGEN, B_SSHUF]
  simp only [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, Ne.symm h1, Ne.symm h2,
    Ne.symm h3, Ne.symm h4, Ne.symm h5, false_and, if_false, List.map_nil, List.count_nil]
  simp

end ZkFormal.NearV3.Render
