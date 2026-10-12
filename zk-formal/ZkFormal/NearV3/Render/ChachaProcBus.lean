import ZkFormal.NearV3.Candidates.ProcComparisonPhysical
import ZkFormal.NearV3.Render.PaddedProc
import ZkFormal.NearV3.Sched.Link.KeyPub
import ZkFormal.Chacha.Shuffle.Complete.Traffic

/-!
# ZkFormal.NearV3.Render.ChachaProcBus — the process table's shuffle traffic (`SSHUF`, `SSIN`, `SSOUT`)

`sprV3` (table 13) receives one `SSHUF` message per round header, sends one `SSIN` and receives one
`SSOUT` message per entry row (`Proc.interactions`, all reading the current row only).

* `eval_shuf`, `eval_in`, `eval_out`: the three buses on one row (`pmsgs`);
* `hdr_msgs`, `ent_msgs`, `quiet`: header / entry / other rows;
* `run_shuf`, `run_in`, `run_out`: per run, `runShuf`, `runIn`, `runOut`;
* **`table_count`**: the bus count of the honest table `procTraceV3 rs` is the count in
  `rs.flatMap F` for the per-run closed form `F`.
* `leWords_getD`, `leWords_lt`, **`keyN_leWords`** (the `shufV3` key limbs of `leWords seed` are the
  process table's `keyLimb seed i`), **`lid_fp`** (`lidOf` in the field).
-/
namespace ZkFormal.NearV3.Render.ChachaBus
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.NearV3.Sched.Complete ZkFormal.NearV3.Candidates NearSpecV3

/-- One process row as a trace. -/
def pvTrace (X : PV) : Trace Fp := ⟨fun _ => 22, fun _ _ c => Fp.ofNat (X.cell c)⟩

def lidF (X : PV) : Fp := ((4194304 : Nat) : Fp) * Fp.ofNat (X.cell Proc.tau) + Fp.ofNat (X.cell Proc.T)
def keyF (X : PV) : List Fp := (List.range 16).map (fun i => Fp.ofNat (X.cell (Proc.colL i)))

/-- The `SSHUF` receives, `SSIN` sends and `SSOUT` receives of a process row. -/
def pmsgs : Nat → Bool → PV → List (List Fp)
  | 49, false, X => if Fp.ofNat (X.cell Proc.kH) = 1 then [[lidF X] ++ keyF X ++
      [Fp.ofNat (X.cell Proc.kq), Fp.ofNat (X.cell Proc.Lr), Fp.ofNat (X.cell Proc.kend)]] else []
  | 45, true, X =>
    if Fp.ofNat (X.cell Proc.kE) = 1 then [[lidF X, Fp.ofNat (X.cell Proc.x), Fp.ofNat (X.cell Proc.ein)]] else []
  | 46, false, X =>
    if Fp.ofNat (X.cell Proc.kE) = 1 then [[lidF X, Fp.ofNat (X.cell Proc.x), Fp.ofNat (X.cell Proc.eout)]] else []
  | _, _, _ => []

theorem eval_shuf (X : PV) (t r : Nat) (pub : List Fp) :
    rowTraffic ProcBoundaryRepair.table.interactions (pvTrace X) t r pub B_SSHUF false =
    if Fp.ofNat (X.cell Proc.kH) = 1 then [[lidF X] ++ keyF X ++
      [Fp.ofNat (X.cell Proc.kq), Fp.ofNat (X.cell Proc.Lr), Fp.ofNat (X.cell Proc.kend)]] else [] := by
  simp [pvTrace,ProcBoundaryRepair.table,Proc.table,Proc.interactions,rowTraffic,Interaction.multNat,Interaction.multNat.go,
    Interaction.msgVal,Expr.eval,Expr.evalWith,rowEnv,ZkFormal.Chacha.Table.E.c,ZkFormal.Chacha.Table.E.k,
    Proc.lidE, Proc.keyMsg, ZkFormal.Chacha.Table.E.smul,
    B_SCMP,B_SOP,B_SPUBB,B_SSHUF,B_SPUSH,B_SSIN,B_SSOUT,B_SINC, lidF, keyF]
  split <;> simp
  intro a _; rfl

theorem eval_in (X : PV) (t r : Nat) (pub : List Fp) :
    rowTraffic ProcBoundaryRepair.table.interactions (pvTrace X) t r pub B_SSIN true =
    if Fp.ofNat (X.cell Proc.kE) = 1 then [[lidF X, Fp.ofNat (X.cell Proc.x), Fp.ofNat (X.cell Proc.ein)]] else [] := by
  simp [pvTrace,ProcBoundaryRepair.table,Proc.table,Proc.interactions,rowTraffic,Interaction.multNat,Interaction.multNat.go,
    Interaction.msgVal,Expr.eval,Expr.evalWith,rowEnv,ZkFormal.Chacha.Table.E.c,ZkFormal.Chacha.Table.E.k,
    Proc.lidE, ZkFormal.Chacha.Table.E.smul,
    B_SCMP,B_SOP,B_SPUBB,B_SSHUF,B_SPUSH,B_SSIN,B_SSOUT,B_SINC, lidF]
  split <;> simp

theorem eval_out (X : PV) (t r : Nat) (pub : List Fp) :
    rowTraffic ProcBoundaryRepair.table.interactions (pvTrace X) t r pub B_SSOUT false =
    if Fp.ofNat (X.cell Proc.kE) = 1 then [[lidF X, Fp.ofNat (X.cell Proc.x), Fp.ofNat (X.cell Proc.eout)]] else [] := by
  simp [pvTrace,ProcBoundaryRepair.table,Proc.table,Proc.interactions,rowTraffic,Interaction.multNat,Interaction.multNat.go,
    Interaction.msgVal,Expr.eval,Expr.evalWith,rowEnv,ZkFormal.Chacha.Table.E.c,ZkFormal.Chacha.Table.E.k,
    Proc.lidE, ZkFormal.Chacha.Table.E.smul,
    B_SCMP,B_SOP,B_SPUBB,B_SSHUF,B_SPUSH,B_SSIN,B_SSOUT,B_SINC, lidF]
  split <;> simp

/-! ## Per-row values -/

theorem fp0 : Fp.ofNat 0 = (0 : Fp) := rfl
theorem fp1 : Fp.ofNat 1 = (1 : Fp) := rfl
theorem fp01 : (0 : Fp) ≠ 1 := by decide +kernel

/-- The three buses on a row with `kH = kE = 0` are empty. -/
theorem quiet (X : PV) (h1 : X.kH = 0) (h2 : X.kE = 0) :
    pmsgs B_SSHUF false X = [] ∧ pmsgs B_SSIN true X = [] ∧ pmsgs B_SSOUT false X = [] := by
  have c1 : X.cell Proc.kH = X.kH := rfl
  have c2 : X.cell Proc.kE = X.kE := rfl
  simp only [pmsgs, B_SSHUF, B_SSIN, B_SSOUT]
  rw [c1, c2, h1, h2, fp0]
  simp [fp01]

/-- The `SSHUF` message of a round header. -/
def hdrShuf (R : Run) (rd : Gen.RoundD) : List Fp :=
  [((4194304 : Nat) : Fp) * Fp.ofNat R.tau + Fp.ofNat rd.T] ++
    (List.range 16).map (fun i => Fp.ofNat (keyLimb R.seed i)) ++
    [Fp.ofNat rd.kst, Fp.ofNat rd.Lr, Fp.ofNat rd.kend]

def entIn (R : Run) (rd : Gen.RoundD) (e : Entry) : List Fp :=
  [((4194304 : Nat) : Fp) * Fp.ofNat R.tau + Fp.ofNat rd.T, Fp.ofNat e.x, Fp.ofNat e.ein]
def entOut (R : Run) (rd : Gen.RoundD) (e : Entry) : List Fp :=
  [((4194304 : Nat) : Fp) * Fp.ofNat R.tau + Fp.ofNat rd.T, Fp.ofNat e.x, Fp.ofNat e.eout]

theorem hdr_msgs (R : Run) (rd : Gen.RoundD) :
    pmsgs B_SSHUF false (hdrV R rd) = [hdrShuf R rd] ∧ pmsgs B_SSIN true (hdrV R rd) = [] ∧
      pmsgs B_SSOUT false (hdrV R rd) = [] := by
  simp only [pmsgs, B_SSHUF, B_SSIN, B_SSOUT]
  have c1 : (hdrV R rd).cell Proc.kH = 1 := rfl
  have c2 : (hdrV R rd).cell Proc.kE = 0 := rfl
  rw [c1, c2, fp0, fp1]
  simp only [ite_true, fp01, ite_false, and_true]
  rfl

theorem ent_msgs (R : Run) (rd : Gen.RoundD) (es : Array Entry) (i : Nat) :
    pmsgs B_SSHUF false (entV R rd es i) = [] ∧ pmsgs B_SSIN true (entV R rd es i) = [entIn R rd es[i]!] ∧
      pmsgs B_SSOUT false (entV R rd es i) = [entOut R rd es[i]!] := by
  simp only [pmsgs, B_SSHUF, B_SSIN, B_SSOUT]
  have c1 : (entV R rd es i).cell Proc.kH = 0 := rfl
  have c2 : (entV R rd es i).cell Proc.kE = 1 := rfl
  rw [c1, c2, fp0, fp1]
  simp only [ite_true, fp01, ite_false, true_and]
  exact ⟨rfl, rfl⟩

/-! ## Per run -/

def runShuf (R : Run) : List (List Fp) := R.rounds.map (hdrShuf R)
def runIn (R : Run) : List (List Fp) :=
  R.rounds.flatMap fun rd => (List.range rd.entries.toArray.size).map fun i => entIn R rd rd.entries.toArray[i]!
def runOut (R : Run) : List (List Fp) :=
  R.rounds.flatMap fun rd => (List.range rd.entries.toArray.size).map fun i => entOut R rd rd.entries.toArray[i]!

theorem keyVs_quiet (R : Run) :
    (keyVs R).flatMap (pmsgs B_SSHUF false) = [] ∧ (keyVs R).flatMap (pmsgs B_SSIN true) = [] ∧
      (keyVs R).flatMap (pmsgs B_SSOUT false) = [] := by
  have q := fun k => quiet (keyV R k) rfl rfl
  simp only [keyVs, List.flatMap_map]
  refine ⟨?_, ?_, ?_⟩ <;> apply List.flatMap_eq_nil_iff.mpr <;> intro k _
  · exact (q k).1
  · exact (q k).2.1
  · exact (q k).2.2

theorem run_shuf (R : Run) : (procVs R).flatMap (pmsgs B_SSHUF false) = runShuf R := by
  rw [procVs, List.flatMap_append, (keyVs_quiet R).1, List.nil_append, List.flatMap_assoc, runShuf,
    List.map_eq_flatMap]
  apply ZkFormal.Near.flatMap_congr'
  intro rd _
  simp only [roundVs, List.flatMap_cons, (hdr_msgs R rd).1, List.flatMap_map, (ent_msgs R rd _ _).1]
  simp

theorem run_in (R : Run) : (procVs R).flatMap (pmsgs B_SSIN true) = runIn R := by
  rw [procVs, List.flatMap_append, (keyVs_quiet R).2.1, List.nil_append, List.flatMap_assoc, runIn]
  apply ZkFormal.Near.flatMap_congr'
  intro rd _
  simp only [roundVs, List.flatMap_cons, (hdr_msgs R rd).2.1, List.flatMap_map, (ent_msgs R rd _ _).2.1]
  rw [List.nil_append, ← List.map_eq_flatMap]

theorem run_out (R : Run) : (procVs R).flatMap (pmsgs B_SSOUT false) = runOut R := by
  rw [procVs, List.flatMap_append, (keyVs_quiet R).2.2, List.nil_append, List.flatMap_assoc, runOut]
  apply ZkFormal.Near.flatMap_congr'
  intro rd _
  simp only [roundVs, List.flatMap_cons, (hdr_msgs R rd).2.2, List.flatMap_map, (ent_msgs R rd _ _).2.2]
  rw [List.nil_append, ← List.map_eq_flatMap]


/-! ## The whole table -/

theorem row_view (rs : List Run) (t r : Nat) (pub : List Fp) (b : Nat) (s : Bool) :
    rowTraffic ProcBoundaryRepair.table.interactions (ProcConcatGeometry.trace rs) t r pub b s =
      rowTraffic ProcBoundaryRepair.table.interactions (pvTrace (ProcConcatGeometry.atRow rs r)) t r pub b s :=
  rowTraffic_current ProcBoundaryRepair.table.interactions proc_currentOnly (ProcConcatGeometry.trace rs)
    (pvTrace (ProcConcatGeometry.atRow rs r)) t r pub (fun _ => rfl) b s

theorem tail_quiet (rs : List Run) :
    pmsgs B_SSHUF false (ProcConcatGeometry.tail rs) = [] ∧ pmsgs B_SSIN true (ProcConcatGeometry.tail rs) = [] ∧
      pmsgs B_SSOUT false (ProcConcatGeometry.tail rs) = [] := by
  unfold ProcConcatGeometry.tail
  split
  · exact quiet _ rfl rfl
  · exact quiet _ rfl rfl

theorem table_count (rs : List Run) (hcap : (ProcConcatGeometry.rows rs).length ≤ 2 ^ 22) (b : Nat) (s : Bool)
    (hev : ∀ X t r pub, rowTraffic ProcBoundaryRepair.table.interactions (pvTrace X) t r pub b s = pmsgs b s X)
    (F : Run → List (List Fp)) (hq : pmsgs b s (ProcConcatGeometry.tail rs) = [] ∧ pmsgs b s padPV = [])
    (hrun : ∀ R, (procVs R).flatMap (pmsgs b s) = F R) (t : Nat) (pub m : List Fp) :
    tableBusCount Proc.tableB.interactions (procTraceV3 rs) t pub b s m = (rs.flatMap F).count m := by
  have hcells : ∀ r, r < 2 ^ 22 → ∀ c, (procTraceV3 rs).cell t r c = Fp.ofNat (procCell rs r c) :=
    fun r hr c => rowsTrace_cells 22 _ _ (fun r c h => pv_cell_ge _ c h) t r hr c
  have hl : (ProcConcatGeometry.trace rs).log t = (procTraceV3 rs).log t := rfl
  have hc : ∀ r, r < (ProcConcatGeometry.trace rs).height t → ∀ c,
      (ProcConcatGeometry.trace rs).cell t r c = (procTraceV3 rs).cell t r c := by
    intro r hr c
    rw [hcells r hr c]; rfl
  rw [← tableBusCount_congr_rows hl hc _ pub b s m, ← boundaryRepair_eq, tableBusCount_eq]
  refine congrArg (List.count m) ?_
  have hh : (ProcConcatGeometry.trace rs).height t = 2 ^ 22 := rfl
  rw [hh]
  simp only [row_view, hev]
  rw [show 2 ^ 22 = (ProcConcatGeometry.rows rs).length + (2 ^ 22 - (ProcConcatGeometry.rows rs).length) by omega,
    List.range_add, List.flatMap_append, List.flatMap_map]
  have hz : (List.range (2 ^ 22 - (ProcConcatGeometry.rows rs).length)).flatMap
      (fun j => pmsgs b s (ProcConcatGeometry.atRow rs ((ProcConcatGeometry.rows rs).length + j))) = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro j _
    rw [ProcConcatGeometry.atRow, dif_neg (show ¬ ((ProcConcatGeometry.rows rs).length + j < (ProcConcatGeometry.rows rs).length) by omega)]
    split
    · exact hq.1
    · exact hq.2
  rw [hz, List.append_nil]
  have ha : (List.range (ProcConcatGeometry.rows rs).length).flatMap
      (fun r => pmsgs b s (ProcConcatGeometry.atRow rs r)) = (ProcConcatGeometry.rows rs).flatMap (pmsgs b s) := by
    rw [← ProcComparisonPhysical.range_flatMap (ProcConcatGeometry.rows rs) padPV (pmsgs b s)]
    apply ZkFormal.Near.flatMap_congr'
    intro r hr
    have hi := List.mem_range.mp hr
    simp [ProcConcatGeometry.atRow, hi, List.getD_eq_getElem?_getD]
  rw [ha, ProcConcatGeometry.rows, List.flatMap_assoc]
  exact ZkFormal.Near.flatMap_congr' (fun R _ => hrun R)
/-! ## Keys and list ids -/

theorem leWords_getD : ∀ (s : List UInt8) (j : Nat), j < (leWords s).length →
    (leWords s).getD j 0 = wordAt s j
  | a :: b :: c :: d :: rest, j, h => by
    cases j with
    | zero => simp [leWords, wordAt]
    | succ j =>
      simp only [leWords, List.length_cons] at h
      simp only [leWords, List.getD_cons_succ]
      rw [leWords_getD rest j (by omega)]
      simp only [wordAt, List.getD_cons_succ, show 4 * (j + 1) = 4 * j + 4 by omega,
        show 4 * j + 4 + 1 = 4 * j + 1 + 4 by omega, show 4 * j + 4 + 2 = 4 * j + 2 + 4 by omega,
        show 4 * j + 4 + 3 = 4 * j + 3 + 4 by omega]
  | [], j, h => by simp [leWords] at h
  | [_], j, h => by simp [leWords] at h
  | [_, _], j, h => by simp [leWords] at h
  | [_, _, _], j, h => by simp [leWords] at h

theorem leWords_lt (s : List UInt8) : ∀ x ∈ leWords s, x < 2 ^ 32 := by
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  have := leWords_getD s j hj
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some] at this
  rw [this, wordAt]
  have := (s.getD (4 * j) 0).toNat_lt; have := (s.getD (4 * j + 1) 0).toNat_lt
  have := (s.getD (4 * j + 2) 0).toNat_lt; have := (s.getD (4 * j + 3) 0).toNat_lt
  omega

theorem keyN_leWords (s : List UInt8) (h8 : (leWords s).length = 8) :
    ZkFormal.Chacha.Shuffle.Complete.keyN (leWords s) =
      (List.range 16).map (fun i => Fp.ofNat (keyLimb s i)) := by
  unfold ZkFormal.Chacha.Shuffle.Complete.keyN
  apply List.map_congr_left
  intro q hq
  have hq := List.mem_range.mp hq
  rw [leWords_getD s (q / 2) (by omega), wordAt, keyLimb]
  have := (s.getD (4 * (q / 2)) 0).toNat_lt; have := (s.getD (4 * (q / 2) + 1) 0).toNat_lt
  have := (s.getD (4 * (q / 2) + 2) 0).toNat_lt; have := (s.getD (4 * (q / 2) + 3) 0).toNat_lt
  congr 1
  rcases Nat.mod_two_eq_zero_or_one q with h | h
  · rw [h, show 2 * q = 4 * (q / 2) by omega, show 4 * (q / 2) + 1 = 4 * (q / 2) + 1 by rfl]
    simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one]
    omega
  · rw [h, show 2 * q = 4 * (q / 2) + 2 by omega, show 4 * (q / 2) + 2 + 1 = 4 * (q / 2) + 3 by omega]
    simp only [Nat.mul_one]
    omega

theorem lid_fp (tau T : Nat) : Fp.ofNat (lidOf tau T) = ((4194304 : Nat) : Fp) * Fp.ofNat tau + Fp.ofNat T := by
  have c (a : Nat) : Fp.ofNat a = (a : Fp) := rfl
  rw [c, c, c, lidOf]
  grind
end ZkFormal.NearV3.Render.ChachaBus
