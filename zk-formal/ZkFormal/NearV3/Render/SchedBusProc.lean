import ZkFormal.NearV3.Render.SchedScmp

/-!
# Process table (13) traffic on `SPUBB`, `SPUSH`, `SINC`, `SOP`: per-row closed forms
-/
set_option linter.unusedSimpArgs false
namespace ZkFormal.NearV3.Render.ProcBus
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.NearV3.Sched.Complete ZkFormal.NearV3.Candidates ProcConcatGeometry

def fKey (X : PV) : List (List Fp) :=
  List.replicate (if Fp.ofNat X.kK = 1 then 1 else 0)
    [Fp.ofNat X.tau, (TAG_KEY : Fp), Fp.ofNat X.kc, Fp.ofNat X.sbIn, Fp.ofNat X.sbOut, ((0:Nat):Fp), ((0:Nat):Fp)]

theorem row_key (rs : List Run) (t r : Nat) (pub : List Fp) :
    rowTraffic ProcBoundaryRepair.table.interactions (trace rs) t r pub B_SPUBB false = fKey (atRow rs r) := by
  simp [fKey,ProcBoundaryRepair.table,Proc.table,Proc.interactions,
    rowTraffic,Interaction.multNat,Interaction.multNat.go,Interaction.msgVal,Expr.eval,Expr.evalWith,
    rowEnv,ZkFormal.Chacha.Table.E.c,ZkFormal.Chacha.Table.E.k,trace,
    B_SCMP,B_SOP,B_SPUBB,B_SSHUF,B_SPUSH,B_SSIN,B_SSOUT,B_SINC, PV.cell, Proc.kK, Proc.tau, Proc.kc,
    Proc.sbIn, Proc.sbOut]

def gE (X : PV) (m : List Fp) : List (List Fp) := List.replicate (if Fp.ofNat X.kE = 1 then 1 else 0) m

def fPushR (X : PV) : List (List Fp) :=
  gE X [Fp.ofNat X.tau, Fp.ofNat X.K, Fp.ofNat X.z, Fp.ofNat X.ts, Fp.ofNat X.ein]

def fPushS (X : PV) : List (List Fp) :=
  List.replicate (if Fp.ofNat X.pm = 1 then 1 else 0)
    [Fp.ofNat X.tau, Fp.ofNat X.alOut, Fp.ofNat X.zn, Fp.ofNat X.T + Fp.ofNat X.x, Fp.ofNat X.eout + ((1:Nat):Fp)]

def fInc (X : PV) : List (List Fp) :=
  gE X [Fp.ofNat X.tau, Fp.ofNat X.eout, Fp.ofNat X.inc, Fp.ofNat X.rem, Fp.ofNat X.s, Fp.ofNat X.r, Fp.ofNat X.link]

def fSop (X : PV) : List (List Fp) :=
  gE X [((16384:Nat):Fp) * Fp.ofNat X.tau + (((4096:Nat):Fp) + Fp.ofNat X.s), Fp.ofNat X.T + Fp.ofNat X.x,
    ((OP_GRANT:Nat):Fp), Fp.ofNat X.sbIn, Fp.ofNat X.sbOut, Fp.ofNat X.inc, Fp.ofNat X.ok, Fp.ofNat X.cS] ++
  gE X [((16384:Nat):Fp) * Fp.ofNat X.tau + (((8192:Nat):Fp) + Fp.ofNat X.r), Fp.ofNat X.T + Fp.ofNat X.x,
    ((OP_GRANT:Nat):Fp), Fp.ofNat X.rbIn, Fp.ofNat X.rbOut, Fp.ofNat X.inc, Fp.ofNat X.ok, Fp.ofNat X.cR] ++
  gE X [((16384:Nat):Fp) * Fp.ofNat X.tau + Fp.ofNat X.link, Fp.ofNat X.T + Fp.ofNat X.x,
    ((OP_GRANT:Nat):Fp), Fp.ofNat X.alIn, Fp.ofNat X.alOut, Fp.ofNat X.inc, Fp.ofNat X.ok, Fp.ofNat X.cL]

theorem row_pushR (rs : List Run) (t r : Nat) (pub : List Fp) :
    rowTraffic ProcBoundaryRepair.table.interactions (trace rs) t r pub B_SPUSH false = fPushR (atRow rs r) := by
  simp [fPushR, gE,ProcBoundaryRepair.table,Proc.table,Proc.interactions,
    rowTraffic,Interaction.multNat,Interaction.multNat.go,Interaction.msgVal,Expr.eval,Expr.evalWith,
    rowEnv,ZkFormal.Chacha.Table.E.c,ZkFormal.Chacha.Table.E.k,ZkFormal.Chacha.Table.E.smul,trace,
    B_SCMP,B_SOP,B_SPUBB,B_SSHUF,B_SPUSH,B_SSIN,B_SSOUT,B_SINC, PV.cell, Proc.kK, Proc.tau, Proc.kc,
    Proc.sbIn, Proc.sbOut, Proc.kE, Proc.K, Proc.z, Proc.ts, Proc.ein, Proc.pm, Proc.alOut, Proc.zn, Proc.tE,
    Proc.T, Proc.x, Proc.eout, Proc.inc, Proc.rem, Proc.s, Proc.r, Proc.link, Proc.aS, Proc.aR, Proc.aL,
    Proc.rbIn, Proc.rbOut, Proc.alIn, Proc.ok, Proc.cS, Proc.cR, Proc.cL]

theorem row_pushS (rs : List Run) (t r : Nat) (pub : List Fp) :
    rowTraffic ProcBoundaryRepair.table.interactions (trace rs) t r pub B_SPUSH true = fPushS (atRow rs r) := by
  simp [fPushS,ProcBoundaryRepair.table,Proc.table,Proc.interactions,
    rowTraffic,Interaction.multNat,Interaction.multNat.go,Interaction.msgVal,Expr.eval,Expr.evalWith,
    rowEnv,ZkFormal.Chacha.Table.E.c,ZkFormal.Chacha.Table.E.k,ZkFormal.Chacha.Table.E.smul,trace,
    B_SCMP,B_SOP,B_SPUBB,B_SSHUF,B_SPUSH,B_SSIN,B_SSOUT,B_SINC, PV.cell, Proc.kK, Proc.tau, Proc.kc,
    Proc.sbIn, Proc.sbOut, Proc.kE, Proc.K, Proc.z, Proc.ts, Proc.ein, Proc.pm, Proc.alOut, Proc.zn, Proc.tE,
    Proc.T, Proc.x, Proc.eout, Proc.inc, Proc.rem, Proc.s, Proc.r, Proc.link, Proc.aS, Proc.aR, Proc.aL,
    Proc.rbIn, Proc.rbOut, Proc.alIn, Proc.ok, Proc.cS, Proc.cR, Proc.cL]

theorem row_inc (rs : List Run) (t r : Nat) (pub : List Fp) :
    rowTraffic ProcBoundaryRepair.table.interactions (trace rs) t r pub B_SINC false = fInc (atRow rs r) := by
  simp [fInc, gE,ProcBoundaryRepair.table,Proc.table,Proc.interactions,
    rowTraffic,Interaction.multNat,Interaction.multNat.go,Interaction.msgVal,Expr.eval,Expr.evalWith,
    rowEnv,ZkFormal.Chacha.Table.E.c,ZkFormal.Chacha.Table.E.k,ZkFormal.Chacha.Table.E.smul,trace,
    B_SCMP,B_SOP,B_SPUBB,B_SSHUF,B_SPUSH,B_SSIN,B_SSOUT,B_SINC, PV.cell, Proc.kK, Proc.tau, Proc.kc,
    Proc.sbIn, Proc.sbOut, Proc.kE, Proc.K, Proc.z, Proc.ts, Proc.ein, Proc.pm, Proc.alOut, Proc.zn, Proc.tE,
    Proc.T, Proc.x, Proc.eout, Proc.inc, Proc.rem, Proc.s, Proc.r, Proc.link, Proc.aS, Proc.aR, Proc.aL,
    Proc.rbIn, Proc.rbOut, Proc.alIn, Proc.ok, Proc.cS, Proc.cR, Proc.cL]

theorem row_sop (rs : List Run) (t r : Nat) (pub : List Fp) :
    rowTraffic ProcBoundaryRepair.table.interactions (trace rs) t r pub B_SOP true = fSop (atRow rs r) := by
  simp [fSop, gE,ProcBoundaryRepair.table,Proc.table,Proc.interactions,
    rowTraffic,Interaction.multNat,Interaction.multNat.go,Interaction.msgVal,Expr.eval,Expr.evalWith,
    rowEnv,ZkFormal.Chacha.Table.E.c,ZkFormal.Chacha.Table.E.k,ZkFormal.Chacha.Table.E.smul,trace,
    B_SCMP,B_SOP,B_SPUBB,B_SSHUF,B_SPUSH,B_SSIN,B_SSOUT,B_SINC, PV.cell, Proc.kK, Proc.tau, Proc.kc,
    Proc.sbIn, Proc.sbOut, Proc.kE, Proc.K, Proc.z, Proc.ts, Proc.ein, Proc.pm, Proc.alOut, Proc.zn, Proc.tE,
    Proc.T, Proc.x, Proc.eout, Proc.inc, Proc.rem, Proc.s, Proc.r, Proc.link, Proc.aS, Proc.aR, Proc.aL,
    Proc.rbIn, Proc.rbOut, Proc.alIn, Proc.ok, Proc.cS, Proc.cR, Proc.cL]

theorem gen_physical (F : PV → List (List Fp)) (b : Nat) (sd : Bool)
    (hrow : ∀ rs t r pub, rowTraffic ProcBoundaryRepair.table.interactions (trace rs) t r pub b sd = F (atRow rs r))
    (htail : ∀ R, F (tailV R) = []) (hpad : F padPV = [])
    (rs : List Run) (hcap : (ProcConcatGeometry.rows rs).length ≤ 2^22) (t : Nat) (pub : List Fp) :
    (List.range (2^22)).flatMap (fun r => rowTraffic ProcBoundaryRepair.table.interactions
      (trace rs) t r pub b sd) = (ProcConcatGeometry.rows rs).flatMap F := by
  simp only [hrow]
  rw [show 2^22=(ProcConcatGeometry.rows rs).length+(2^22-(ProcConcatGeometry.rows rs).length) by omega,List.range_add,List.flatMap_append,List.flatMap_map]
  have hz:(List.range (2^22-(ProcConcatGeometry.rows rs).length)).flatMap
      (fun j=>F (atRow rs ((ProcConcatGeometry.rows rs).length+j)))=[] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro j _
    rw [atRow,dif_neg (by omega)]
    split
    · unfold tail
      split
      · exact hpad
      · exact htail _
    · exact hpad
  rw [hz,List.append_nil]
  rw [←ProcComparisonPhysical.range_flatMap (ProcConcatGeometry.rows rs) padPV F]
  apply ZkFormal.Near.flatMap_congr'
  intro r hr
  have hi:=List.mem_range.mp hr
  simp [atRow,hi,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi]

theorem gen_count (F : PV → List (List Fp)) (b : Nat) (sd : Bool)
    (hrow : ∀ rs t r pub, rowTraffic ProcBoundaryRepair.table.interactions (trace rs) t r pub b sd = F (atRow rs r))
    (htail : ∀ R, F (tailV R) = []) (hpad : F padPV = [])
    (rs : List Run) (hcap : (ProcConcatGeometry.rows rs).length ≤ 2^22) (t : Nat) (pub msg : List Fp) :
    tableBusCount Proc.tableB.interactions (procTraceV3 rs) t pub b sd msg = ((ProcConcatGeometry.rows rs).flatMap F).count msg := by
  have hcells : ∀ r, r < 2 ^ 22 → ∀ c, (procTraceV3 rs).cell t r c = Fp.ofNat (procCell rs r c) :=
    fun r hr c => Render.rowsTrace_cells 22 _ _ (fun r c h => pv_cell_ge _ c h) t r hr c
  have hl : (ProcConcatGeometry.trace rs).log t = (procTraceV3 rs).log t := rfl
  have hc : ∀ r, r < (ProcConcatGeometry.trace rs).height t → ∀ c,
      (ProcConcatGeometry.trace rs).cell t r c = (procTraceV3 rs).cell t r c := by
    intro r hr c
    rw [hcells r hr c]; rfl
  rw [← tableBusCount_congr_rows hl hc _ pub b sd msg]
  change tableBusCount ProcBoundaryRepair.table.interactions (trace rs) t pub b sd msg = _
  rw [tableBusCount_eq]
  exact congrArg (fun xs => xs.count msg) (gen_physical F b sd hrow htail hpad rs hcap t pub)

/-! ## Per kind and per run -/

def nf (l : List Nat) : List Fp := l.map Fp.ofNat

theorem cast_eq (n : Nat) : ((n : Nat) : Fp) = Fp.ofNat n := rfl

theorem f0 : (Fp.ofNat 0 : Fp) ≠ 1 := by decide +kernel
theorem f1 : (Fp.ofNat 1 : Fp) = 1 := rfl
theorem succ1 (v : Nat) : Fp.ofNat v + 1 = Fp.ofNat (v + 1) := by
  rw [← ZkFormal.Near.ofNat_add']; rfl

def keyL (R : Run) : List (List Fp) := (List.range 16).map fun k =>
  nf [R.tau, TAG_KEY, k, (R.seed.getD (2 * k) 0).toNat, (R.seed.getD (2 * k + 1) 0).toNat, 0, 0]

def pushRE (R : Run) (rd : Gen.RoundD) (e : Entry) : List Fp := nf [R.tau, rd.K, rd.z, e.ts, e.ein]
def pushSE (R : Run) (rd : Gen.RoundD) (e : Entry) : List (List Fp) :=
  if e.ok && !(e.rem == 0) then [nf [R.tau, e.alOut, e.zn, rd.T + e.x, e.eout + 1]] else []
def incE (R : Run) (e : Entry) : List Fp := nf [R.tau, e.eout, e.inc, e.rem, e.s, e.r, e.link]
def sopE (R : Run) (rd : Gen.RoundD) (e : Entry) : List (List Fp) :=
  [nf [16384 * R.tau + (4096 + e.s), rd.T + e.x, OP_GRANT, e.sbIn, e.sbOut, e.inc, b2n e.ok, b2n e.cS],
   nf [16384 * R.tau + (8192 + e.r), rd.T + e.x, OP_GRANT, e.rbIn, e.rbOut, e.inc, b2n e.ok, b2n e.cR],
   nf [16384 * R.tau + e.link, rd.T + e.x, OP_GRANT, e.alIn, e.alOut, e.inc, b2n e.ok, b2n e.cL]]

theorem key_key (R : Run) (k : Nat) : fKey (keyV R k) =
    [nf [R.tau, TAG_KEY, k, (R.seed.getD (2 * k) 0).toNat, (R.seed.getD (2 * k + 1) 0).toNat, 0, 0]] := by
  simp [fKey, keyV, zeroV, nf, f1, cast_eq]

theorem key_hdr (R : Run) (rd : Gen.RoundD) : fKey (hdrV R rd) = [] := by
  simp [fKey, hdrV, baseV, zeroV, f0]
theorem key_ent (R : Run) (rd : Gen.RoundD) (es : Array Entry) (i : Nat) : fKey (entV R rd es i) = [] := by
  simp [fKey, entV, baseV, zeroV, f0]
theorem key_tail (R : Run) : fKey (tailV R) = [] := by simp [fKey, tailV, zeroV, f0]
theorem key_pad : fKey padPV = [] := by simp [fKey, padPV, zeroV, f0]

theorem gE_key (R : Run) (k : Nat) (m : List Fp) : gE (keyV R k) m = [] := by simp [gE, keyV, zeroV, f0]
theorem gE_hdr (R : Run) (rd : Gen.RoundD) (m : List Fp) : gE (hdrV R rd) m = [] := by
  simp [gE, hdrV, baseV, zeroV, f0]
theorem gE_ent (R : Run) (rd : Gen.RoundD) (es : Array Entry) (i : Nat) (m : List Fp) :
    gE (entV R rd es i) m = [m] := by simp [gE, entV, baseV, zeroV, f1]
theorem gE_tail (R : Run) (m : List Fp) : gE (tailV R) m = [] := by simp [gE, tailV, zeroV, f0]
theorem gE_pad (m : List Fp) : gE padPV m = [] := by simp [gE, padPV, zeroV, f0]

theorem pushS_key (R : Run) (k : Nat) : fPushS (keyV R k) = [] := by simp [fPushS, keyV, zeroV, f0]
theorem pushS_hdr (R : Run) (rd : Gen.RoundD) : fPushS (hdrV R rd) = [] := by
  simp [fPushS, hdrV, baseV, zeroV, f0]
theorem pushS_tail (R : Run) : fPushS (tailV R) = [] := by simp [fPushS, tailV, zeroV, f0]
theorem pushS_pad : fPushS padPV = [] := by simp [fPushS, padPV, zeroV, f0]
theorem pushS_ent (R : Run) (rd : Gen.RoundD) (es : Array Entry) (i : Nat) :
    fPushS (entV R rd es i) = pushSE R rd es[i]! := by
  unfold fPushS pushSE
  by_cases h : (es[i]!.ok && !(es[i]!.rem == 0)) = true
  · simp [entV, baseV, zeroV, h, b2n, f1, nf, cast_eq, succ1]
  · simp [entV, baseV, zeroV, h, b2n, f0]

theorem pushR_ent (R : Run) (rd : Gen.RoundD) (es : Array Entry) (i : Nat) :
    fPushR (entV R rd es i) = [pushRE R rd es[i]!] := by
  simp only [fPushR, gE_ent]; simp [entV, baseV, zeroV, pushRE, nf]
theorem inc_ent (R : Run) (rd : Gen.RoundD) (es : Array Entry) (i : Nat) :
    fInc (entV R rd es i) = [incE R es[i]!] := by
  simp only [fInc, gE_ent]; simp [entV, baseV, zeroV, incE, nf]
theorem sop_ent (R : Run) (rd : Gen.RoundD) (es : Array Entry) (i : Nat) :
    fSop (entV R rd es i) = sopE R rd es[i]! := by
  simp only [fSop, gE_ent]; simp [entV, baseV, zeroV, sopE, nf, cast_eq]

theorem arr_flat {α β : Type} [Inhabited α] (l : List α) (g : α → List β) :
    (List.range l.toArray.size).flatMap (fun i => g l.toArray[i]!) = l.flatMap g := by
  rw [← ProcComparisonPhysical.range_flatMap l default g]
  simp only [List.size_toArray]
  apply ZkFormal.Near.flatMap_congr'
  intro i hi
  have hi' := List.mem_range.mp hi
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', getElem!_pos l.toArray i (by simpa using hi')]

/-- Per-run closed form from per-kind facts. -/
theorem run_gen (F : PV → List (List Fp)) (R : Run) (G : Gen.RoundD → Entry → List (List Fp))
    (hk : ∀ k, F (keyV R k) = []) (hh : ∀ rd, F (hdrV R rd) = [])
    (he : ∀ rd (es : Array Entry) i, F (entV R rd es i) = G rd es[i]!) :
    (procVs R).flatMap F = R.rounds.flatMap fun rd => rd.entries.flatMap (G rd) := by
  simp only [procVs, keyVs, List.flatMap_append, List.flatMap_map, hk]
  rw [show (List.range 16).flatMap (fun _ => ([] : List (List Fp))) = [] by decide, List.nil_append, List.flatMap_assoc]
  apply ZkFormal.Near.flatMap_congr'
  intro rd _
  simp only [roundVs, List.flatMap_cons, hh, List.nil_append, List.flatMap_map, he]
  exact arr_flat rd.entries (G rd)

def pushRL (R : Run) : List (List Fp) := R.rounds.flatMap fun rd => rd.entries.flatMap fun e => [pushRE R rd e]
def pushSL (R : Run) : List (List Fp) := R.rounds.flatMap fun rd => rd.entries.flatMap (pushSE R rd)
def incL (R : Run) : List (List Fp) := R.rounds.flatMap fun rd => rd.entries.flatMap fun e => [incE R e]
def sopL (R : Run) : List (List Fp) := R.rounds.flatMap fun rd => rd.entries.flatMap (sopE R rd)

theorem run_key (R : Run) : (procVs R).flatMap fKey = keyL R := by
  simp only [procVs, keyVs, List.flatMap_append, List.flatMap_map, key_key]
  have : R.rounds.flatMap (fun rd => (roundVs R rd).flatMap fKey) = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro rd _
    simp [roundVs, key_hdr, key_ent]
  rw [List.flatMap_assoc, this, List.append_nil, keyL, ← List.map_eq_flatMap]

theorem run_pushR (R : Run) : (procVs R).flatMap fPushR = pushRL R :=
  run_gen _ R _ (fun k => gE_key R k _) (fun rd => gE_hdr R rd _) (pushR_ent R)
theorem run_pushS (R : Run) : (procVs R).flatMap fPushS = pushSL R :=
  run_gen _ R _ (pushS_key R) (pushS_hdr R) (pushS_ent R)
theorem run_inc (R : Run) : (procVs R).flatMap fInc = incL R :=
  run_gen _ R _ (fun k => gE_key R k _) (fun rd => gE_hdr R rd _) (fun rd es i => inc_ent R rd es i)
theorem run_sop (R : Run) : (procVs R).flatMap fSop = sopL R := by
  apply run_gen _ R _ (fun k => by simp [fSop, gE_key]) (fun rd => by simp [fSop, gE_hdr]) (sop_ent R)

/-! ## Table level -/

theorem tail_all (R : Run) : fKey (tailV R) = [] ∧ fPushR (tailV R) = [] ∧ fPushS (tailV R) = [] ∧
    fInc (tailV R) = [] ∧ fSop (tailV R) = [] := by
  simp [key_tail, fPushR, fInc, fSop, gE_tail, pushS_tail]
theorem pad_all : fKey padPV = [] ∧ fPushR padPV = [] ∧ fPushS padPV = [] ∧
    fInc padPV = [] ∧ fSop padPV = [] := by
  simp [key_pad, fPushR, fInc, fSop, gE_pad, pushS_pad]

theorem rows_flat (F : PV → List (List Fp)) (L : Run → List (List Fp)) (h : ∀ R, (procVs R).flatMap F = L R)
    (rs : List Run) : (ProcConcatGeometry.rows rs).flatMap F = rs.flatMap L := by
  simp only [ProcConcatGeometry.rows, List.flatMap_assoc, h]

theorem count_key (rs : List Run) (hcap : (ProcConcatGeometry.rows rs).length ≤ 2^22) (t : Nat) (pub msg : List Fp) :
    tableBusCount Proc.tableB.interactions (procTraceV3 rs) t pub B_SPUBB false msg = (rs.flatMap keyL).count msg := by
  rw [gen_count fKey _ _ row_key (fun R => (tail_all R).1) pad_all.1 rs hcap, rows_flat _ _ run_key]
theorem count_pushR (rs : List Run) (hcap : (ProcConcatGeometry.rows rs).length ≤ 2^22) (t : Nat) (pub msg : List Fp) :
    tableBusCount Proc.tableB.interactions (procTraceV3 rs) t pub B_SPUSH false msg = (rs.flatMap pushRL).count msg := by
  rw [gen_count fPushR _ _ row_pushR (fun R => (tail_all R).2.1) pad_all.2.1 rs hcap, rows_flat _ _ run_pushR]
theorem count_pushS (rs : List Run) (hcap : (ProcConcatGeometry.rows rs).length ≤ 2^22) (t : Nat) (pub msg : List Fp) :
    tableBusCount Proc.tableB.interactions (procTraceV3 rs) t pub B_SPUSH true msg = (rs.flatMap pushSL).count msg := by
  rw [gen_count fPushS _ _ row_pushS (fun R => (tail_all R).2.2.1) pad_all.2.2.1 rs hcap, rows_flat _ _ run_pushS]
theorem count_inc (rs : List Run) (hcap : (ProcConcatGeometry.rows rs).length ≤ 2^22) (t : Nat) (pub msg : List Fp) :
    tableBusCount Proc.tableB.interactions (procTraceV3 rs) t pub B_SINC false msg = (rs.flatMap incL).count msg := by
  rw [gen_count fInc _ _ row_inc (fun R => (tail_all R).2.2.2.1) pad_all.2.2.2.1 rs hcap, rows_flat _ _ run_inc]
theorem count_sop (rs : List Run) (hcap : (ProcConcatGeometry.rows rs).length ≤ 2^22) (t : Nat) (pub msg : List Fp) :
    tableBusCount Proc.tableB.interactions (procTraceV3 rs) t pub B_SOP true msg = (rs.flatMap sopL).count msg := by
  rw [gen_count fSop _ _ row_sop (fun R => (tail_all R).2.2.2.2) pad_all.2.2.2.2 rs hcap, rows_flat _ _ run_sop]

end ZkFormal.NearV3.Render.ProcBus
