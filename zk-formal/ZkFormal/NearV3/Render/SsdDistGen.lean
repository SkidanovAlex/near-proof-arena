import ZkFormal.NearV3.Render.SsdChain
import ZkFormal.NearV3.Candidates.ProcDistComparisonValid
import ZkFormal.NearV3.Candidates.ExceptRange
import ZkFormal.NearV3.Sched.Link.InitDist

/-!
# The distribute rows of one native scheduler run as a descriptor chain

The distribute generator (`distRows`, factored as `ProcDistGeneratorFactor.build`) emits the
sender shard rows, the receiver shard rows, then per sender position a grid header and `n` cells.
`dist_block`: for a run with `n ≤ 64` shards, final budgets `≤ 4,500,000` (`Budget R`) and
`τ < P`, the emitted rows are the rows of a descriptor list that is a chain of valid descriptors,
starts with sender shard row `0` (`kp = 0`) and ends with the last grid cell (`Final`).

The shard rows are explicit (`shardD`); the cells are tracked through the loops by invariants on
the sender endpoint `se` and the receiver endpoints `ri` (bounded by 64 links and 4.5 M), the
allowed-cell check of the generator giving `0 < n1, n2` on allowed cells.
-/
namespace ZkFormal.NearV3.Render.Ssd
open ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Candidates
open ProcDistGeneratorFactor ProcDistCellBridge NearSpecV3.Scheduler

section
variable (I : Input) (R : Run)

/-! ## Shard rows -/

def sX (sd i : Nat) : Nat := ProcDistShardRow.nativeX I R sd i
def sC (sd i : Nat) : Nat := ProcDistShardRow.nativeCount I R sd (sX I R sd i)
def sL (sd i : Nat) : Nat := ProcDistShardRow.nativeLeft R sd (sX I R sd i)
def sB (sd i : Nat) : Nat := budget0 ⟨I.ids, I.p, I.allowed, I.raw, I.seed, I.ash⟩ sd (sX I R sd i)
def kpOf (sd i : Nat) : Nat :=
  if i = 0 then 0 else SsdShard.key (sC I R sd (i-1)) (sL I R sd (i-1)) (sX I R sd (i-1)) + 1

def shardD (sd i : Nat) : Desc :=
  .shard R.tau R.n sd i (sX I R sd i) (sC I R sd i) (sL I R sd i) (sB I R sd i) (kpOf I R sd i)

theorem shard_step (sd i : Nat) (s : ShardAcc) (o : ForInStep ShardAcc) (h : shardStep I R sd i s = .ok o) :
    ∃ out, o = .yield out ∧
      out.1 = s.1.push (ProcDistShardRow.row R.tau R.n sd i (sX I R sd i) (sC I R sd i) (sL I R sd i)
        (sB I R sd i) s.2.2) ∧
      out.2.2 = SsdShard.key (sC I R sd i) (sL I R sd i) (sX I R sd i) + 1 := by
  have h' := h
  unfold shardStep at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    refine ⟨_, rfl, ?_, rfl⟩
    exact ProcDistShardRow.emitted I R sd i s _ h'

theorem shard_loop (sd : Nat) (acc : Array (Array Nat) × List Cmp) (out : ShardAcc)
    (h : forIn (List.range R.n) (acc.1, acc.2, 0) (shardStep I R sd) = .ok out) :
    out.1.toList = acc.1.toList ++ ((List.range R.n).map (shardD I R sd)).map Desc.row := by
  have := ExceptRange.range_invariant (shardStep I R sd)
    (fun k (s : ShardAcc) => s.1.toList = acc.1.toList ++ ((List.range k).map (shardD I R sd)).map Desc.row ∧
      s.2.2 = kpOf I R sd k) R.n
    (fun k _ s hs o ho => by
      obtain ⟨out, rfl, h1, h2⟩ := shard_step I R sd k s o ho
      refine ⟨out, rfl, ?_, ?_⟩
      · rw [h1, Array.toList_push, hs.1, List.range_succ, List.map_append, List.map_append,
          List.append_assoc]
        simp only [List.map_cons, List.map_nil]
        rw [hs.2]
        rfl
      · rw [h2]; simp [kpOf])
    _ out ⟨by simp, by simp [kpOf]⟩ h
  exact this.1

/-! ## Cells -/

def cAl (i j : Nat) : Bool := I.allowed[sender I R i * R.n + receiver I R j]!

theorem cell_step (i j : Nat) (acc : CellAcc) (o : ForInStep CellAcc) (h : cellStep I R i j acc = .ok o) :
    ∃ out, o = .yield out ∧
      out.1 = acc.1.push (ProcDistCellRow.row I.ids R.tau R.n i j (sender I R i) (receiver I R j)
        acc.2.2.2.2.1 acc.2.2.2.2.2 (acc.2.2.2.1[receiver I R j]!).1 (acc.2.2.2.1[receiver I R j]!).2
        (cAl I R i j)) ∧
      out.2.2.2.1 = acc.2.2.2.1.set! (receiver I R j)
        ((acc.2.2.2.1[receiver I R j]!).1 - b2n (cAl I R i j),
         (acc.2.2.2.1[receiver I R j]!).2 - ProcDistCellRow.grant (cAl I R i j) acc.2.2.2.2.1 acc.2.2.2.2.2
           (acc.2.2.2.1[receiver I R j]!).1 (acc.2.2.2.1[receiver I R j]!).2) ∧
      out.2.2.2.2 = (acc.2.2.2.2.1 - b2n (cAl I R i j),
        acc.2.2.2.2.2 - ProcDistCellRow.grant (cAl I R i j) acc.2.2.2.2.1 acc.2.2.2.2.2
           (acc.2.2.2.1[receiver I R j]!).1 (acc.2.2.2.1[receiver I R j]!).2) ∧
      (cAl I R i j = true → 1 ≤ acc.2.2.2.2.1 ∧ 1 ≤ (acc.2.2.2.1[receiver I R j]!).1) := by
  have h' := h
  by_cases hal : cAl I R i j = true
  · unfold cellStep at h
    dsimp only at h
    unfold cAl at hal
    dsimp only [sender, receiver] at hal
    simp only [hal, ite_true] at h
    simp only [bind, Except.bind] at h
    split at h
    · cases h
    · rename_i v hchk
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      have hc := ProcActualReplayShape.check_true _ _ hchk
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      refine ⟨_, rfl, ?_, ?_, ?_, ?_⟩
      · exact ProcDistCellRow.emitted I R i j acc _ h'
      · simp only [cAl, sender, receiver, hal, ProcDistCellRow.grant, b2n, ite_true]
      · simp only [cAl, sender, receiver, hal, ProcDistCellRow.grant, b2n, ite_true]
      · intro _; exact ⟨hc.1, hc.2⟩
  · have hf : cAl I R i j = false := by simpa using hal
    unfold cellStep at h
    dsimp only at h
    unfold cAl at hf
    dsimp only [sender, receiver] at hf
    simp only [hf, Bool.false_eq_true, ite_false] at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    refine ⟨_, rfl, ?_, ?_, ?_, ?_⟩
    · exact ProcDistCellRow.emitted I R i j acc _ h'
    · simp only [cAl, sender, receiver, hf, ProcDistCellRow.grant, b2n, ite_false, Bool.false_eq_true,
        Nat.sub_zero]
    · simp only [cAl, sender, receiver, hf, ProcDistCellRow.grant, b2n, ite_false, Bool.false_eq_true,
        Nat.sub_zero]
    · intro h; exact absurd h hal

/-! ## Bounds -/

theorem sorted_lt (f : Nat → Nat) (n i : Nat) (hi : i < n) : (sortByKey f (List.range n))[i]! < n := by
  have hl : (sortByKey f (List.range n)).length = n :=
    (sortByKey_perm _ _).length_eq.trans List.length_range
  have hm : (sortByKey f (List.range n))[i]! ∈ sortByKey f (List.range n) := by
    rw [getElem!_pos _ i (by omega)]
    exact List.getElem_mem _
  exact List.mem_range.mp ((sortByKey_perm _ _).mem_iff.mp hm)

theorem cntS_le (n : Nat) (al : Array Bool) (s : Nat) : cntS n al s ≤ n := by
  unfold cntS; exact Nat.le_trans (List.length_filter_le _ _) (by simp)

theorem cntR_le (n : Nat) (al : Array Bool) (r : Nat) : cntR n al r ≤ n := by
  unfold cntR; exact Nat.le_trans (List.length_filter_le _ _) (by simp)

theorem sX_lt (sd i : Nat) (hi : i < R.n) : sX I R sd i < R.n := by
  unfold sX ProcDistShardRow.nativeX
  split
  · exact sorted_lt _ _ _ hi
  · exact sorted_lt _ _ _ hi

theorem sender_lt (i : Nat) (hi : i < R.n) : sender I R i < R.n := sorted_lt _ _ _ hi

theorem sC_le (sd i : Nat) : sC I R sd i ≤ R.n := by
  unfold sC ProcDistShardRow.nativeCount
  split
  · exact cntS_le _ _ _
  · exact cntR_le _ _ _

theorem sL_le (hb : ProcDistShardValid.Budget R) (sd i : Nat) : sL I R sd i ≤ 4500000 := by
  unfold sL ProcDistShardRow.nativeLeft
  split
  · exact hb.1 _
  · exact hb.2 _

theorem sB_le (hmax : I.p.maxShardBandwidth = 4500000) (sd i : Nat) : sB I R sd i ≤ 4500000 := by
  unfold sB
  have := budget0_le ⟨I.ids, I.p, I.allowed, I.raw, I.seed, I.ash⟩ sd (sX I R sd i)
  simpa [hmax] using this

theorem shardD_valid (hn : R.n ≤ 64) (hb : ProcDistShardValid.Budget R)
    (hmax : I.p.maxShardBandwidth = 4500000) (ht : R.tau < P) (sd i : Nat) (hsd : sd = 0 ∨ sd = 1)
    (hi : i < R.n) : (shardD I R sd i).Valid := by
  have hkp : kpOf I R sd i < P := by
    unfold kpOf
    split
    · unfold P; omega
    · have := SsdShard.key_lt (sC I R sd (i-1)) (sL I R sd (i-1)) (sX I R sd (i-1))
        (by have := sC_le I R sd (i-1); omega) (sL_le I R hb sd (i-1))
        (by have := sX_lt I R sd (i-1) (by omega); omega)
      unfold P; omega
  refine ⟨hsd, ?_, ?_, sL_le I R hb sd i, ?_, hi, hn, ht, hkp⟩
  · have := sB_le I R hmax sd i; omega
  · have := sC_le I R sd i; omega
  · have := sX_lt I R sd i hi; omega

theorem shards_chain (sd : Nat) :
    Chain ((List.range R.n).map (shardD I R sd)) := by
  apply chain_map_range
  intro k hk
  refine ⟨rfl, rfl, Or.inl ⟨hk, rfl, rfl, ?_⟩⟩
  simp [kpOf]

def RiOk (ri : Array (Nat × Nat)) : Prop := ∀ r : Nat, (ri[r]! : Nat × Nat).1 ≤ 64 ∧ (ri[r]! : Nat × Nat).2 ≤ 4500000

theorem riOk_set (ri : Array (Nat × Nat)) (h : RiOk ri) (k : Nat) (v : Nat × Nat)
    (hv : v.1 ≤ 64 ∧ v.2 ≤ 4500000) : RiOk (ri.set! k v) := by
  intro j
  by_cases he : k = j
  · subst j
    by_cases hk : k < ri.size
    · rw [Array.getElem!_set!_self _ _ _ hk]; exact hv
    · rw [Array.set!_eq_setIfInBounds, Array.setIfInBounds_eq_of_size_le (by omega)]
      exact h k
  · rw [Array.getElem!_set!_ne _ _ _ _ he]; exact h j

/-! ## Cells of one grid row -/

def hdrD (i : Nat) : Desc :=
  .header R.tau R.n i (sender I R i) (cntS R.n I.allowed (sender I R i)) (R.fin.sb[sender I R i]!)

def LastCellAt (x : Desc) (i j : Nat) : Prop :=
  ∃ sv rr n1 l1 n2 l2 al, x = .cell I.ids R.tau R.n i j sv rr n1 l1 n2 l2 al

def CInv (i : Nat) (pre : List (Array Nat)) (j : Nat) (acc : CellAcc) : Prop :=
  ∃ cl : List Desc, acc.1.toList = pre ++ (hdrD I R i :: cl).map Desc.row ∧ cl.length = j ∧
    (∀ d ∈ cl, d.Valid) ∧ Chain (hdrD I R i :: cl) ∧
    (j < R.n → ∀ rr n2 l2 al, Desc.Adj ((hdrD I R i :: cl).getLast (by simp))
      (.cell I.ids R.tau R.n i j (sender I R i) rr acc.2.2.2.2.1 acc.2.2.2.2.2 n2 l2 al)) ∧
    (0 < j → LastCellAt I R ((hdrD I R i :: cl).getLast (by simp)) i (j-1)) ∧
    RiOk acc.2.2.2.1 ∧ acc.2.2.2.2.1 ≤ 64 ∧ acc.2.2.2.2.2 ≤ 4500000

theorem getLast_cons_snoc (a : Desc) (l : List Desc) (d : Desc) (h : a :: (l ++ [d]) ≠ []) :
    (a :: (l ++ [d])).getLast h = d := by
  rw [List.getLast_cons (by simp)]
  simp

theorem cell_inv_step (i : Nat) (hi : i < R.n) (hn : R.n ≤ 64) (pre : List (Array Nat)) (j : Nat)
    (hj : j < R.n) (acc : CellAcc) (hinv : CInv I R i pre j acc) (o : ForInStep CellAcc)
    (h : cellStep I R i j acc = .ok o) : ∃ out, o = .yield out ∧ CInv I R i pre (j+1) out := by
  obtain ⟨out, rfl, h1, h2, h3, h4⟩ := cell_step I R i j acc o h
  obtain ⟨cl, hrows, hlen, hval, hch, hnext, _, hri, hs1, hs2⟩ := hinv
  have hrr := hri (receiver I R j)
  let dnew : Desc := .cell I.ids R.tau R.n i j (sender I R i) (receiver I R j) acc.2.2.2.2.1 acc.2.2.2.2.2
    (acc.2.2.2.1[receiver I R j]!).1 (acc.2.2.2.1[receiver I R j]!).2 (cAl I R i j)
  refine ⟨out, rfl, cl ++ [dnew], ?_, by simp [hlen], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h1, Array.toList_push, hrows]
    simp only [List.cons_append, List.map_cons, List.map_append, List.map_cons, List.map_nil,
      List.append_assoc]
    rfl
  · intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · exact hval d hd
    · simp only [List.mem_singleton] at hd
      subst hd
      refine ⟨hi, hj, hn, hs1, hrr.1, hs2, hrr.2, fun ha => ?_⟩
      have := h4 ha; omega
  · have := chain_append (hdrD I R i :: cl) [dnew] hch (chain_single _) (fun x y hx hy => by
      simp only [List.head?_cons, Option.some.injEq] at hy
      subst hy
      rw [List.getLast?_eq_getLast (by simp)] at hx
      simp only [Option.some.injEq] at hx
      subst hx
      exact hnext hj _ _ _ _)
    simpa using this
  · intro hj1 rr n2 l2 al
    rw [getLast_cons_snoc, h3]
    exact ⟨rfl, rfl, rfl, rfl, hj1, rfl, rfl, rfl, rfl⟩
  · intro _
    rw [getLast_cons_snoc]
    exact ⟨_, _, _, _, _, _, _, rfl⟩
  · rw [h2]
    apply riOk_set _ hri
    constructor
    · exact Nat.le_trans (Nat.sub_le _ _) hrr.1
    · exact Nat.le_trans (Nat.sub_le _ _) hrr.2
  · rw [h3]; exact Nat.le_trans (Nat.sub_le _ _) hs1
  · rw [h3]; exact Nat.le_trans (Nat.sub_le _ _) hs2

theorem bind_ok' {α β ε : Type} {x : Except ε α} {f : α → Except ε β} {out : β}
    (h : x >>= f = .ok out) : ∃ v, x = .ok v ∧ f v = .ok out := by
  cases x with
  | error e => cases h
  | ok v => exact ⟨v, rfl, h⟩

/-! ## Grid rows -/

def GInv (shards : List (Array Nat)) (i : Nat) (acc : GridAcc) : Prop :=
  ∃ gl : List Desc, acc.1.toList = shards ++ gl.map Desc.row ∧ (∀ d ∈ gl, d.Valid) ∧ Chain gl ∧
    (∀ x, gl.head? = some x → ∃ sv c l, x = .header R.tau R.n 0 sv c l) ∧ (i = 0 → gl = []) ∧
    (0 < i → ∃ x, gl.getLast? = some x ∧ LastCellAt I R x (i-1) (R.n-1)) ∧ RiOk acc.2.2.2

theorem hdrD_valid (hn : R.n ≤ 64) (hb : ProcDistShardValid.Budget R) (ht : R.tau < P) (i : Nat)
    (hi : i < R.n) : (hdrD I R i).Valid := by
  have hs := sender_lt I R i hi
  have hc := cntS_le R.n I.allowed (sender I R i)
  have hl := hb.1 (sender I R i)
  refine ⟨ht, ?_, ?_, ?_, ?_, ?_⟩ <;> unfold P <;> omega

theorem grid_step (hn : R.n ≤ 64) (hb : ProcDistShardValid.Budget R) (ht : R.tau < P)
    (shards : List (Array Nat)) (i : Nat) (hi : i < R.n) (acc : GridAcc) (hinv : GInv I R shards i acc)
    (o : ForInStep GridAcc) (h : gridStep I R i acc = .ok o) :
    ∃ out, o = .yield out ∧ GInv I R shards (i+1) out := by
  obtain ⟨gl, hrows, hval, hch, hhead, hzero, hlast, hri⟩ := hinv
  unfold gridStep at h
  obtain ⟨u, hu, h⟩ := bind_ok' h
  cases h
  have hcl := ExceptRange.range_invariant (cellStep I R i) (CInv I R i acc.1.toList) R.n
    (fun j hj b hbI s hs => cell_inv_step I R i hi hn acc.1.toList j hj b hbI s hs) _ u
    (by
      refine ⟨[], ?_, rfl, fun d hd => by simp at hd, chain_single _, ?_, fun h => by omega, hri, ?_, ?_⟩
      · simp only [Array.toList_push, List.map_cons, List.map_nil]; rfl
      · intro _ rr n2 l2 al
        exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · exact Nat.le_trans (cntS_le _ _ _) hn
      · exact hb.1 _) hu
  obtain ⟨cl, hrows', _, hval', hch', _, hlastc, hri', _, _⟩ := hcl
  refine ⟨_, rfl, gl ++ (hdrD I R i :: cl), ?_, ?_, ?_, ?_, fun h => by omega, ?_, hri'⟩
  · change u.1.toList = _
    rw [hrows', hrows, List.map_append, List.append_assoc]
  · intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · exact hval d hd
    · rcases List.mem_cons.mp hd with rfl | hd
      · exact hdrD_valid I R hn hb ht i hi
      · exact hval' d hd
  · apply chain_append _ _ hch hch'
    intro x y hx hy
    simp only [List.head?_cons, Option.some.injEq] at hy
    subst hy
    by_cases hi0 : i = 0
    · rw [hzero hi0] at hx; simp at hx
    · obtain ⟨z, hz, sv, rr, n1, l1, n2, l2, al, rfl⟩ := hlast (by omega)
      rw [hz] at hx; cases hx
      exact ⟨by omega, by omega, rfl, rfl, by omega⟩
  · intro x hx
    rw [List.head?_append] at hx
    cases hg : gl.head? with
    | none =>
      rw [hg] at hx
      simp only [Option.none_or, List.head?_cons, Option.some.injEq] at hx
      subst hx
      have : gl = [] := by simpa using hg
      have hi0 : i = 0 := by
        rcases Nat.eq_zero_or_pos i with h0 | h0
        · exact h0
        · exfalso
          obtain ⟨z, hz, _⟩ := hlast h0
          rw [this] at hz; simp at hz
      subst hi0
      exact ⟨_, _, _, rfl⟩
    | some z => rw [hg] at hx; simp at hx; subst hx; exact hhead _ hg
  · intro _
    refine ⟨(hdrD I R i :: cl).getLast (by simp), ?_, ?_⟩
    · rw [List.getLast?_append, List.getLast?_eq_getLast (l := hdrD I R i :: cl) (by simp)]; rfl
    · have := hlastc (by omega)
      simpa using this

/-! ## The block -/

def DistStart (d : Desc) : Prop := ∃ tv n x c l bud, d = .shard tv n 0 0 x c l bud 0

theorem shard_side (sd : Nat) (acc : Array (Array Nat) × List Cmp) (o : ForInStep (Array (Array Nat) × List Cmp))
    (h : shardSide I R sd acc = .ok o) :
    ∃ out, o = .yield out ∧ out.1.toList = acc.1.toList ++ ((List.range R.n).map (shardD I R sd)).map Desc.row := by
  unfold shardSide at h
  obtain ⟨u, hu, h⟩ := bind_ok' h
  cases h
  exact ⟨_, rfl, shard_loop I R sd acc u hu⟩

theorem head?_map_range (n : Nat) (f : Nat → Desc) :
    ((List.range n).map f).head? = if n = 0 then none else some (f 0) := by
  cases n with
  | zero => rfl
  | succ n => simp [List.range_succ_eq_map]

theorem getLast?_map_range (n : Nat) (f : Nat → Desc) :
    ((List.range n).map f).getLast? = if n = 0 then none else some (f (n-1)) := by
  cases n with
  | zero => rfl
  | succ n => simp [List.range_succ]

/-- **The distribute block of one run.** -/
theorem dist_block (hn : R.n ≤ 64) (hb : ProcDistShardValid.Budget R)
    (hmax : I.p.maxShardBandwidth = 4500000) (ht : R.tau < P) (d : DistOut) (hd : distRows I R = .ok d) :
    ∃ ds : List Desc, d.rows.toList = ds.map Desc.row ∧ Chain ds ∧ (∀ x ∈ ds, x.Valid) ∧
      (∀ x, ds.head? = some x → DistStart x) ∧ (∀ x, ds.getLast? = some x → x.Final) ∧
      (0 < R.n → ds ≠ []) := by
  rw [native_eq] at hd
  unfold build at hd
  obtain ⟨a, ha, hd⟩ := bind_ok' hd
  obtain ⟨b, hbld, hd⟩ := bind_ok' hd
  cases hd
  -- the two shard sides
  have hA : a.1.toList = ((List.range R.n).map (shardD I R 0)).map Desc.row ++
      ((List.range R.n).map (shardD I R 1)).map Desc.row := by
    simp only [List.forIn_cons, List.forIn_nil] at ha
    obtain ⟨o0, h0, ha⟩ := bind_ok' ha
    obtain ⟨a0, rfl, ha0⟩ := shard_side I R 0 _ o0 h0
    simp only at ha
    obtain ⟨o1, h1, ha⟩ := bind_ok' ha
    obtain ⟨a1, rfl, ha1⟩ := shard_side I R 1 _ o1 h1
    simp only [pure, Except.pure, Except.ok.injEq] at ha
    subst ha
    rw [ha1, ha0]; simp
  have hG := ExceptRange.range_invariant (gridStep I R) (GInv I R (((List.range R.n).map (shardD I R 0)).map Desc.row ++
      ((List.range R.n).map (shardD I R 1)).map Desc.row)) R.n
    (fun i hi acc hacc o ho => grid_step I R hn hb ht _ i hi acc hacc o ho) _ b
    (by
      refine ⟨[], by simpa using hA, fun d hd => by simp at hd, chain_nil, fun x hx => by simp at hx,
        fun _ => rfl, fun h => by omega, ?_⟩
      intro r
      by_cases hr : r < R.n
      · rw [List.map_toArray, getElem!_toArray_map_range R.n _ hr]
        exact ⟨Nat.le_trans (cntR_le _ _ _) hn, hb.2 r⟩
      · rw [getElem!_neg _ _ (by simp only [Array.size_map, List.size_toArray, List.length_range]; omega)]
        exact ⟨Nat.zero_le _, Nat.zero_le _⟩) hbld
  obtain ⟨gl, hrows, hval, hch, hhead, hzero, hlast, _⟩ := hG
  refine ⟨(List.range R.n).map (shardD I R 0) ++ (List.range R.n).map (shardD I R 1) ++ gl, ?_, ?_, ?_, ?_, ?_,
    fun h0 => by cases hn' : R.n with | zero => omega | succ m => simp [List.range_succ]⟩
  · change b.1.toList = _
    rw [hrows]; simp
  · apply chain_append
    · apply chain_append _ _ (shards_chain I R 0) (shards_chain I R 1)
      intro x y hx hy
      rw [getLast?_map_range] at hx; rw [head?_map_range] at hy
      split at hx
      · cases hx
      · rename_i hn0
        rw [if_neg hn0] at hy
        cases hx; cases hy
        exact ⟨rfl, rfl, Or.inr ⟨by omega, rfl, rfl, rfl, by simp [kpOf]⟩⟩
    · exact hch
    · intro x y hx hy
      obtain ⟨sv, c, l, rfl⟩ := hhead y hy
      rw [List.getLast?_append, getLast?_map_range] at hx
      by_cases hn0 : R.n = 0
      · rw [hzero hn0] at hy; simp at hy
      · rw [if_neg hn0] at hx
        simp only [Option.some_or] at hx
        cases hx
        exact ⟨rfl, rfl, by omega, rfl, rfl⟩
  · intro x hx
    simp only [List.mem_append, List.mem_map, List.mem_range] at hx
    rcases hx with (⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩) | hx
    · exact shardD_valid I R hn hb hmax ht 0 i (Or.inl rfl) hi
    · exact shardD_valid I R hn hb hmax ht 1 i (Or.inr rfl) hi
    · exact hval x hx
  · intro x hx
    rw [List.append_assoc, List.head?_append, head?_map_range] at hx
    by_cases hn0 : R.n = 0
    · rw [if_pos hn0] at hx
      rw [List.head?_append, head?_map_range, if_pos hn0, hzero hn0] at hx
      simp at hx
    · rw [if_neg hn0] at hx
      simp only [Option.some_or, Option.some.injEq] at hx
      subst hx
      exact ⟨_, _, _, _, _, _, rfl⟩
  · intro x hx
    by_cases hn0 : R.n = 0
    · rw [hzero hn0] at hx
      simp [getLast?_map_range, hn0] at hx
    · obtain ⟨z, hz, sv, rr, n1, l1, n2, l2, al, rfl⟩ := hlast (by omega)
      rw [List.getLast?_append, hz] at hx
      simp only [Option.some_or, Option.some.injEq] at hx
      subst hx
      exact ⟨by omega, by omega⟩

end

end ZkFormal.NearV3.Render.Ssd
