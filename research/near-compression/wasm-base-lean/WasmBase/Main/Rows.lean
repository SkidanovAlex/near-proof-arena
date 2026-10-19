import WasmBase.Main.Lookups
import WasmBase.CheckFacts
import WasmBase.SpecLemmas
/-!
# WasmBase.Main.Rows — shared definitions for the per-chip row lemmas

The view of one row of an instruction table (index `t`): its input / output STATE messages
(`inters[0]`, `inters[1]`), the CH messages it consumes / produces (decoded to `Msg`), the public
input layout (`PubOK`), and the generic facts every chip uses: a FETCH query pins the code record
of its pc (`fetch_rec`, `recordOf_spec`), and a channel time check bounds the producer time
(`time_chk`).
-/
namespace WasmBase
open ZkFormal.Algebra NearSpecV3.Wasm Chips Local
set_option linter.unusedSimpArgs false

/-- Decode a CH message `[space, slot, tag, v0, v1, v2, v3, tp]`. -/
def decMsg (l : List F) : Msg :=
  ⟨(l.getD 0 0).toNat, (l.getD 1 0).toNat, (l.getD 2 0).toNat, (l.getD 3 0).toNat, (l.getD 4 0).toNat,
   (l.getD 5 0).toNat, (l.getD 6 0).toNat, (l.getD 7 0).toNat⟩

def rowIn (T : Table) (tr : Trace) (pub : List F) (t r : Nat) : List F :=
  (T.inters.getD 0 default).msg.map (·.eval (tr.row pub t r))
def rowOut (T : Table) (tr : Trace) (pub : List F) (t r : Nat) : List F :=
  (T.inters.getD 1 default).msg.map (·.eval (tr.row pub t r))
def rowCons (T : Table) (tr : Trace) (pub : List F) (t r : Nat) : List Msg :=
  (rowMsgs T tr pub t r busStk false).map decMsg
def rowProd (T : Table) (tr : Trace) (pub : List F) (t r : Nat) : List Msg :=
  (rowMsgs T tr pub t r busStk true).map decMsg
/-- The row is active: its STATE receive has count 1. -/
def rowAct (T : Table) (tr : Trace) (pub : List F) (t r : Nat) : Prop :=
  ((T.inters.getD 0 default).count.eval (tr.row pub t r)).toNat = 1

/-- The public inputs are the ones the verifier derives from the checker output. -/
structure PubOK (X : Ctx) (nloc ncode : Nat) (pub : List F) : Prop where
  hnloc : nloc = X.pf.locals.size
  hncode : ncode = X.pf.code.size
  len : pub.length = Boundary.pubLoc + nloc
  locTags : ∀ j, j < nloc → pub.getD (Boundary.pubLoc + j) 0 = ((X.ck.localTags.getD j 0 : Nat) : F)
  nres : pub.getD Boundary.pubNres 0 = ((X.ck.arity : Nat) : F)
  status : pub.getD Boundary.pubStatus 0 = ((1 : Nat) : F) ∨ pub.getD Boundary.pubStatus 0 = ((2 : Nat) : F)
  rtag : pub.getD Boundary.pubTag 0 = ((X.ck.resTag : Nat) : F)

/-! ## Occurrences of a row -/

theorem row_occ {A : Air} {tr : Trace} {pub : List F} {t : Nat} (ht : t < A.tables.length) {r : Nat}
    (hr : r < tr.height t) {i : Inter} (hi : i ∈ (A.tables[t]'ht).inters) :
    (i.bus, i.send, i.msg.map (·.eval (tr.row pub t r)), (i.count.eval (tr.row pub t r)).toNat) ∈
      occs A tr pub :=
  mem_occs.mpr ⟨t, ht, r, hr, i, hi, rfl⟩

/-! ## Code records -/

theorem recordOf_spec {ls : List Label} {h fee pc : Nat} {ins : Instr} {rec : List Nat}
    (hr : recordOf ls h fee pc ins = some rec) :
    ∃ op x0 x1 x2 x3, rec = [pc, op, h, fee, x0, x1, x2, x3] ∧
      ((∃ v : UInt32, ins = .i32Const v ∧ op = 0x41 ∧ [x0, x1, x2, x3] = limbs4 v.toNat) ∨
       (∃ v : UInt64, ins = .i64Const v ∧ op = 0x42 ∧ [x0, x1, x2, x3] = limbs4 v.toNat) ∨
       (ins = .drop ∧ op = 0x1A ∧ [x0, x1, x2, x3] = [0, 0, 0, 0]) ∨
       (∃ ty, ins = .select ty ∧ op = 0x1B ∧ [x0, x1, x2, x3] = [0, 0, 0, 0]) ∨
       (∃ x, ins = .localGet x ∧ op = 0x20 ∧ [x0, x1, x2, x3] = [x, 0, 0, 0]) ∨
       (∃ x, ins = .localSet x ∧ op = 0x21 ∧ [x0, x1, x2, x3] = [x, 0, 0, 0]) ∨
       (∃ x, ins = .localTee x ∧ op = 0x22 ∧ [x0, x1, x2, x3] = [x, 0, 0, 0]) ∨
       (ins = .num op ∧ isFamilyNum op = true ∧ [x0, x1, x2, x3] = [0, 0, 0, 0]) ∨
       (kindOf ls ins = some .next ∧ op = Ctrl.opNext ∧ [x0, x1, x2, x3] = [0, 0, 0, 0]) ∨
       (∃ tg, kindOf ls ins = some (.jump tg) ∧ op = Ctrl.opJump ∧ [x0, x1, x2, x3] = [tg, 0, 0, 0]) ∨
       (∃ tg, kindOf ls ins = some (.jumpIf tg) ∧ op = Ctrl.opJif ∧ [x0, x1, x2, x3] = [tg, 0, 0, 0]) ∨
       (kindOf ls ins = some .halt ∧ op = Ctrl.opHalt ∧ [x0, x1, x2, x3] = [0, 0, 0, 0]) ∨
       (kindOf ls ins = some .haltIf ∧ op = Ctrl.opHif ∧ [x0, x1, x2, x3] = [0, 0, 0, 0])) := by
  unfold recordOf at hr
  split at hr
  · simp only [Option.some.injEq] at hr; subst hr
    exact ⟨_, _, _, _, _, by simp [limbs4], Or.inl ⟨_, rfl, rfl, rfl⟩⟩
  · simp only [Option.some.injEq] at hr; subst hr
    exact ⟨_, _, _, _, _, by simp [limbs4], Or.inr (Or.inl ⟨_, rfl, rfl, rfl⟩)⟩
  · simp only [Option.some.injEq] at hr; subst hr
    exact ⟨_, _, _, _, _, rfl, Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))⟩
  · simp only [Option.some.injEq] at hr; subst hr
    exact ⟨_, _, _, _, _, rfl, Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl, rfl, rfl⟩)))⟩
  · simp only [Option.some.injEq] at hr; subst hr
    exact ⟨_, _, _, _, _, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl, rfl, rfl⟩))))⟩
  · simp only [Option.some.injEq] at hr; subst hr
    exact ⟨_, _, _, _, _, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl, rfl, rfl⟩)))))⟩
  · simp only [Option.some.injEq] at hr; subst hr
    exact ⟨_, _, _, _, _, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl, rfl, rfl⟩))))))⟩
  · split at hr
    · simp only [Option.some.injEq] at hr; subst hr
      exact ⟨_, _, _, _, _, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, ‹_›, rfl⟩)))))))⟩
    · simp at hr
  · rename_i hk1 hk2 hk3 hk4 hk5 hk6 hk7 hk8
    split at hr <;> simp only [Option.some.injEq, reduceCtorEq] at hr <;> subst hr
    · exact ⟨_, _, _, _, _, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl ⟨‹_›, rfl, rfl⟩))))))))⟩
    · exact ⟨_, _, _, _, _, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inl ⟨_, ‹_›, rfl, rfl⟩)))))))))⟩
    · exact ⟨_, _, _, _, _, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inl ⟨_, ‹_›, rfl, rfl⟩))))))))))⟩
    · exact ⟨_, _, _, _, _, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inl ⟨‹_›, rfl, rfl⟩)))))))))))⟩
    · exact ⟨_, _, _, _, _, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr ⟨‹_›, rfl, rfl⟩)))))))))))⟩

theorem fetch_rec {X : Ctx} {nloc ncode : Nat} {pub : List F} {tr : Trace} (_hpub : PubOK X nloc ncode pub)
    (L : Looks X nloc ncode pub tr) {m : List F}
    (ho : (busFetch, true, m, 1) ∈ occs (wasmBaseAir nloc ncode) tr pub) {pc : Nat}
    (hpc : m.getD 0 0 = ((pc : Nat) : F)) (hpcl : pc < X.pf.code.size) :
    ∃ ins fee rec, X.pf.code[pc]? = some ins ∧ feeUnits X.cfg X.pf.gas[pc]? = some fee ∧ fee ≤ X.ck.maxFee ∧
      recordOf (X.ck.labels[pc]?.getD []) (X.ck.heights[pc]?.getD 0) fee pc ins = some rec ∧
      m = rec.map fun x => ((x : Nat) : F) := by
  have hP' := P_val
  obtain ⟨j, hjc, hm⟩ := L.fetch _ ho rfl rfl rfl
  simp only [codeRec] at hm
  have CF := X.facts
  obtain ⟨ins, fee, hins, hfee, hfl, hrec⟩ := CF.recs j hjc
  have hsz : j < X.ck.records.size := by rw [CF.records]; exact hjc
  rw [Array.getElem?_eq_getElem hsz] at hrec hm
  simp only [Option.getD_some] at hm
  obtain ⟨op, x0, x1, x2, x3, hre, -⟩ := recordOf_spec hrec
  have hj' : ((j : Nat) : F) = ((pc : Nat) : F) := by rw [← hpc, hm, hre]; rfl
  have := CF.codeLt
  have hjp : j = pc := natEq hj' (by omega) (by omega)
  subst hjp
  exact ⟨ins, fee, _, hins, hfee, hfl, hrec, hm⟩

/-- A channel time check `[r16 (ts - tp - 1 - 2^16 hi), r16 (4 hi)]` with count 1 bounds the
producer time: `tp + 1 + n = ts` with `n < 2^30 + 2^16`. -/
theorem time_chk {X : Ctx} {nloc ncode : Nat} {pub : List F} {tr : Trace} (L : Looks X nloc ncode pub tr)
    {ts tp hi : F}
    (h1 : (busR16, true, [ts - tp - ((1 : Nat) : F) - ((65536 : Nat) : F) * hi], 1) ∈ occs (wasmBaseAir nloc ncode) tr pub)
    (h2 : (busR16, true, [((4 : Nat) : F) * hi], 1) ∈ occs (wasmBaseAir nloc ncode) tr pub) :
    ∃ n, n < 2 ^ 30 + 2 ^ 16 ∧ ((tp.toNat + 1 + n : Nat) : F) = ts := by
  obtain ⟨x, hx, hxl⟩ := L.r16 _ h1 rfl rfl rfl
  obtain ⟨y, hy, hyl⟩ := L.r16 _ h2 rfl rfl rfl
  simp only [List.cons.injEq, and_true] at hx hy
  refine ⟨x.toNat + 16384 * y.toNat, by omega, ?_⟩
  simp only [Lean.Grind.Semiring.natCast_add, Lean.Grind.Semiring.natCast_mul, Fp.cast_toNat]
  rw [← hx, ← hy]
  have : ((65536 : Nat) : F) = ((16384 : Nat) : F) * ((4 : Nat) : F) := by
    rw [← Lean.Grind.Semiring.natCast_mul]
  rw [this]; grind

theorem toNat_cast_sub {h k : Nat} (hk : k ≤ h) (hh : h < ZkFormal.Algebra.P) :
    (((h : Nat) : F) - ((k : Nat) : F)).toNat = h - k := by
  have : ((h : Nat) : F) - ((k : Nat) : F) = ((h - k : Nat) : F) := by
    have e : ((h : Nat) : F) = ((h - k : Nat) : F) + ((k : Nat) : F) := by
      rw [← Lean.Grind.Semiring.natCast_add, Nat.sub_add_cancel hk]
    rw [e]; grind
  rw [this, Fp.toNat_cast_of_lt (by omega)]

theorem cell_cast (tr : Trace) (t r i : Nat) : tr.cell t r i = ((rowNat tr t r i : Nat) : F) := by
  simp only [rowNat, Fp.cast_toNat]

theorem rowMsgs_eq (T : Table) (tr : Trace) (pub : List F) (t r b : Nat) (s : Bool) :
    rowMsgs T tr pub t r b s = (T.inters.filter fun i => i.bus = b ∧ i.send = s).filterMap fun i =>
      if (i.count.eval (tr.row pub t r)).toNat = 1 then some (i.msg.map (·.eval (tr.row pub t r))) else none := by
  unfold rowMsgs rowOccs
  generalize T.inters = l
  induction l with
  | nil => rfl
  | cons i l ih =>
    by_cases h1 : i.bus = b ∧ i.send = s
    · by_cases h2 : (i.count.eval (tr.row pub t r)).toNat = 1
      · rw [List.map_cons, List.filter_cons_of_pos (by simp [h1, h2]), List.map_cons,
          List.filter_cons_of_pos (by simp [h1]), List.filterMap_cons, ih]
        simp [h2]
      · rw [List.map_cons, List.filter_cons_of_neg (by simp [h2]), List.filter_cons_of_pos (by simp [h1]),
          List.filterMap_cons, ih]
        simp [h2]
    · rw [List.map_cons, List.filter_cons_of_neg (by simp only [decide_eq_true_eq]; exact fun h => h1 ⟨h.1, h.2.1⟩),
        List.filter_cons_of_neg (by simpa using h1), ih]

theorem feeUnits_lt {cfg : NearCfg} {g : Option (Option (IK × Fee))} {fee : Nat} (h : feeUnits cfg g = some fee) :
    fee < 2 ^ 16 := by
  unfold feeUnits at h
  split at h
  · simp only [Option.some.injEq] at h; omega
  · split at h
    · simp only [Option.some.injEq] at h; omega
    · simp at h
  · simp at h

/-- The pc of any FETCH query is a code index. -/
theorem fetch_pc {X : Ctx} {nloc ncode : Nat} {pub : List F} {tr : Trace} (_hpub : PubOK X nloc ncode pub)
    (L : Looks X nloc ncode pub tr) {m : List F}
    (ho : (busFetch, true, m, 1) ∈ occs (wasmBaseAir nloc ncode) tr pub) :
    ∃ pc, pc < X.pf.code.size ∧ m.getD 0 0 = ((pc : Nat) : F) := by
  obtain ⟨j, hjc, hm⟩ := L.fetch _ ho rfl rfl rfl
  simp only [codeRec] at hm
  have CF := X.facts
  obtain ⟨ins, fee, hins, hfee, hfl, hrec⟩ := CF.recs j hjc
  have hsz : j < X.ck.records.size := by rw [CF.records]; exact hjc
  rw [Array.getElem?_eq_getElem hsz] at hrec hm
  simp only [Option.getD_some] at hm
  obtain ⟨op, x0, x1, x2, x3, hre, -⟩ := recordOf_spec hrec
  exact ⟨j, hjc, by rw [hm, hre]; rfl⟩

theorem stMsg_cons {a b c d : F} {pc t S h : Nat} (e : [a, b, c, d] = stMsg pc t S h) :
    a = ((pc : Nat) : F) ∧ b = ((t : Nat) : F) ∧ c = ((S : Nat) : F) ∧ d = ((h : Nat) : F) := by
  simp only [stMsg, List.cons.injEq, and_true] at e; exact e

theorem decMsg_cast (a0 a1 a2 a3 a4 a5 a6 a7 : Nat) (h0 : a0 < ZkFormal.Algebra.P) (h1 : a1 < ZkFormal.Algebra.P)
    (h2 : a2 < ZkFormal.Algebra.P) (h3 : a3 < ZkFormal.Algebra.P) (h4 : a4 < ZkFormal.Algebra.P)
    (h5 : a5 < ZkFormal.Algebra.P) (h6 : a6 < ZkFormal.Algebra.P) (h7 : a7 < ZkFormal.Algebra.P) :
    decMsg [((a0 : Nat) : F), ((a1 : Nat) : F), ((a2 : Nat) : F), ((a3 : Nat) : F), ((a4 : Nat) : F),
      ((a5 : Nat) : F), ((a6 : Nat) : F), ((a7 : Nat) : F)] = ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩ := by
  simp only [decMsg, List.getD_cons_zero, List.getD_cons_succ, Fp.toNat_cast_of_lt h0, Fp.toNat_cast_of_lt h1,
    Fp.toNat_cast_of_lt h2, Fp.toNat_cast_of_lt h3, Fp.toNat_cast_of_lt h4, Fp.toNat_cast_of_lt h5,
    Fp.toNat_cast_of_lt h6, Fp.toNat_cast_of_lt h7]

theorem isFamilyNum_le {op : Nat} (h : isFamilyNum op = true) : op ≤ 0x8A := by
  unfold isFamilyNum at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  omega

theorem recordOf_op_lt {ls : List Label} {h fee pc : Nat} {ins : Instr} {rec : List Nat}
    (hr : recordOf ls h fee pc ins = some rec) : rec.getD 1 0 < 512 := by
  obtain ⟨op, x0, x1, x2, x3, rfl, hc⟩ := recordOf_spec hr
  simp only [List.getD_cons_succ, List.getD_cons_zero]
  rcases hc with ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩ |
    ⟨_, _, h, _⟩ | ⟨_, hf, _⟩ | ⟨_, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, h, _⟩ | ⟨_, h, _⟩ <;>
  first | (subst h; decide) | (have := isFamilyNum_le hf; omega)

end WasmBase
