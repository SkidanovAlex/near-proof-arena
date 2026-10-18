import WasmBase.Check
/-!
# Facts established by a successful `check`
-/
namespace WasmBase
open NearSpecV3.Wasm
set_option linter.unusedSimpArgs false

theorem mapM_some {α β : Type} (f : α → Option β) :
    ∀ (l : List α) (rs : List β), l.mapM f = some rs →
      rs.length = l.length ∧ ∀ i (hi : i < l.length), f l[i] = rs[i]? := by
  intro l
  induction l with
  | nil => intro rs h; simp at h; subst h; simp
  | cons a l ih =>
    intro rs h
    simp only [List.mapM_cons, bind, Option.bind] at h
    cases hfa : f a with
    | none => simp [hfa] at h
    | some b =>
      simp only [hfa] at h
      cases hml : l.mapM f with
      | none => simp [hml] at h
      | some rs' =>
        simp only [hml, pure, Option.some.injEq] at h
        subst h
        obtain ⟨hlen, hall⟩ := ih rs' hml
        refine ⟨by simp [hlen], ?_⟩
        intro i hi
        cases i with
        | zero => simp [hfa]
        | succ i => simpa using hall i (by simpa using hi)

theorem foldl_max_ge (l : List Nat) (a : Nat) : ∀ x ∈ l, x ≤ l.foldl max a := by
  induction l generalizing a with
  | nil => simp
  | cons y l ih =>
    intro x hx
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · have := foldl_max_init l (max a x)
      omega
    · exact ih _ x hx
where
  foldl_max_init : ∀ (l : List Nat) (a : Nat), a ≤ l.foldl max a := by
    intro l
    induction l with
    | nil => intro a; simp
    | cons y l ih => intro a; simp only [List.foldl_cons]; have := ih (max a y); omega

/-- Everything the base-faithful proof uses from `check`. -/
structure CheckFacts (cfg : NearCfg) (p : Prepared) (fn : Nat) (pf : PFunc) (ck : CheckOut) : Prop where
  func : p.funcs[fn]? = some pf
  params : pf.type.params.size = 0
  nloc : pf.locals.size ≤ 64
  results : pf.type.results.size ≤ 1
  resTypes : ∀ t ∈ pf.type.results.toList, t = .i32 ∨ t = .i64
  locTypes : ∀ t ∈ pf.locals.toList, t = .i32 ∨ t = .i64
  codeLt : pf.code.size < 2 ^ 20
  gasSize : pf.gas.size = pf.code.size
  lsize : ck.labels.size = pf.code.size
  hsize : ck.heights.size = pf.code.size
  l0 : ck.labels[0]? = some [rootLabel pf]
  h0 : ck.heights[0]? = some 0
  verify : ∀ pc, pc < pf.code.size → verifyAt pf ck.labels ck.heights pc = true
  hBound : ∀ pc, pc < pf.code.size → ck.heights[pc]?.getD 0 < 2 ^ 16
  records : ck.records.size = pf.code.size
  recs : ∀ pc, pc < pf.code.size → ∃ ins fee, pf.code[pc]? = some ins ∧
    feeUnits cfg pf.gas[pc]? = some fee ∧ fee ≤ ck.maxFee ∧
    recordOf (ck.labels[pc]?.getD []) (ck.heights[pc]?.getD 0) fee pc ins = ck.records[pc]?
  arity : ck.arity = pf.type.results.size
  resTag : ck.resTag = if pf.type.results[0]? == some .i64 then 1 else 0
  localTags : ck.localTags = pf.locals.toList.map fun t => if t == .i64 then 1 else 0
  locIdx : ∀ i ∈ pf.code.toList, ∀ x, (i = .localGet x ∨ i = .localSet x ∨ i = .localTee x) →
    x < pf.locals.size

theorem recordOf_fee {ls : List Label} {h fee pc : Nat} {ins : Instr} {r : List Nat}
    (hr : recordOf ls h fee pc ins = some r) : r.getD 3 0 = fee := by
  unfold recordOf at hr
  split at hr <;> (try split at hr) <;> (try split at hr) <;> simp_all <;>
    (try (obtain ⟨_, rfl⟩ := hr; rfl)) <;> (try (subst hr; rfl))

end WasmBase

namespace WasmBase
open NearSpecV3.Wasm

theorem check_sound {cfg : NearCfg} {p : Prepared} {fn : Nat} {ck : CheckOut}
    (h : check cfg p fn = some ck) : ∃ pf, CheckFacts cfg p fn pf ck := by
  unfold check at h
  cases hpf : p.funcs[fn]? with
  | none => simp [hpf] at h
  | some pf =>
    simp only [hpf] at h
    cases hb : basicOk pf with
    | false => simp [hb] at h
    | true =>
      simp only [hb, ite_true] at h
      cases han : analyze pf with
      | none => simp [han] at h
      | some LH =>
        obtain ⟨L, H⟩ := LH
        simp only [han] at h
        cases hs : structOk pf L H with
        | false => simp [hs] at h
        | true =>
          simp only [hs, ite_true] at h
          cases hm : (List.range pf.code.size).mapM (recordAt cfg pf L H) with
          | none => simp [hm] at h
          | some recs =>
            simp only [hm, Option.some.injEq] at h
            subst h
            obtain ⟨hlen, hall⟩ := mapM_some _ _ _ hm
            simp only [List.length_range] at hlen
            simp only [basicOk, Bool.and_eq_true, decide_eq_true_eq] at hb
            obtain ⟨⟨⟨⟨⟨⟨⟨g1, g1a⟩, g1b⟩, g2⟩, g3⟩, g4⟩, g5⟩, g5a⟩ := hb
            simp only [structOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
              at hs
            obtain ⟨⟨⟨⟨g6, g6a⟩, g6b⟩, g6c⟩, g7⟩ := hs
            have fee_of : ∀ pc (hpc : pc < pf.code.size), ∃ ins fee, pf.code[pc]? = some ins ∧
                feeUnits cfg pf.gas[pc]? = some fee ∧
                recordOf (L[pc]?.getD []) (H[pc]?.getD 0) fee pc ins = recs[pc]? := by
              intro pc hpc
              have := hall pc (by simpa using hpc)
              simp only [List.getElem_range, recordAt] at this
              revert this
              have hr : recs[pc]? = some (recs[pc]'(by omega)) := List.getElem?_eq_getElem (by omega)
              cases hc : pf.code[pc]? with
              | none => intro e; simp [hr] at e
              | some ins =>
                cases hfu : feeUnits cfg pf.gas[pc]? with
                | none => intro e; simp [hr] at e
                | some fee => intro e; exact ⟨ins, fee, rfl, rfl, e⟩
            refine ⟨pf, {
              func := hpf, params := g1, nloc := g1a, results := g1b,
              resTypes := ?_, locTypes := ?_, codeLt := g5, gasSize := g5a,
              lsize := g6, hsize := g6a, l0 := g6b, h0 := g6c,
              verify := fun pc hpc => by have := g7 pc hpc; simp_all,
              hBound := fun pc hpc => by have := g7 pc hpc; simp_all,
              records := by simp [hlen],
              recs := ?_, arity := rfl, resTag := rfl, localTags := rfl, locIdx := ?_ }⟩
            · intro t ht
              rw [Array.all_eq_true] at g2
              obtain ⟨x, hx, rfl⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp ht)
              have := g2 x hx
              revert this
              cases pf.type.results[x] <;> decide
            · intro t ht
              rw [Array.all_eq_true] at g3
              obtain ⟨x, hx, rfl⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp ht)
              have := g3 x hx
              revert this
              cases pf.locals[x] <;> decide
            · intro pc hpc
              obtain ⟨ins, fee, h1, h2, h3⟩ := fee_of pc hpc
              refine ⟨ins, fee, h1, h2, ?_, by simpa using h3⟩
              apply foldl_max_ge
              simp only [List.mem_map]
              refine ⟨recs[pc]'(by omega), List.getElem_mem _, ?_⟩
              rw [List.getElem?_eq_getElem (by omega)] at h3
              exact (recordOf_fee h3)
            · intro i hi x hx
              rw [Array.all_eq_true] at g4
              obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp hi)
              have := g4 k hk
              rcases hx with e | e | e <;> rw [e] at this <;> simpa using this

end WasmBase
