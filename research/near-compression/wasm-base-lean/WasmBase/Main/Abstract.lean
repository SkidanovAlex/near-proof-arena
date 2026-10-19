import WasmBase.StepCtrl
import WasmBase.StepOps
import WasmBase.Chain
import WasmBase.Channel
/-!
# WasmBase.Main.Abstract — the execution theorem from per-row facts

The STATE bus gives a permutation `init :: outs ~ final :: ins` over the active instruction rows,
the CH bus gives `init_locals ++ produced ~ final_values ++ consumed`.  Each active row satisfies
`RowFacts`: its local guarantee as a spec step (`RowSpec`, proven per chip from the local AIR
soundness lemmas and the spec step lemmas) plus a few timestamp facts.  From these alone:
the rows form one path (`chain`), the channel is sound (`ChanOK`), and by induction along the path
the spec `run` from the initial state finishes after exactly `#rows` steps, with the gas, the
final operand stack and the final locals given by the boundary.
-/
namespace WasmBase
open NearSpecV3.Wasm
set_option linter.unusedSimpArgs false

/-- STATE message `[pc, ts, S, halted]`. -/
def stMsg (pc t S h : Nat) : List F := [(pc : F), (t : F), (S : F), (h : F)]

/-- The level (timestamp) field of a STATE message. -/
def lvl (m : List F) : F := m.getD 1 0
/-- The gas-units field of a STATE message. -/
def gasF (m : List F) : F := m.getD 2 0

/-- What one active instruction row guarantees about the spec, given the spec state it is related
to at the row's input STATE message and given that the messages it consumes are live. -/
def RowSpec (X : Ctx) (inS outS : List F) (cons prod : List Msg) : Prop :=
  ∀ (s : St) (f : Frame) (tps tpl : Nat → Nat) (t pc S : Nat) (live : Msg → Prop),
    RelW X s f tps tpl t pc S live → inS = stMsg pc t S 0 → (∀ x ∈ cons, live x) →
    t + 1 < ZkFormal.Algebra.P → S + X.ck.maxFee < ZkFormal.Algebra.P → X.g0 < 2 ^ 64 →
    ∃ pc' fee hb, fee ≤ X.ck.maxFee ∧ hb ≤ 1 ∧ outS = stMsg pc' (t + 1) (S + fee) hb ∧
      (X.R * (S + fee) ≤ X.g0 →
        (hb = 0 → ∃ s', step X.cfg X.p s = .cont s' ∧
          Rel X s' (t + 1) pc' (S + fee) (stepLive live cons prod)) ∧
        (hb = 1 → ∃ sN, step X.cfg X.p s = .fin sN ∧ sN.frames = [] ∧
          X.R * (S + fee) + sN.gas.g = X.g0 ∧
          ∀ x, stepLive live cons prod x ↔ x ∈ stackView sN.stack tps ∨ x ∈ localView f.locals tpl))

structure RowFacts (X : Ctx) (inS outS : List F) (cons prod : List Msg) : Prop where
  spec : RowSpec X inS outS cons prod
  halt0 : inS.getD 3 0 = 0
  tsOut : lvl outS = lvl inS + 1
  gasOut : ∃ fee, fee ≤ X.ck.maxFee ∧ gasF outS = gasF inS + (fee : F)
  consT : ∀ x ∈ cons, ∃ n, n < 2 ^ 30 ∧ ((x.tp + 1 + n : Nat) : F) = lvl inS
  prodT : ∀ x ∈ prod, x.tp < ZkFormal.Algebra.P ∧ ((x.tp : Nat) : F) = lvl inS
  prodNd : prod.Nodup

/-! ## List helpers -/

theorem perm_map_lift {ρ β : Type} [DecidableEq ρ] (g : ρ → β) :
    ∀ (es : List β) (act : List ρ), es.Perm (act.map g) → ∃ rs : List ρ, rs.Perm act ∧ es = rs.map g := by
  intro es
  induction es with
  | nil => intro act h; exact ⟨[], by simpa using h.symm, rfl⟩
  | cons e es ih =>
    intro act h
    have he : e ∈ act.map g := h.subset List.mem_cons_self
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp he
    have hp : act.Perm (r :: act.erase r) := List.perm_cons_erase hr
    have h2 : (g r :: es).Perm (g r :: (act.erase r).map g) := h.trans (by simpa using hp.map g)
    obtain ⟨rs, hrs, rfl⟩ := ih (act.erase r) (List.Perm.cons_inv h2)
    exact ⟨r :: rs, (hrs.cons r).trans hp.symm, rfl⟩

theorem path_link {α : Type} : ∀ (es : List (α × α)) (a b : α), IsPath a es b →
    (∀ k (hk : k + 1 < es.length), (es[k + 1]'hk).1 = (es[k]'(by omega)).2) ∧
    (∀ h : 0 < es.length, (es[0]'h).1 = a ∧ (es[es.length - 1]'(by omega)).2 = b) ∧
    (es.length = 0 → a = b) := by
  intro es
  induction es with
  | nil => intro a b h; simp only [IsPath] at h; simp [h]
  | cons e es ih =>
    intro a b h
    obtain ⟨he, hp⟩ := h
    obtain ⟨i1, i2, i3⟩ := ih e.2 b hp
    refine ⟨?_, ?_, by simp⟩
    · intro k hk
      cases k with
      | zero =>
        cases es with
        | nil => simp at hk
        | cons e' es' => exact (i2 (by simp)).1
      | succ k => simpa using i1 k (by simpa using hk)
    · intro _
      refine ⟨he, ?_⟩
      cases es with
      | nil => simpa [IsPath] using hp
      | cons e' es' =>
        have := (i2 (by simp)).2
        simpa using this

theorem run_cont {cfg : NearCfg} {p : Prepared} {s s' : St} (h : step cfg p s = .cont s') (n : Nat) :
    run cfg p (n + 1) s = run cfg p n s' := by
  simp only [run, h]

theorem stMsg_inj {pc t S h pc' t' S' h' : Nat} (e : stMsg pc t S h = stMsg pc' t' S' h') :
    (pc : F) = pc' ∧ (t : F) = t' ∧ (S : F) = S' ∧ (h : F) = h' := by
  simp only [stMsg, List.cons.injEq, and_true] at e
  exact e

theorem nodup_flatten_of {α : Type} (L : List (List α)) (hnd : ∀ j (hj : j < L.length), (L[j]).Nodup)
    (hdis : ∀ i j (hi : i < L.length) (hj : j < L.length), i ≠ j → ∀ x ∈ L[i], x ∉ L[j]) :
    L.flatten.Nodup := by
  induction L with
  | nil => simp
  | cons l L ih =>
    simp only [List.flatten_cons, List.nodup_append]
    refine ⟨hnd 0 (by simp), ih (fun j hj => by have h := hnd (j + 1) (by simp; omega); rwa [List.getElem_cons_succ] at h)
      (fun i j hi hj hij => by
        have h := hdis (i + 1) (j + 1) (by simp; omega) (by simp; omega) (by omega)
        rwa [List.getElem_cons_succ, List.getElem_cons_succ] at h), ?_⟩
    intro x hx y hy hxy
    subst hxy
    obtain ⟨j, hj, hyj⟩ := mem_flatten_iff.mp hy
    exact hdis 0 (j + 1) (by simp) (by simp; omega) (by omega) x (by simpa using hx) (by simpa using hyj)

/-! ## The abstract execution theorem -/

section
variable (X : Ctx) {ρ : Type} [DecidableEq ρ] (act : List ρ) (inS outS : ρ → List F)
  (cons prod : ρ → List Msg) (init fin : List Msg) (pcf N Sf : F)

theorem exec_of_rows
    (hrows : ∀ r ∈ act, RowFacts X (inS r) (outS r) (cons r) (prod r))
    (hst : (stMsg 0 1 0 0 :: act.map outS).Perm ([pcf, N, Sf, 1] :: act.map inS))
    (hch : (init ++ act.flatMap prod).Perm (fin ++ act.flatMap cons))
    (hinit : init.Nodup) (hinitTp : ∀ x ∈ init, x.tp = 0)
    (hlen : act.length < 2 ^ 28)
    (hfee : (act.length + 1) * (X.ck.maxFee + 1) < ZkFormal.Algebra.P)
    (hgas : X.R * Sf.toNat ≤ X.g0) (hg64 : X.g0 < 2 ^ 64)
    {s0 : St} {f0 : Frame} (h0 : RelW X s0 f0 (fun _ => 0) (fun _ => 0) 1 0 0 (· ∈ init)) :
    ∃ sN tps tpl locs, run X.cfg X.p act.length s0 = .fin sN ∧ sN.frames = [] ∧
      X.R * Sf.toNat + sN.gas.g = X.g0 ∧ act.length + 1 = N.toNat ∧
      ∀ x, x ∈ fin ↔ x ∈ stackView sN.stack tps ∨ x ∈ localView locs tpl := by
  have hP' := P_val
  -- (A) the chain
  let g : ρ → List F × List F := fun r => (inS r, outS r)
  have hE1 : (act.map g).map Prod.snd = act.map outS := by simp [g, List.map_map]
  have hE2 : (act.map g).map Prod.fst = act.map inS := by simp [g, List.map_map]
  have hstepE : ∀ e ∈ act.map g, lvl e.2 = lvl e.1 + 1 := by
    intro e he
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp he
    exact (hrows r hr).tsOut
  obtain ⟨es, hes, hpath⟩ := chain (act.map g) (stMsg 0 1 0 0) [pcf, N, Sf, 1] lvl
    (by rw [hE1, hE2]; exact hst) hstepE (by simp; omega)
  obtain ⟨rs, hrs, rfl⟩ := perm_map_lift g es act hes
  have hlenrs : rs.length = act.length := hrs.length_eq
  have hmem : ∀ k (hk : k < rs.length), rs[k] ∈ act := fun k hk => hrs.subset (List.getElem_mem hk)
  have RF : ∀ k (hk : k < rs.length), RowFacts X (inS rs[k]) (outS rs[k]) (cons rs[k]) (prod rs[k]) :=
    fun k hk => hrows _ (hmem k hk)
  obtain ⟨lk, lfin⟩ := path_levels lvl (rs.map g) _ _ hpath (fun e he => hstepE e (hes.subset he))
  obtain ⟨link, ends, _⟩ := path_link (rs.map g) _ _ hpath
  simp only [List.length_map, List.getElem_map] at lk lfin link ends
  have l0 : lvl (stMsg 0 1 0 0) = 1 := rfl
  have lvlk : ∀ k (hk : k < rs.length), lvl (inS rs[k]) = ((k + 1 : Nat) : F) := by
    intro k hk; rw [lk k hk, l0, Lean.Grind.Semiring.natCast_add, cast_one]; grind
  have hpos : 0 < rs.length := by
    refine Nat.pos_of_ne_zero fun h0' => ?_
    have := (path_link (rs.map g) _ _ hpath).2.2 (by simp [h0'])
    simp only [stMsg, List.cons.injEq] at this
    exact absurd this.2.2.2.1 (by decide)
  have hN : act.length + 1 = N.toNat := by
    have : N = ((rs.length + 1 : Nat) : F) := by
      have e : lvl [pcf, N, Sf, 1] = N := rfl
      rw [← e, lfin, l0, Lean.Grind.Semiring.natCast_add, cast_one]; grind
    rw [this, Fp.toNat_cast_of_lt (by omega), hlenrs]
  -- position messages: `pos k` is the STATE message entering step `k` (the final one at `k = n`)
  let pos : Nat → List F := fun k => if h : k < rs.length then inS rs[k] else [pcf, N, Sf, 1]
  have pos_in : ∀ k (hk : k < rs.length), pos k = inS rs[k] := fun k hk => by simp [pos, hk]
  have pos_out : ∀ k (hk : k < rs.length), pos (k + 1) = outS rs[k] := by
    intro k hk
    by_cases h1 : k + 1 < rs.length
    · simp only [pos, h1, dite_true]; exact link k h1
    · have : k = rs.length - 1 := by omega
      subst this
      simp only [pos, h1, dite_false]; exact (ends hpos).2.symm
  have pos0 : pos 0 = stMsg 0 1 0 0 := by rw [pos_in 0 hpos]; exact (ends hpos).1
  -- gas units along the path: no wrap-around, monotone up to `Sf`
  have gasB : ∀ k, k ≤ rs.length → (gasF (pos k)).toNat ≤ k * X.ck.maxFee ∧
      ∀ j, k ≤ j → j ≤ rs.length → (gasF (pos k)).toNat ≤ (gasF (pos j)).toNat := by
    have step1 : ∀ k (hk : k < rs.length), (gasF (pos k)).toNat ≤ k * X.ck.maxFee →
        ∃ fee, fee ≤ X.ck.maxFee ∧ (gasF (pos (k + 1))).toNat = (gasF (pos k)).toNat + fee := by
      intro k hk hb
      obtain ⟨fee, hfl, hfe⟩ := (RF k hk).gasOut
      refine ⟨fee, hfl, ?_⟩
      rw [pos_out k hk, hfe, ← pos_in k hk]
      conv => lhs; rw [← Fp.cast_toNat (gasF (pos k))]
      rw [← Lean.Grind.Semiring.natCast_add, Fp.toNat_cast_of_lt]
      have : (k + 1) * (X.ck.maxFee + 1) ≤ (act.length + 1) * (X.ck.maxFee + 1) := Nat.mul_le_mul_right _ (by omega)
      have : k * X.ck.maxFee + X.ck.maxFee ≤ (k + 1) * (X.ck.maxFee + 1) := by
        rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]; omega
      omega
    have bnd : ∀ k, k ≤ rs.length → (gasF (pos k)).toNat ≤ k * X.ck.maxFee := by
      intro k
      induction k with
      | zero => intro _; rw [pos0]; simp [gasF, stMsg]; rfl
      | succ k ih =>
        intro hk
        have ih' := ih (by omega)
        obtain ⟨fee, hfl, he⟩ := step1 k (by omega) ih'
        rw [he, Nat.succ_mul]
        omega
    refine fun k hk => ⟨bnd k hk, ?_⟩
    intro j hkj hjn
    induction j with
    | zero => have : k = 0 := by omega
              subst this; exact Nat.le_refl _
    | succ j ih =>
      by_cases hkj' : k = j + 1
      · subst hkj'; exact Nat.le_refl _
      · have := ih (by omega) (by omega)
        obtain ⟨fee, hfl, he⟩ := step1 j (by omega) (bnd j (by omega))
        rw [he]
        omega
  have posN : pos rs.length = [pcf, N, Sf, 1] := by simp [pos]
  have gasN : (gasF (pos rs.length)).toNat = Sf.toNat := by rw [posN]; rfl
  -- (B) the channel
  let prodL := rs.map prod
  let consL := rs.map cons
  have hpTp : ∀ k (hk : k < rs.length), ∀ x ∈ prod rs[k], x.tp = k + 1 := by
    intro k hk x hx
    obtain ⟨h1, h2⟩ := (RF k hk).prodT x hx
    rw [lvlk k hk] at h2
    exact natEq h2 h1 (by omega)
  have hpermC : (init ++ prodL.flatten).Perm (fin ++ consL.flatten) := by
    have e1 : prodL.flatten = rs.flatMap prod := by simp [prodL, List.flatMap]
    have e2 : consL.flatten = rs.flatMap cons := by simp [consL, List.flatMap]
    rw [e1, e2]
    exact ((hrs.flatMap_right prod).append_left init).trans (hch.trans
      ((hrs.flatMap_right cons).symm.append_left fin))
  have tpBound : ∀ x ∈ fin ++ consL.flatten, x.tp ≤ rs.length := by
    intro x hx
    rcases List.mem_append.mp (hpermC.symm.subset hx) with h | h
    · rw [hinitTp x h]; omega
    · obtain ⟨j, hj, hxj⟩ := mem_flatten_iff.mp h
      simp only [prodL, List.length_map, List.getElem_map] at hj hxj
      rw [hpTp j hj x hxj]; omega
  have C : ChanOK init fin prodL consL Msg.tp := by
    refine ⟨by simp [prodL, consL], hpermC, ?_, hinitTp, ?_, ?_⟩
    · rw [List.nodup_append]
      refine ⟨hinit, nodup_flatten_of _ (fun j hj => by simpa [prodL] using (RF j (by simpa [prodL] using hj)).prodNd) ?_, ?_⟩
      · intro i j hi hj hij x hx hx'
        simp only [prodL, List.length_map, List.getElem_map] at hi hj hx hx'
        have := hpTp i hi x hx; have := hpTp j hj x hx'; omega
      · intro x hx y hy hxy
        subst hxy
        obtain ⟨j, hj, hxj⟩ := mem_flatten_iff.mp hy
        simp only [prodL, List.length_map, List.getElem_map] at hj hxj
        have := hpTp j hj x hxj; have := hinitTp x hx; omega
    · intro k hk x hx
      simp only [prodL, List.length_map, List.getElem_map] at hk hx
      exact hpTp k hk x hx
    · intro k hk x hx
      simp only [consL, List.length_map, List.getElem_map] at hk hx
      obtain ⟨m, hm, he⟩ := (RF k hk).consT x hx
      rw [lvlk k hk] at he
      have hb := tpBound x (List.mem_append_right _ (mem_flatten_iff.mpr ⟨k, by simpa [consL] using hk, by simpa [consL] using hx⟩))
      have := natEq he (by omega) (by omega)
      omega
  -- (C) induction along the path
  have IH : ∀ k (hk : k < rs.length), ∃ s pc, (∀ m, run X.cfg X.p (m + k) s0 = run X.cfg X.p m s) ∧
      inS rs[k] = stMsg pc (k + 1) (gasF (pos k)).toNat 0 ∧
      Rel X s (k + 1) pc (gasF (pos k)).toNat (live init prodL consL k) := by
    intro k
    induction k with
    | zero =>
      intro hk
      refine ⟨s0, 0, fun m => rfl, ?_, ?_⟩
      · rw [← pos_in 0 hk, pos0]; rfl
      · rw [pos0]
        refine Rel_of_RelW_congr h0 ?_
        funext x; simp [live, prodBefore, consBefore]
    | succ k ih =>
      intro hk
      obtain ⟨s, pc, hrun, hin, f, tps, tpl, R⟩ := ih (by omega)
      have gb := (gasB k (by omega)).1
      have hm : (k + 1) * (X.ck.maxFee + 1) ≤ (act.length + 1) * (X.ck.maxFee + 1) := Nat.mul_le_mul_right _ (by omega)
      have hS : (gasF (pos k)).toNat + X.ck.maxFee < ZkFormal.Algebra.P := by
        have : k * X.ck.maxFee + X.ck.maxFee ≤ (k + 1) * (X.ck.maxFee + 1) := by
          rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]; omega
        omega
      have hlive : ∀ x ∈ cons rs[k], live init prodL consL k x := fun x hx =>
        C.consumed_live (k := k) (by simp [consL]; omega) (by simpa [consL] using hx)
      obtain ⟨pc', fee, hb, hfl, hbl, hout, hspec⟩ :=
        (RF k (by omega)).spec s f tps tpl (k + 1) pc _ _ R hin hlive (by omega) hS hg64
      have hout' : pos (k + 1) = stMsg pc' (k + 1 + 1) ((gasF (pos k)).toNat + fee) hb := by
        rw [pos_out k (by omega), hout]
      have hg1 : (gasF (pos (k + 1))).toNat = (gasF (pos k)).toNat + fee := by
        rw [hout']; simp only [gasF, stMsg, List.getD_cons_succ, List.getD_cons_zero]
        exact Fp.toNat_cast_of_lt (by simp only [gasF] at hS; omega)
      have hgas' : X.R * ((gasF (pos k)).toNat + fee) ≤ X.g0 := by
        have := (gasB (k + 1) (by omega)).2 rs.length (by omega) (Nat.le_refl _)
        rw [gasN, hg1] at this
        exact Nat.le_trans (Nat.mul_le_mul_left _ this) hgas
      have hb0 : hb = 0 := by
        have h3 : (pos (k + 1)).getD 3 0 = 0 := by rw [pos_in (k + 1) hk]; exact (RF (k + 1) hk).halt0
        rw [hout'] at h3
        simp only [stMsg, List.getD_cons_succ, List.getD_cons_zero] at h3
        exact natEq (h3.trans rfl) (by omega) (by decide)
      obtain ⟨s', hs', f', tps', tpl', R'⟩ := (hspec hgas').1 hb0
      refine ⟨s', pc', ?_, ?_, ?_⟩
      · intro m
        rw [show m + (k + 1) = (m + 1) + k by omega, hrun, run_cont hs']
      · rw [hg1, ← pos_in (k + 1) hk, hout', hb0]
      · rw [hg1]
        refine Rel_of_RelW_congr R' ?_
        funext x
        have := (C.live_succ (k := k) (by simp [consL]; omega) x).symm
        simp only [consL, prodL, List.getElem_map] at this
        exact propext this
  -- (D) the last step halts
  obtain ⟨s, pc, hrun, hin, f, tps, tpl, R⟩ := IH (rs.length - 1) (by omega)
  have gb := (gasB (rs.length - 1) (by omega)).1
  have hS : (gasF (pos (rs.length - 1))).toNat + X.ck.maxFee < ZkFormal.Algebra.P := by
    have : (rs.length - 1) * X.ck.maxFee + X.ck.maxFee ≤ rs.length * (X.ck.maxFee + 1) := by
      have : (rs.length - 1) * X.ck.maxFee + X.ck.maxFee = rs.length * X.ck.maxFee := by
        rw [← Nat.succ_mul, show (rs.length - 1).succ = rs.length by omega]
      rw [this, Nat.mul_add]; omega
    have : rs.length * (X.ck.maxFee + 1) ≤ (act.length + 1) * (X.ck.maxFee + 1) := Nat.mul_le_mul_right _ (by omega)
    omega
  have hlive : ∀ x ∈ cons rs[rs.length - 1], live init prodL consL (rs.length - 1) x := fun x hx =>
    C.consumed_live (k := rs.length - 1) (by simp [consL]; omega) (by simpa [consL] using hx)
  obtain ⟨pc', fee, hb, hfl, hbl, hout, hspec⟩ :=
    (RF (rs.length - 1) (by omega)).spec s f tps tpl (rs.length - 1 + 1) pc _ _ R hin hlive (by omega) hS hg64
  have hout' : pos rs.length = stMsg pc' (rs.length - 1 + 1 + 1) ((gasF (pos (rs.length - 1))).toNat + fee) hb := by
    rw [show rs.length = rs.length - 1 + 1 by omega, pos_out (rs.length - 1) (by omega), hout]
    simp only [show rs.length - 1 + 1 - 1 = rs.length - 1 by omega]
  rw [posN] at hout'
  have e := hout'.symm
  simp only [stMsg, List.cons.injEq, and_true] at e
  obtain ⟨-, -, eS, eH⟩ := e
  have hb1 : hb = 1 := natEq (eH.trans rfl) (by omega) (by decide)
  have hSf : (gasF (pos (rs.length - 1))).toNat + fee = Sf.toNat := by
    rw [← eS, Fp.toNat_cast_of_lt (by omega)]
  have hgas' : X.R * ((gasF (pos (rs.length - 1))).toNat + fee) ≤ X.g0 := by rw [hSf]; exact hgas
  obtain ⟨sN, hsN, hfr, hg, hview⟩ := (hspec hgas').2 hb1
  refine ⟨sN, tps, tpl, f.locals, ?_, hfr, by rw [← hSf]; exact hg, hN, ?_⟩
  · rw [← hlenrs, show rs.length = 0 + 1 + (rs.length - 1) by omega, hrun]
    simp only [run, hsN]
  · intro x
    rw [← hview x, ← C.live_final x]
    have := C.live_succ (k := rs.length - 1) (by simp [consL]; omega) x
    simp only [consL, List.length_map, show rs.length - 1 + 1 = rs.length by omega] at this ⊢
    rw [this]; simp only [stepLive, prodL, List.getElem_map]
end

end WasmBase
