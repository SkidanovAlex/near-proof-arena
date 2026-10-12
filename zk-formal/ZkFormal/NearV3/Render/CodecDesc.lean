import ZkFormal.NearV3.Render.CodecRowMod
import ZkFormal.NearV3.Render.CodecHeader
import ZkFormal.NearV3.Render.CodecRecInt
import ZkFormal.NearV3.Render.CodecEndInt

/-!
# Row descriptors of the honest codec table (table 11) and local legality on one row

`Desc` names an honest row of the frozen `Sched.Codec.table` by its assignment parameters (header row
`p`, record row `(f, gg)` of link `R.kk` with its byte/accumulator values, sanity-hash row `j`,
`sha256(all_shards)` row `j`); `Desc.asg` is the assignment (`CodecDefs`), `Desc.row` its array.
`Desc.Valid` collects the row lemmas' own premises (cells `< P` included), `Desc.Adj` the admissible
successors (exactly what the integer-pass lemmas ask of the next row), `Final` (followed by zero
padding) and `FirstOk` (may sit on row 0).

`local_at`: every constraint of `Sched.Codec.table` vanishes on a row whose cells (and successor's
cells) are the honest assignments — integer pass (`CodecHeader`, `CodecRecInt`, `CodecEndInt`) plus
the modular pass (`CodecRowMod`).  `mult_bits`: every interaction multiplicity on an honest row is a
bit.
-/
namespace ZkFormal.NearV3.Render.Cdc
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen
open ZkFormal.NearV3.Sched.Codec ZkFormal.Chacha.Table.E ZkFormal.NearV3.Candidates.SchedSetAll

set_option maxRecDepth 65536

/-- A row of the honest codec table. -/
inductive Desc where
  | hdr (I : Inst) (p : Nat)
  | record (I : Inst) (R : Rec) (f gg bpo bpr apv apostv bigv : Nat)
  | hash (I : Inst) (dig hpre : List Nat) (j : Nat)
  | ash (I : Inst) (ash : List Nat) (j : Nat)

/-- Instance-level premises. -/
def InstOk (I : Inst) : Prop :=
  I.tv < P ∧ I.N < 65536 ∧ (I.n : Int) * I.n = I.N ∧ I.base < 2 ^ 24 ∧ I.fair < 2 ^ 24

/-- Record-row premises (own row). -/
def RecOk (I : Inst) (R : Rec) (f gg bpo bpr bigv apostv : Nat) : Prop :=
  f < 3 ∧ gg < 8 ∧ R.kk < I.N ∧ R.iklv = inv (fsub R.kk (I.N - 1)) ∧ bpo < 256 ∧ bpr < 256 ∧
  (f < 2 → bpr = b2n I.pres * bpo) ∧ (I.pres = false → bpr = 0) ∧ (f = 2 → 3 ≤ gg → bpo = 0) ∧
  bigv ≤ 1 ∧ (R.hasC = false → apRv R = 0) ∧ (R.hasC = false → bigRv R = 0) ∧
  (f = 2 → gg = 7 → apostv = R.afin ∧ R.ft < 2 ^ 24 ∧ b2n R.al * I.base ≤ a1v I R)

namespace Desc

def asg : Desc → List (Nat × Nat)
  | hdr I p => hdrA I p
  | record I R f gg bpo bpr apv apostv bigv => recA I R f gg bpo bpr apv apostv bigv
  | hash I dig hpre j => hashA I dig hpre j
  | ash I a j => ashA I a j

def row (d : Desc) : Array Nat := setAll Codec.width d.asg

def inst : Desc → Inst
  | hdr I _ => I
  | record I .. => I
  | hash I .. => I
  | ash I .. => I

/-- The row lemmas' own premises. -/
def Valid (d : Desc) : Prop :=
  (∀ q ∈ d.asg, q.2 < P) ∧ InstOk d.inst ∧
  match d with
  | hdr _ p => p ≤ 4
  | record I R f gg bpo bpr _ apostv bigv => RecOk I R f gg bpo bpr bigv apostv
  | hash _ dig hpre j => j < 32 ∧ dig.getD j 0 < 256 ∧ hpre.getD j 0 < 256
  | ash _ _ j => j < 32

/-- The admissible successors. -/
def Adj : Desc → Desc → Prop
  | hdr I p, hdr I' p' => p < 4 ∧ I = I' ∧ p' = p + 1
  | hdr I p, record I' R f gg _ _ _ _ _ => p = 4 ∧ I = I' ∧ R.kk = 0 ∧ f = 0 ∧ gg = 0
  | record I R f gg bpo bpr apv apostv bigv, record I' R' f' gg' _ _ apv' apostv' bigv' =>
      I = I' ∧
      ((gg < 7 ∧ R = R' ∧ f = f' ∧ gg' = gg + 1 ∧
        (f = 2 → apv' = apv + (if gg < 3 then 256 ^ gg * bpr else 0) ∧
          apostv' = apostv + (if gg < 3 then 256 ^ gg * bpo else 0) ∧
          bigv' = if bigv = 1 ∨ (3 ≤ gg ∧ bpr ≠ 0) then 1 else 0)) ∨
       (gg = 7 ∧ f < 2 ∧ R = R' ∧ f' = f + 1 ∧ gg' = 0 ∧ (f = 1 → apv' = 0 ∧ apostv' = 0 ∧ bigv' = 0)) ∨
       (gg = 7 ∧ f = 2 ∧ f' = 0 ∧ gg' = 0 ∧ R'.kk = R.kk + 1 ∧ R.kk + 1 < I.N))
  | record I R f gg _ _ _ _ _, hash I' _ _ j => I = I' ∧ f = 2 ∧ gg = 7 ∧ R.kk + 1 = I.N ∧ j = 0
  | hash I dig hpre j, hash I' dig' hpre' j' => j < 31 ∧ I = I' ∧ dig = dig' ∧ hpre = hpre' ∧ j' = j + 1
  | hash I _ _ j, ash I' _ j' => j = 31 ∧ I = I' ∧ j' = 0
  | ash I a j, ash I' a' j' => j < 31 ∧ I = I' ∧ a = a' ∧ j' = j + 1
  | ash _ _ j, hdr _ p => j = 31 ∧ p = 0
  | _, _ => False

/-- May be followed by zero padding. -/
def Final : Desc → Prop
  | ash _ _ j => j = 31
  | _ => False

/-- May sit on row 0. -/
def FirstOk : Desc → Prop
  | hdr _ p => p = 0
  | _ => False

end Desc

open Desc

def asgO : Option Desc → List (Nat × Nat)
  | none => []
  | some d => d.asg

def AdjO (d : Desc) : Option Desc → Prop
  | none => d.Final
  | some d' => d.Adj d'

theorem b2n_le1 (b : Bool) : b2n b ≤ 1 := by cases b <;> decide

section
variable {tr : Trace Fp} {t r : Nat} {pub : List Fp}

/-- **Every constraint on an honest row with an admissible successor.** -/
theorem local_at (d : Desc) (nx : Option Desc) (hv : d.Valid) (hadj : AdjO d nx)
    (hcur : ∀ c, (tenv tr t r pub).cur c = lookup d.asg c 0)
    (hnxt : ∀ c, (tenv tr t r pub).nxt c = lookup (asgO nx) c 0)
    (hfi : (tenv tr t r pub).first = 0 ∨ d.FirstOk) (hl : (tenv tr t r pub).last = 0) :
    ∀ e ∈ constraints, e.eval tr t r pub = 0 := by
  obtain ⟨_, ⟨htv, hN, hNN, hb, hfa⟩, hk⟩ := hv
  cases d with
  | hdr I p =>
    simp only [Desc.inst] at htv hN hNN hb hfa
    have hp : p ≤ 4 := hk
    refine row_local ?_ (hdr_mod I p hp htv hcur)
    cases nx with
    | none => exact hadj.elim
    | some d' =>
      cases d' with
      | hdr I' p' =>
        obtain ⟨hp4, rfl, rfl⟩ := hadj
        have hfp : p = 0 ∨ (tenv tr t r pub).first = 0 := by
          rcases hfi with h | h
          · exact Or.inr h
          · exact Or.inl h
        exact hdr_int I p hp4 _ hcur hnxt hl hfp hN hNN hb hfa
      | record I' R f gg bpo bpr apv apostv bigv =>
        obtain ⟨rfl, rfl, hk0, rfl, rfl⟩ := hadj
        have hf0 : (tenv tr t r pub).first = 0 := hfi.resolve_right (by simp [Desc.FirstOk])
        exact hdr_last_int I R bpo bpr apv apostv bigv _ hcur hnxt hl hf0 hk0 hN hNN hb hfa
      | _ => exact hadj.elim
  | record I R f gg bpo bpr apv apostv bigv =>
    simp only [Desc.inst] at htv hN hNN hb hfa
    obtain ⟨hf, hg, hkN, hikl, hbpo, hbpr, hid, hpz0, hpz, hbig1, hA0r, hA0b, hend⟩ := hk
    have hf0 : (tenv tr t r pub).first = 0 := hfi.resolve_right (by simp [Desc.FirstOk])
    have hNP : I.N ≤ P := by unfold P; omega
    have hbP : bpr < P := by unfold P; omega
    cases nx with
    | none => exact hadj.elim
    | some d' =>
      cases d' with
      | record I' R' f' gg' bpo' bpr' apv' apostv' bigv' =>
        obtain ⟨rfl, hc⟩ := hadj
        rcases hc with ⟨hg7, rfl, rfl, rfl, hacc⟩ | ⟨rfl, hf2, rfl, rfl, rfl, h0⟩ |
            ⟨rfl, rfl, rfl, rfl, hk1, hkN1⟩
        · refine row_local ?_ (rec_mod I R f gg bpo bpr apv apostv bigv hf hg htv hkN hNP hbP hikl hcur ?_)
          · exact rec_in_int I R f gg bpo bpr apv apostv bigv bpo' bpr' apv' apostv' bigv' hf hg7 _ hcur
              hnxt hl hf0 hbpo hbpr hid hpz0 hpz (fun h => (hacc h).1) (fun h => (hacc h).2.1)
              (fun h => (hacc h).2.2) hbig1 hA0r hA0b
          · intro h2 _
            subst h2
            rw [hnxt]
            simp only [asgO, Desc.asg]
            cdc_cell
        · refine row_local ?_ (rec_mod I R f 7 bpo bpr apv apostv bigv hf hg htv hkN hNP hbP hikl hcur
            (fun h => absurd h (by omega)))
          exact rec_fend_int I R f bpo bpr apv apostv bigv bpo' bpr' apv' apostv' bigv' hf2 _ hcur hnxt
            hl hf0 hbpo hbpr (hid hf2) hpz0 h0 hA0r hA0b
        · obtain ⟨he1, he2, he3⟩ := hend rfl rfl
          refine row_local ?_ (rec_mod I R 2 7 bpo bpr apv apostv bigv hf hg htv hkN hNP hbP hikl hcur
            (fun _ h => absurd h (by omega)))
          exact rec_end_int I R R' bpo bpr apv apostv bigv bpo' bpr' apv' apostv' bigv' _ hcur hnxt hl
            hf0 (hpz rfl (by omega)) hbpr hpz0 hbig1 he1 hk1 hkN1 he2 he3 hA0r hA0b
      | hash I' dig hpre j =>
        obtain ⟨rfl, rfl, rfl, hk1, rfl⟩ := hadj
        obtain ⟨he1, he2, he3⟩ := hend rfl rfl
        refine row_local ?_ (rec_mod I R 2 7 bpo bpr apv apostv bigv hf hg htv hkN hNP hbP hikl hcur
          (fun _ h => absurd h (by omega)))
        exact rec_last_int I R dig hpre bpo bpr apv apostv bigv _ hcur hnxt hl hf0
          (hpz rfl (by omega)) hbpr hpz0 hbig1 he1 hk1 he2 he3 hA0r hA0b
      | _ => exact hadj.elim
  | hash I dig hpre j =>
    simp only [Desc.inst] at htv hN hNN hb hfa
    obtain ⟨hj, hd, hp⟩ := hk
    have hf0 : (tenv tr t r pub).first = 0 := hfi.resolve_right (by simp [Desc.FirstOk])
    refine row_local ?_ (hash_mod I dig hpre j hj htv hcur)
    cases nx with
    | none => exact hadj.elim
    | some d' =>
      cases d' with
      | hash I' dig' hpre' j' =>
        obtain ⟨hj31, rfl, rfl, rfl, rfl⟩ := hadj
        exact hash_int I dig hpre j hj31 _ hcur hnxt hl hf0 hd hp
      | ash I' a j' =>
        obtain ⟨rfl, rfl, rfl⟩ := hadj
        exact hash_last_int I dig hpre a _ hcur hnxt hl hf0 hd hp
      | _ => exact hadj.elim
  | ash I a j =>
    simp only [Desc.inst] at htv hN hNN hb hfa
    have hj : j < 32 := hk
    have hf0 : (tenv tr t r pub).first = 0 := hfi.resolve_right (by simp [Desc.FirstOk])
    refine row_local ?_ (ash_mod I a j hj htv hcur)
    cases nx with
    | none =>
      have h31 : j = 31 := hadj
      subst h31
      exact ash_pad_int I a _ hcur hnxt hl hf0
    | some d' =>
      cases d' with
      | ash I' a' j' =>
        obtain ⟨hj31, rfl, rfl, rfl⟩ := hadj
        exact ash_int I a j hj31 _ hcur hnxt hl hf0
      | hdr I' p =>
        obtain ⟨rfl, rfl⟩ := hadj
        exact ash_last_int I I' a _ hcur hnxt hl hf0
      | _ => exact hadj.elim

theorem bit_eval {b : Expr} (h : zev (tenv tr t r pub) b = 0 ∨ zev (tenv tr t r pub) b = 1) :
    b.eval tr t r pub = 0 ∨ b.eval tr t r pub = 1 := by
  rcases h with h | h
  · left; rw [eval_eq, h]; rfl
  · right; rw [eval_eq, h]; rfl

set_option hygiene false in
macro "bit_close" : tactic => `(tactic| (
  simp only [zev_c, zev_add, encG, hcur, Desc.asg]
  try cdc_cell
  first | omega | ((repeat' split) <;> omega)))

set_option maxHeartbeats 0 in
/-- **Interaction multiplicities are bits on honest rows.** -/
theorem mult_bits (d : Desc) (hv : d.Valid) (hcur : ∀ c, (tenv tr t r pub).cur c = lookup d.asg c 0) :
    ∀ i ∈ interactions, ∀ b ∈ i.mult, b.eval tr t r pub = 0 ∨ b.eval tr t r pub = 1 := by
  intro i hi b hb
  apply bit_eval
  have hz := zt0_le d.inst
  have hp := b2n_le1 d.inst.pres
  simp only [interactions, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb <;> subst hb <;>
  cases d <;> simp only [Desc.inst] at hz hp
  all_goals first
    | bit_close
    | (rename_i I R f gg bpo bpr apv apostv bigv
       obtain ⟨_, _, hf, hg, _⟩ := hv
       have hu := b2n_le1 R.useC
       have hh := b2n_le1 R.hasC
       rcases (show f = 0 ∨ f = 1 ∨ f = 2 by omega) with rfl | rfl | rfl <;>
       rcases (show gg = 0 ∨ gg = 1 ∨ gg = 2 ∨ gg = 3 ∨ gg = 4 ∨ gg = 5 ∨ gg = 6 ∨ gg = 7 by omega)
         with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
       bit_close)

end

end ZkFormal.NearV3.Render.Cdc
