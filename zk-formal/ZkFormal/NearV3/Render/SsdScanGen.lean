import ZkFormal.NearV3.Render.SsdChain
import ZkFormal.NearV3.Candidates.ProcScanConvertedShape
import ZkFormal.NearV3.Candidates.ProcActualRunProjection

/-!
# The scan rows of one native scheduler run as a descriptor chain

`scanDescs R`: no rows without converted requests, else the param row and the 20 rows of every
converted request in `cid` order.  For a native run (`ActualRun.run I τ = .ok R`) the generator's
rows `Gen.Scan.rows R` are exactly these descriptors' rows, the converted requests are numbered
`cid = 0, 1, …` (`conv_indexed`), so the descriptors form a chain, every descriptor is valid,
and a nonempty block starts with a param row and ends with a request's last row.
-/
namespace ZkFormal.NearV3.Render.Ssd
open ZkFormal.Algebra ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Gen ZkFormal.NearV3.Candidates

/-! ## Converted requests are numbered consecutively -/

def Indexed (cs : Array CReq) : Prop := ∀ k (hk : k < cs.toList.length), (cs.toList[k]).cid = k

theorem conv_step (I : Input) (q : RawReq) (cs : Array CReq) (hs : Indexed cs)
    (out : ForInStep (Array CReq)) (h : ProcActualConverted.step I q cs = .ok out) :
    ExceptLoop.StepInv Indexed out := by
  unfold ProcActualConverted.step at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat first | cases h | split at h
  all_goals repeat first | cases h | split at h
  all_goals first
    | exact hs
    | (simp only [ExceptLoop.StepInv, Indexed, Array.toList_push, List.length_append,
         List.length_singleton]
       intro k hk
       by_cases hlt : k < cs.toList.length
       · rw [List.getElem_append_left hlt]; exact hs k hlt
       · have hk' : k = cs.toList.length := by omega
         subst hk'
         rw [List.getElem_append_right (by omega)]
         simp)

theorem conv_loop (I : Input) (cs : Array CReq)
    (h : forIn I.raw #[] (ProcActualConverted.step I) = .ok cs) : Indexed cs :=
  ExceptLoop.invariant I.raw (ProcActualConverted.step I) Indexed
    (fun q _ a ha out ho => conv_step I q a ha out ho) #[] cs (by intro k hk; simp at hk) h

set_option maxHeartbeats 400000 in
theorem conv_indexed (I : Input) (tau : Nat) (R : Run) (h : ActualRun.run I tau = .ok R) :
    ∀ k (hk : k < R.conv.length), R.conv[k].cid = k := by
  unfold ActualRun.run at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat first | cases h | split at h
  all_goals apply conv_loop I; assumption

/-! ## Descriptors -/

def scanDescs (R : Run) : List Desc :=
  if R.conv.isEmpty then [] else .param R :: R.conv.flatMap (fun c => (List.range 20).map (.req R c))

def ScanStart (d : Desc) : Prop := ∃ R, d = .param R
def ScanEnd (d : Desc) : Prop := ∃ R c, d = .req R c 19

theorem foldl_append_toList (l : List CReq) (f : CReq → Array (Array Nat)) (init : Array (Array Nat)) :
    (l.foldl (fun acc c => acc ++ f c) init).toList = init.toList ++ l.flatMap (fun c => (f c).toList) := by
  induction l generalizing init with
  | nil => simp
  | cons c l ih => simp [List.foldl_cons, ih, List.flatMap_cons, List.append_assoc]

theorem req_size (R : Run) (c : CReq) : (Scan.reqRows R c).size = 20 := by
  rw [ProcScanRequestState.native, ProcScanRequestState.size]

theorem req_toList (R : Run) (c : CReq) :
    (Scan.reqRows R c).toList = ((List.range 20).map (Desc.req R c)).map Desc.row := by
  rw [toList_range _ 20 (req_size R c), List.map_map]
  rfl

attribute [local irreducible] Scan.reqRows Gen.Scan.paramRow in
theorem scan_rows (R : Run) : (Gen.Scan.rows R).toList = (scanDescs R).map Desc.row := by
  by_cases h : R.conv.isEmpty
  · have h1 : Gen.Scan.rows R = #[] := by simp only [Gen.Scan.rows, h, ite_true]
    have h2 : scanDescs R = [] := by simp only [scanDescs, h, ite_true]
    rw [h1, h2]; rfl
  · have h1 : Gen.Scan.rows R = R.conv.foldl (fun acc c => acc ++ Scan.reqRows R c) #[Gen.Scan.paramRow R] := by
      simp only [Gen.Scan.rows, h, Bool.false_eq_true, ite_false]
    have h2 : scanDescs R = .param R :: R.conv.flatMap (fun c => (List.range 20).map (.req R c)) := by
      simp only [scanDescs, h, Bool.false_eq_true, ite_false]
    rw [h1, h2, foldl_append_toList, List.map_cons, List.map_flatMap]
    simp only [req_toList]
    rfl

theorem reqs_chain (R : Run) (cs : List CReq)
    (hcons : ∀ k (hk : k + 1 < cs.length), cs[k+1].cid = cs[k].cid + 1) :
    Chain (cs.flatMap (fun c => (List.range 20).map (Desc.req R c))) ∧
    (cs.flatMap (fun c => (List.range 20).map (Desc.req R c))).head? = cs.head?.map (fun c => .req R c 0) ∧
    (cs.flatMap (fun c => (List.range 20).map (Desc.req R c))).getLast? =
      cs.getLast?.map (fun c => .req R c 19) := by
  induction cs with
  | nil => exact ⟨chain_nil, rfl, rfl⟩
  | cons c cs ih =>
    have ih' := ih (fun k hk => by
      have := hcons (k+1) (by simp; omega)
      simpa using this)
    have hblk : Chain ((List.range 20).map (Desc.req R c)) :=
      chain_map_range 20 _ (fun k hk => Or.inl ⟨by omega, rfl, rfl, rfl⟩)
    have hh : ((List.range 20).map (Desc.req R c)).head? = some (.req R c 0) := rfl
    have hl : ((List.range 20).map (Desc.req R c)).getLast? = some (.req R c 19) := rfl
    simp only [List.flatMap_cons]
    refine ⟨chain_append _ _ hblk ih'.1 (fun x y hx hy => ?_), ?_, ?_⟩
    · rw [hl] at hx; cases hx
      rw [ih'.2.1] at hy
      cases cs with
      | nil => simp at hy
      | cons c' cs =>
        simp at hy; subst hy
        exact Or.inr ⟨rfl, rfl, by simpa using hcons 0 (by simp), rfl⟩
    · rw [List.head?_append, hh]; rfl
    · rw [List.getLast?_append, ih'.2.2, hl]
      cases cs with
      | nil => rfl
      | cons c' cs =>
        rw [List.getLast?_cons_cons]
        have hne : (c' :: cs).getLast? ≠ none := by simp
        cases hg : (c' :: cs).getLast? with
        | none => exact absurd hg hne
        | some z => rfl

/-- **The scan block of one native run.** -/
theorem scan_block (I : Input) (tau : Nat) (R : Run) (hr : ActualRun.run I tau = .ok R)
    (hp : NearSpecV3.Scheduler.Params.calculate NearSpecV3.Scheduler.Config.pv86 I.ids.length = some I.p)
    (ht : R.tau < P) (hn : R.n < P) :
    (Gen.Scan.rows R).toList = (scanDescs R).map Desc.row ∧ Chain (scanDescs R) ∧
    (∀ d ∈ scanDescs R, d.Valid) ∧ (∀ x, (scanDescs R).head? = some x → ScanStart x) ∧
    (∀ x, (scanDescs R).getLast? = some x → ScanEnd x) ∧ (scanDescs R ≠ [] → 0 < R.n) := by
  have hidx := conv_indexed I tau R hr
  have hcons : ∀ k (hk : k + 1 < R.conv.length), R.conv[k+1].cid = R.conv[k].cid + 1 := by
    intro k hk; rw [hidx k (by omega), hidx (k+1) hk]
  obtain ⟨hc, hh, hl⟩ := reqs_chain R R.conv hcons
  refine ⟨scan_rows R, ?_, ?_, ?_, ?_, ?_⟩
  · unfold scanDescs
    split
    · exact chain_nil
    · apply chain_cons _ _ hc
      intro y hy
      rw [hh] at hy
      cases hcv : R.conv with
      | nil => simp_all
      | cons c cs =>
        rw [hcv] at hy; simp at hy; subst hy
        have h0 := hidx 0 (by rw [hcv]; simp)
        simp only [hcv, List.getElem_cons_zero] at h0
        exact ⟨rfl, h0, rfl⟩
  · intro d hd
    unfold scanDescs at hd
    split at hd
    · simp at hd
    · simp only [List.mem_cons, List.mem_flatMap, List.mem_map, List.mem_range] at hd
      rcases hd with rfl | ⟨c, hc, rho, hrho, rfl⟩
      · exact ⟨I, tau, hr, ht, hn⟩
      · exact ⟨I, tau, hr, hp, hc, hrho⟩
  · intro x hx
    unfold scanDescs at hx
    split at hx
    · simp at hx
    · simp at hx; exact ⟨R, hx.symm⟩
  · intro x hx
    unfold scanDescs at hx
    split at hx
    · simp at hx
    · rename_i hne
      rw [List.getLast?_cons, hl] at hx
      cases hcv : R.conv.getLast? with
      | none =>
        exfalso
        rw [List.getLast?_eq_none_iff] at hcv
        simp [hcv] at hne
      | some c => rw [hcv] at hx; simp at hx; exact ⟨R, c, hx.symm⟩
  · intro hne
    unfold scanDescs at hne
    split at hne
    · exact absurd rfl hne
    · rename_i hcv
      cases hc : R.conv with
      | nil => simp [hc] at hcv
      | cons c cs =>
        have hf := ProcActualConvertedFacts.run_facts I tau R hr c (by rw [hc]; simp)
        have hfld := (ProcActualRunProjection.run_fields I tau R hr).2.1
        have := hf.1
        omega

end ZkFormal.NearV3.Render.Ssd
