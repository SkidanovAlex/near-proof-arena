import NearCompression.SyntheticMultiplicity

namespace NearCompression
open Lean.Grind ZkFormal.Algebra
variable {K : Type} [Field K]

private theorem quotient_cons_cons (a c d : K) (cs : List K) :
    Poly.quotL a (c::d::cs)=Poly.evalL a (d::cs)::Poly.quotL a (d::cs) := by
  induction cs generalizing c d with
  | nil => simp [Poly.quotL,Poly.addL,Poly.scaleL,Poly.evalL];grind
  | cons e cs ih =>
    rw [Poly.quotL,ih d e]
    simp only [Poly.addL,Poly.scaleL,List.map_cons,Poly.evalL]
    congr 1
    exact ih d e

private theorem quotient_drop (cs : List K) (a : K) (i : Nat) :
    (Poly.quotL a cs).drop i=Poly.quotL a (cs.drop i) := by
  induction i generalizing cs with
  | zero => rfl
  | succ i ih =>
    cases cs with
    | nil => simp [Poly.quotL]
    | cons c cs =>
      cases cs with
      | nil => simp [Poly.quotL,Poly.addL,Poly.scaleL]
      | cons d ds =>
        rw [quotient_cons_cons]
        simpa only [List.drop_succ_cons] using ih (d::ds)

private theorem quotient_head (cs : List K) (a : K) :
    (Poly.quotL a cs).getD 0 0=Poly.evalL a (cs.drop 1) := by
  cases cs with
  | nil => rfl
  | cons c cs =>
    cases cs with
    | nil => simp [Poly.quotL,Poly.addL,Poly.scaleL]
    | cons d ds => rw [quotient_cons_cons];rfl

/-- Every quotient coefficient is an evaluation of a coefficient tail. -/
theorem synthetic_quotient_tail (p : Poly K) (a : K) (i : Nat) :
    (p.quot a).coeff i=(Poly.mk (p.coeffs.drop (i+1))).eval a := by
  change (Poly.quotL a p.coeffs).getD i 0=Poly.evalL a (p.coeffs.drop (i+1))
  have head:=quotient_head (p.coeffs.drop i) a
  rw [←quotient_drop] at head
  simpa [List.getD, List.getElem?_drop, List.drop_drop, Nat.add_comm] using head
private theorem quotient_length (cs : List K) (a : K) :
    (Poly.quotL a cs).length=cs.length-1 := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    cases cs with
    | nil => simp [Poly.quotL,Poly.addL,Poly.scaleL]
    | cons d ds => rw [quotient_cons_cons];simp only [List.length_cons] at ih ⊢;omega

private theorem double_tail (p : Poly K) (a b : K) (i : Nat) :
    ((p.quot a).quot b).coeff i=((Poly.mk (p.coeffs.drop (i+1))).quot a).eval b := by
  rw [synthetic_quotient_tail]
  change Poly.evalL b ((Poly.quotL a p.coeffs).drop (i+1))=
    Poly.evalL b (Poly.quotL a (p.coeffs.drop (i+1)))
  rw [quotient_drop]

/-- Synthetic divisions commute as formal coefficient lists. -/
theorem synthetic_quotients_commute (p : Poly K) (a b : K) :
    (p.quot a).quot b=(p.quot b).quot a := by
  by_cases same : a=b
  · rw [same]
  have coefficients : ∀ i,((p.quot a).quot b).coeff i=((p.quot b).quot a).coeff i := by
    intro i
    have ab:=Poly.eval_quot (Poly.mk (p.coeffs.drop (i+1))) a b
    have ba:=Poly.eval_quot (Poly.mk (p.coeffs.drop (i+1))) b a
    rw [←synthetic_quotient_tail p b i,←synthetic_quotient_tail p a i,←double_tail p a b i] at ab
    rw [←synthetic_quotient_tail p a i,←synthetic_quotient_tail p b i,←double_tail p b a i] at ba
    grind
  have lists : ((p.quot a).quot b).coeffs=((p.quot b).quot a).coeffs := by
    apply List.ext_getElem
    · change (Poly.quotL b (Poly.quotL a p.coeffs)).length=(Poly.quotL a (Poly.quotL b p.coeffs)).length
      simp only [quotient_length]
    · intro i hi hj
      have h:=coefficients i
      simpa only [Poly.coeff,List.getD,List.getElem?_eq_getElem hi,List.getElem?_eq_getElem hj,Option.getD_some] using h
  exact congrArg Poly.mk lists

/-- Jet of a quotient at another center. At order zero the remainder at the
removed root contributes; at positive orders the recurrence is homogeneous. -/
theorem synthetic_quotient_jet_step (p : Poly K) (a b : K) (n : Nat) :
    syntheticJet p b (n+1)=syntheticJet (p.quot a) b n+
      (b-a)*syntheticJet (p.quot a) b (n+1) := by
  induction n generalizing p with
  | zero =>
    have h:=Poly.eval_quot (p.quot b) a b
    rw [synthetic_quotients_commute p b a] at h
    have base:=Poly.eval_quot p b a
    have other:=Poly.eval_quot p a b
    change (p.quot b).eval b=(p.quot a).eval b+(b-a)*((p.quot a).quot b).eval b
    by_cases same : a=b
    · subst b;grind
    · grind
  | succ n ih =>
    have h:=ih (p.quot b)
    rw [synthetic_quotients_commute p b a] at h
    exact h

/-- Removing a root preserves every prescribed jet at a different center. -/
theorem synthetic_quotient_preserves_jets (p : Poly K) (a b : K) (m : Nat)
    (different : a≠b) (root : p.eval a=0)
    (jets : ∀ i<m,syntheticJet p b i=0) :
    ∀ i<m,syntheticJet (p.quot a) b i=0 := by
  intro i hi
  induction i with
  | zero =>
    have h:=Poly.eval_quot p a b
    have zero:=jets 0 hi
    change p.eval b=0 at zero
    change (p.quot a).eval b=0
    grind
  | succ i ih =>
    have previous:=ih (by omega)
    have h:=synthetic_quotient_jet_step p a b i
    have zero:=jets (i+1) hi
    grind
def syntheticPeel (p : Poly K) (a : K) : Nat→Poly K
  | 0 => p
  | m+1 => syntheticPeel (p.quot a) a m

private theorem peel_other_jets (m : Nat) (p : Poly K) (a b : K) (n : Nat)
    (different : a≠b) (atRoot : ∀ i<m,syntheticJet p a i=0)
    (atOther : ∀ i<n,syntheticJet p b i=0) :
    ∀ i<n,syntheticJet (syntheticPeel p a m) b i=0 := by
  induction m generalizing p with
  | zero => exact atOther
  | succ m ih =>
    exact ih (p.quot a) (fun i hi=>atRoot (i+1) (by omega))
      (synthetic_quotient_preserves_jets p a b n different (atRoot 0 (by omega)) atOther)

private theorem peel_certificate (m : Nat) (p : Poly K) (a : K) (rest : List K)
    (jets : ∀ i<m,syntheticJet p a i=0)
    (tail : SyntheticRootCertificate (syntheticPeel p a m) rest) :
    SyntheticRootCertificate p (List.replicate m a++rest) := by
  induction m generalizing p with
  | zero => exact tail
  | succ m ih =>
    change p.eval a=0 ∧ SyntheticRootCertificate (p.quot a) (List.replicate m a++rest)
    exact ⟨jets 0 (by omega),ih (p.quot a) (fun i hi=>jets (i+1) (by omega)) tail⟩

/-- Independent jet constraints at distinct centers yield a sequential
certificate containing each center its prescribed number of times. -/
theorem synthetic_multipoint_certificate (centers : List K) (distinct : centers.Nodup)
    (multiplicity : K→Nat) (p : Poly K)
    (jets : ∀ a∈centers,∀ i<multiplicity a,syntheticJet p a i=0) :
    SyntheticRootCertificate p (centers.flatMap (fun a=>List.replicate (multiplicity a) a)) := by
  induction centers generalizing p with
  | nil => trivial
  | cons a rest ih =>
    have nd:=List.nodup_cons.mp distinct
    have first:=jets a (by simp)
    apply peel_certificate (multiplicity a) p a _ first
    apply ih nd.2
    intro b hb
    exact peel_other_jets (multiplicity a) p a b (multiplicity b)
      (by intro same;subst b;exact nd.1 hb) first (jets b (by simp [hb]))

/-- Total multiplicity at distinct centers is less than D for a nonzero
formal polynomial of degree <D. Zero multiplicities and empty lists allowed. -/
theorem synthetic_multipoint_bound (centers : List K) (distinct : centers.Nodup)
    (multiplicity : K→Nat) (D : Nat) (p : Poly K)
    (degree : p.DegLt D) (nonzero : ¬p.IsZero)
    (jets : ∀ a∈centers,∀ i<multiplicity a,syntheticJet p a i=0) :
    (centers.map multiplicity).sum<D := by
  have certificate:=synthetic_multipoint_certificate centers distinct multiplicity p jets
  have size : (centers.flatMap (fun a=>List.replicate (multiplicity a) a)).length=
      (centers.map multiplicity).sum := by
    induction centers with
    | nil => rfl
    | cons a rest ih => simp_all
  apply Classical.byContradiction
  intro large
  exact nonzero (synthetic_root_certificate_zero D p degree _ (by rw [size];omega) certificate)
end NearCompression
