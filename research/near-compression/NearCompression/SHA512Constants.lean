import NearCompression.SHA512CombinedRun

/-! One fixed 128-row compression-instance trace. Rows 0..79 use the actual
SHA-512 constants; rows 80..127 execute zero-key rounds. The cryptographic
endpoint is row 79, not the last row. Initial state, message padding,
feed-forward, and block chaining remain separate obligations. -/
namespace NearCompression
open ZkFormal.Air ZkFormal.Algebra NearSpecV3.SHA512

def sha512ConstantDigit (i limb : Nat) : Nat := (K.getD i 0 / 65536^limb)%65536

def sha512ConstantSum (limb : Nat) : Nat → Expr
  | 0 => .const 0
  | n+1 => .add (sha512ConstantSum limb n)
      (.mul (.col (5152+n) false) (.const (sha512ConstantDigit n limb)))

def sha512ConstantFirst (i : Nat) : Expr :=
  .mul .isFirst (.add (.col (5152+i) false) (.neg (.const (if i=0 then 1 else 0))))
def sha512ConstantStep (i : Nat) : Expr :=
  .mul .isTransition (.add (.col (5152+i) true)
    (.neg (if i=0 then .const 0 else .col (5152+(i-1)) false)))
def sha512ConstantLast : Expr :=
  .mul .isLast (.add (.col 5279 false) (.neg (.const 1)))
def sha512ConstantBinding (limb : Nat) : Expr :=
  .add (.col (4116+limb) false) (.neg (sha512ConstantSum limb 128))

def sha512ConstantsConstraints : List Expr :=
  sha512CombinedConstraints ++ (List.range 128).map sha512ConstantFirst ++
    (List.range 128).map sha512ConstantStep ++ [sha512ConstantLast] ++
    (List.range 4).map sha512ConstantBinding

def sha512ConstantsTable : Table := ⟨5280,sha512ConstantsConstraints,[],7⟩

theorem sha512_constants_first (air : Air) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t<air.tables.length) (table : air.tables[t]=sha512ConstantsTable)
    (holds : Holds air pub tr) (i : Nat) (hi : i<128) :
    tr.cell t 0 (5152+i) = if i=0 then 1 else 0 := by
  have hc := holds.constr t ht 0 (Nat.two_pow_pos _) (sha512ConstantFirst i)
  rw [table] at hc
  have hv := hc (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ (List.mem_map.mpr ⟨i,List.mem_range.mpr hi,rfl⟩)))))
  change (1 : Fp) * (tr.cell t 0 (5152+i) + -Fp.ofNat (if i=0 then 1 else 0))=0 at hv
  by_cases hi0 : i=0
  · rw [if_pos hi0] at hv ⊢
    change (1 : Fp) * (tr.cell t 0 (5152+i) + -1)=0 at hv
    grind
  · rw [if_neg hi0] at hv ⊢
    change (1 : Fp) * (tr.cell t 0 (5152+i) + -0)=0 at hv
    grind

theorem sha512_constants_step (air : Air) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t<air.tables.length) (table : air.tables[t]=sha512ConstantsTable)
    (holds : Holds air pub tr) (r i : Nat) (hi : i<128) (next : r+1<tr.height t) :
    tr.cell t (r+1) (5152+i) = if i=0 then 0 else tr.cell t r (5152+(i-1)) := by
  have hc := holds.constr t ht r (by omega) (sha512ConstantStep i)
  rw [table] at hc
  have hv := hc (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ (List.mem_map.mpr ⟨i,List.mem_range.mpr hi,rfl⟩))))
  by_cases hi0 : i=0
  · simp only [sha512ConstantStep,hi0,ite_true,Expr.eval,Expr.evalWith,rowEnv,
      Nat.mod_eq_of_lt next,Nat.ne_of_lt next,Bool.false_eq_true,ite_false] at hv
    change (1 : Fp) * (tr.cell t (r+1) (5152+0) + -0)=0 at hv
    subst i
    simp only [ite_true]
    grind
  · simp only [sha512ConstantStep,hi0,ite_false,Expr.eval,Expr.evalWith,rowEnv,
      Nat.mod_eq_of_lt next,Nat.ne_of_lt next,ite_true,Bool.false_eq_true] at hv
    change (1 : Fp) * (tr.cell t (r+1) (5152+i) + -tr.cell t r (5152+(i-1)))=0 at hv
    rw [if_neg hi0]
    grind

/-- One-hot phase values are forced by initial and transition polynomials;
there is no external phase or Boolean assumption. -/
theorem sha512_constants_phase (air : Air) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t<air.tables.length) (table : air.tables[t]=sha512ConstantsTable)
    (holds : Holds air pub tr) (r : Nat) (hr : r<tr.height t) (i : Nat) (hi : i<128) :
    tr.cell t r (5152+i) = if i=r then 1 else 0 := by
  induction r generalizing i with
  | zero => exact sha512_constants_first air tr pub t ht table holds i hi
  | succ r ih =>
    rw [sha512_constants_step air tr pub t ht table holds r i hi hr]
    by_cases hi0 : i=0
    · subst i
      simp
    · rw [if_neg hi0,ih (by omega) (i-1) (by omega)]
      have he : i-1=r ↔ i=r+1 := by omega
      simp only [he]

theorem sha512_constants_height (air : Air) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t<air.tables.length) (table : air.tables[t]=sha512ConstantsTable)
    (holds : Holds air pub tr) : tr.height t=128 := by
  have log := holds.logBound t ht
  rw [table] at log
  have upper : tr.height t ≤ 128 := Nat.pow_le_pow_right (by decide) log.2
  have pos : 0<tr.height t := Nat.two_pow_pos _
  have last : tr.height t-1+1=tr.height t := by omega
  have hc := holds.constr t ht (tr.height t-1) (by omega) sha512ConstantLast
  rw [table] at hc
  have hv := hc (List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_self ..)))
  simp only [sha512ConstantLast,Expr.eval,Expr.evalWith,rowEnv,last,ite_true,Bool.false_eq_true,ite_false] at hv
  change (1 : Fp) * (tr.cell t (tr.height t-1) 5279 + -1)=0 at hv
  have phase := sha512_constants_phase air tr pub t ht table holds (tr.height t-1) (by omega) 127 (by decide)
  change tr.cell t (tr.height t-1) 5279 = _ at phase
  rw [phase] at hv
  by_cases eq : 127=tr.height t-1
  · omega
  · rw [if_neg eq] at hv
    have bad : (0 : Fp)=1 := by grind
    have hn := congrArg Fp.toNat bad
    change 0=1 at hn
    omega

set_option maxRecDepth 65536 in
set_option maxHeartbeats 8000000 in
theorem sha512_constants_table_wf : sha512ConstantsTable.wf ⟨[sha512ConstantsTable],0,0⟩ 3=true := by decide

set_option maxRecDepth 65536 in
theorem sha512_constants_table_size :
    sha512ConstantsTable.width=5280 ∧ sha512ConstantsTable.constraints.length=7109 := by decide

theorem sha512_constants_sum_eval (tr : Trace Fp) (pub : List Fp) (t r limb n : Nat)
    (hn : n≤128)
    (phase : ∀ i, i<128 → tr.cell t r (5152+i) = if i=r then 1 else 0) :
    (sha512ConstantSum limb n).eval tr t r pub =
      if r<n then Fp.ofNat (sha512ConstantDigit r limb) else 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (sha512ConstantSum limb n).eval tr t r pub +
      tr.cell t r (5152+n) * Fp.ofNat (sha512ConstantDigit n limb) = _
    rw [ih (by omega),phase n (by omega)]
    by_cases eq : n=r
    · subst n
      simp only [Nat.lt_irrefl,ite_false,ite_true,Nat.lt_succ_self]
      grind
    · by_cases lt : r<n
      · have lt' : r<n+1 := by omega
        rw [if_pos lt,if_pos lt',if_neg eq]
        grind
      · have lt' : ¬r<n+1 := by omega
        rw [if_neg lt,if_neg lt',if_neg eq]
        grind

theorem sha512_constants_key_limb (air : Air) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t<air.tables.length) (table : air.tables[t]=sha512ConstantsTable)
    (holds : Holds air pub tr) (r limb : Nat) (hr : r<tr.height t) (hl : limb<4) :
    (tr.cell t r (4116+limb)).toNat = sha512ConstantDigit r limb := by
  have hc := holds.constr t ht r hr (sha512ConstantBinding limb)
  rw [table] at hc
  have hv := hc (List.mem_append_right _ (List.mem_map.mpr ⟨limb,List.mem_range.mpr hl,rfl⟩))
  change tr.cell t r (4116+limb) + -(sha512ConstantSum limb 128).eval tr t r pub = 0 at hv
  rw [sha512_constants_sum_eval tr pub t r limb 128 (by decide)
    (sha512_constants_phase air tr pub t ht table holds r hr)] at hv
  have rbound : r<128 := by rw [sha512_constants_height air tr pub t ht table holds] at hr; exact hr
  rw [if_pos rbound] at hv
  have eq : tr.cell t r (4116+limb) = Fp.ofNat (sha512ConstantDigit r limb) := by grind
  rw [eq,Fp.toNat_ofNat]
  have bound : sha512ConstantDigit r limb < 65536 := Nat.mod_lt _ (by decide)
  apply Nat.mod_eq_of_lt
  unfold P
  omega

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
theorem sha512_constants_digits (r : Nat) (hr : r<128) :
    sha512ConstantDigit r 0 + 65536*sha512ConstantDigit r 1 +
      4294967296*sha512ConstantDigit r 2 + 281474976710656*sha512ConstantDigit r 3 = K.getD r 0 := by
  have checked : ∀ r : Fin 128,
    sha512ConstantDigit r.val 0 + 65536*sha512ConstantDigit r.val 1 +
      4294967296*sha512ConstantDigit r.val 2 + 281474976710656*sha512ConstantDigit r.val 3 = K.getD r.val 0 := by decide
  exact checked ⟨r,hr⟩

theorem sha512_constants_key (air : Air) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t<air.tables.length) (table : air.tables[t]=sha512ConstantsTable)
    (holds : Holds air pub tr) (r : Nat) (hr : r<tr.height t) :
    sha512CombinedK (tr.cell t r) = K.getD r 0 := by
  have l0 := sha512_constants_key_limb air tr pub t ht table holds r 0 hr (by decide)
  have l1 := sha512_constants_key_limb air tr pub t ht table holds r 1 hr (by decide)
  have l2 := sha512_constants_key_limb air tr pub t ht table holds r 2 hr (by decide)
  have l3 := sha512_constants_key_limb air tr pub t ht table holds r 3 hr (by decide)
  change (tr.cell t r (4116+0)).toNat + 65536*(tr.cell t r (4116+1)).toNat +
    4294967296*(tr.cell t r (4116+2)).toNat + 281474976710656*(tr.cell t r (4116+3)).toNat = _
  rw [l0,l1,l2,l3]
  apply sha512_constants_digits
  rw [←sha512_constants_height air tr pub t ht table holds]
  exact hr

theorem sha512_constants_combined_holds (air : Air) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t<air.tables.length) (table : air.tables[t]=sha512ConstantsTable)
    (holds : Holds air pub tr) :
    Holds ⟨[sha512CombinedTable],0,0⟩ pub (sha512CombinedProjection tr t 0) := by
  constructor
  · intro j hj
    have hz : j=0 := by simpa using hj
    subst j
    have log := holds.logBound t ht
    rw [table] at log
    change 1≤tr.log t ∧ tr.log t≤22
    change 1≤tr.log t ∧ tr.log t≤7 at log
    omega
  · intro j hj r hr e he
    have hz : j=0 := by simpa using hj
    subst j
    rw [←sha512_combined_relocate_eval,sha512_relocate_zero]
    have hc := holds.constr t ht r hr e
    rw [table] at hc
    exact hc (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ he))))
  · intro j hj r hr i hi
    have hz : j=0 := by simpa using hj
    subst j
    simp [sha512CombinedTable] at hi
  · intro b m
    simp [busCount,busCount.go,tableBusCount,sha512CombinedTable]

/-- All eighty decoded round constants are the actual specification list. -/
theorem sha512_constants_keys (air : Air) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t<air.tables.length) (table : air.tables[t]=sha512ConstantsTable)
    (holds : Holds air pub tr) : sha512CombinedKeys tr t 0 80 = K := by
  have eq : sha512CombinedKeys tr t 0 80 = (List.range' 0 80).map (fun r => K.getD r 0) := by
    apply List.map_congr_left
    intro r hr
    apply sha512_constants_key air tr pub t ht table holds
    have hb := List.mem_range'.mp hr
    rw [sha512_constants_height air tr pub t ht table holds]
    omega
  rw [eq]
  decide

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
/-- The fixed SHA-512 eighty-round endpoint is row 79; later rows are not padding. -/
theorem sha512_constants_endpoint (air : Air) (tr : Trace Fp) (pub : List Fp)
    (t : Nat) (ht : t<air.tables.length) (table : air.tables[t]=sha512ConstantsTable)
    (holds : Holds air pub tr) :
    rounds (sha512CombinedVars (tr.cell t 0)) K (sha512CombinedWindow (tr.cell t 0)) =
      sha512CombinedOutput (tr.cell t 79) := by
  have combined := sha512_constants_combined_holds air tr pub t ht table holds
  have height := sha512_constants_height air tr pub t ht table holds
  have result := sha512_combined_segment _ _ pub 0 (by decide) rfl combined 79 0 (by
    change 0+79<tr.height t
    omega)
  have keys := sha512_constants_keys air tr pub t ht table holds
  have result' : rounds (sha512CombinedVars (tr.cell t 0)) (sha512CombinedKeys tr t 0 80)
      (sha512CombinedWindow (tr.cell t 0)) = sha512CombinedOutput (tr.cell t 79) := by
    simpa only [sha512CombinedProjection,Nat.zero_add,sha512CombinedKeys] using result
  rw [keys] at result'
  exact result' 

end NearCompression
