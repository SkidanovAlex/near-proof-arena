/-
Hand-written deltas for the generated D1 copies (`scripts/rcpt_d1_copy.py`, lane
v3-d1-phase2, V4).  Not a Lean module.

* `-- @override <D0a constant>`: the following text (up to the next marker) replaces the copy
  of that declaration verbatim, in its namespace and section.
* `-- @patch <D0a constant>` followed by `<<<` old `===` new `>>>`: a textual replacement
  inside the generated copy of the module of that declaration (after renaming).

The deltas are the six changes of `rcptV3D1` (plan §7, step 3): first-row tokens `TOK0`
(Tok), body offset `O0` (Body), the count with `M0` (Count), the 14-bit deposit age with
`T0` (Age14; the `MEM` time and `MPOS` position are traffic-level, `Delta/Traffic`), plus
the provider bound `tprev ≤ 2^25` (versions are now `≤ r + 1 + T0`) and `con` with its
`replC' e = e` side condition.
-/

-- @override ZkFormal.NearV3.Assembly.ReceiptCandidateProof.con
/-- `con` for `rcptV3D1`: a D0a constraint that `rcptV3D1` keeps (`replC' e = e`, by `rfl`
on a closed constraint) holds on every row. -/
theorem con_d1 (hL : ZkFormal.NearV3.D1.RcptD1.LocalD1 tr tt pub) {r : Nat}
    (hq : r < tr.height tt) {e : Expr} (he : e ∈ receiptArithmeticCandidate.constraints)
    (hn : ZkFormal.NearV3.D1.RcptD1.replC' e = e := by rcpt_unchanged) :
    e.eval tr tt r pub = 0 :=
  hL.constr r hq e (ZkFormal.NearV3.D1.RcptD1.memD1 he hn)

-- @override ZkFormal.NearV3.Assembly.ReceiptCandidateProof.first0
/-- First row: list `0`, receipt `0`, body position `O0` (Delta/Body). -/
theorem first0_d1 (h0 : 0 < tr.height tt) :
    tr.cell tt 0 j = 0 ∧ tr.cell tt 0 RcptV3.r = 0 ∧
      tr.cell tt 0 o2 = ((ZkFormal.NearV3.D1.RcptD1.o0V pub : Nat) : Fp) := by
  have h1 := con_d1 hL h0 (e := .mul .isFirst (c j)) (mem_st (by simp [cStates]))
  have h2 := con_d1 hL h0 (e := .mul .isFirst (c RcptV3.r)) (mem_st (by simp [cStates]))
  simp only [eval_mul, eval_c, eval_isFirst, if_true] at h1 h2
  exact ⟨by grind, by grind, ZkFormal.NearV3.D1.RcptD1.o2_first hL h0⟩

-- @override ZkFormal.NearV3.Assembly.ReceiptCandidateProof.token_zero
/-- The first physical row starts with the tokens `TOK0` (Delta/Tok). -/
theorem token_zero_d1 (h0 : 0<tr.height tt) (j : Nat) (hj : j<16) :
    tr.cell tt 0 (tok j)=((pubNat pub (ZkFormal.NearV3.D1.E_TOK0+j) : Nat) : Fp) :=
  ZkFormal.NearV3.D1.RcptD1.tok_first hL h0 hj

-- @patch ZkFormal.NearV3.Assembly.ReceiptCandidateProof.token_bytes
<<<
    simp [cv,token_zero_d1 hL hq j hj,Fp.toNat_zero]
===
    rw [cv,token_zero_d1 hL hq j hj,toNat_natCast,Nat.mod_eq_of_lt (ZkFormal.Near.RcptProof.pubNat_lt pub _)]
    exact ZkFormal.NearV3.D1.RcptD1.tok0_byte hL.ext.1 hj
>>>

-- @override ZkFormal.NearV3.Assembly.ReceiptCandidateProof.tokenAt_zero
theorem tokenAt_zero_d1 (h0 : 0<tr.height tt) : tokenAt tr tt 0=ZkFormal.NearV3.D1.RcptD1.tok0V pub := by
  rw [ZkFormal.NearV3.D1.RcptD1.tok0V,
    show pubBytes pub ZkFormal.NearV3.D1.E_TOK0 16=(List.range 16).map
      (fun j => pubNat pub (ZkFormal.NearV3.D1.E_TOK0+j)) from rfl,
    ZkFormal.Near.RcptProof.leN'_rows _ (fun j hj => ZkFormal.NearV3.D1.RcptD1.tok0_byte hL.ext.1 hj)]
  apply ZkFormal.Near.RcptProof.sumL_congr
  intro j hj
  rw [cv,token_zero_d1 hL h0 j hj,toNat_natCast,Nat.mod_eq_of_lt (ZkFormal.Near.RcptProof.pubNat_lt pub _)]

-- @patch ZkFormal.NearV3.Assembly.ReceiptCandidateProof.ListChain.zero_token_run
<<<
    TokenRun tr tt (bs.flatMap ListBlock.receipts) 0 (tokenAt tr tt (e-1)) := by
===
    TokenRun tr tt (bs.flatMap ListBlock.receipts) (ZkFormal.NearV3.D1.RcptD1.tok0V pub) (tokenAt tr tt (e-1)) := by
>>>

-- @patch ZkFormal.NearV3.Assembly.ReceiptCandidateProof.ListChain.view_tokens
<<<
    (hprovider : ∀ B∈bs, ∀ y∈B.receipts, (rcptOf tr tt y).tprev≤2^22) :
    let ls := bs.map (ListBlock.view tr tt)
    ∃ toks : List Nat,toks.length=(flatR ls).length+1 ∧ toks.head?=some 0 ∧
      (∀ r,(hr:r<(flatR ls).length) →
        (flatR ls)[r].Wf r (pubBytes pub PH_GP 16) (toks.getD r 0) (toks.getD (r+1) 0)) ∧
===
    (hprovider : ∀ B∈bs, ∀ y∈B.receipts, (rcptOf tr tt y).tprev≤2^25) :
    let ls := bs.map (ListBlock.view tr tt)
    ∃ toks : List Nat,toks.length=(flatR ls).length+1 ∧ toks.head?=some (ZkFormal.NearV3.D1.RcptD1.tok0V pub) ∧
      (∀ r,(hr:r<(flatR ls).length) →
        (flatR ls)[r].Wf (r+ZkFormal.NearV3.D1.RcptD1.t0V pub) (pubBytes pub PH_GP 16) (toks.getD r 0) (toks.getD (r+1) 0)) ∧
>>>

-- @patch ZkFormal.NearV3.Assembly.ReceiptCandidateProof.ListChain.view_tokens
<<<
  refine ⟨tokenList tr tt xs 0,?_,rfl,?_,?_⟩
===
  refine ⟨tokenList tr tt xs (ZkFormal.NearV3.D1.RcptD1.tok0V pub),?_,rfl,?_,?_⟩
>>>

-- @patch ZkFormal.NearV3.Assembly.ReceiptCandidateProof.ListChain.indexed_wf
<<<
    (hprovider : (rcptOf tr tt bs[j].receipts[k]).tprev≤2^22) :
    let y := bs[j].receipts[k]
    (rcptOf tr tt y).Wf (((bs.take j).map fun B => B.receipts.length).sum+k) (pubBytes pub PH_GP 16)
===
    (hprovider : (rcptOf tr tt bs[j].receipts[k]).tprev≤2^25) :
    let y := bs[j].receipts[k]
    (rcptOf tr tt y).Wf (((bs.take j).map fun B => B.receipts.length).sum+k+ZkFormal.NearV3.D1.RcptD1.t0V pub)
      (pubBytes pub PH_GP 16)
>>>

-- @patch ZkFormal.NearV3.Assembly.ReceiptCandidateProof.wf_numbered
<<<
    (hrN : tr.cell tt y.s RcptV3.r=(rN:Fp)) (hrP : rN<P) (hprovider : (rcptOf tr tt y).tprev≤2^22) :
    (rcptOf tr tt y).Wf rN (pubBytes pub PH_GP 16)
===
    (hrN : tr.cell tt y.s RcptV3.r=(rN:Fp)) (hrP : rN<P) (hprovider : (rcptOf tr tt y).tprev≤2^25) :
    (rcptOf tr tt y).Wf (rN+ZkFormal.NearV3.D1.RcptD1.t0V pub) (pubBytes pub PH_GP 16)
>>>

-- @patch ZkFormal.NearV3.Assembly.ReceiptCandidateProof.wf_of
<<<
    (hprovider : (rcptOf tr tt y).tprev≤2^22) :
    (rcptOf tr tt y).Wf rN (pubBytes pub PH_GP 16)
===
    (hprovider : (rcptOf tr tt y).tprev≤2^25) :
    (rcptOf tr tt y).Wf (rN+ZkFormal.NearV3.D1.RcptD1.t0V pub) (pubBytes pub PH_GP 16)
>>>

-- @patch ZkFormal.NearV3.Assembly.ReceiptCandidateProof.wf_of_route
<<<
    (hprovider : (rcptOf tr tt y).tprev≤2^22) :
    (rcptOf tr tt y).Wf rN (pubBytes pub PH_GP 16)
===
    (hprovider : (rcptOf tr tt y).tprev≤2^25) :
    (rcptOf tr tt y).Wf (rN+ZkFormal.NearV3.D1.RcptD1.t0V pub) (pubBytes pub PH_GP 16)
>>>

-- @patch ZkFormal.NearV3.Assembly.ReceiptCandidateProof.previous_of_provider_bound
<<<
    (ht : (rcptOf tr tt ⟨s,h,Lp,Lv,Ls,kt⟩).tprev≤2^22) :
    (rcptOf tr tt ⟨s,h,Lp,Lv,Ls,kt⟩).tprev≤rN := by
===
    (ht : (rcptOf tr tt ⟨s,h,Lp,Lv,Ls,kt⟩).tprev≤2^25) :
    (rcptOf tr tt ⟨s,h,Lp,Lv,Ls,kt⟩).tprev≤rN+ZkFormal.NearV3.D1.RcptD1.t0V pub := by
>>>

-- @patch ZkFormal.NearV3.Assembly.ReceiptCandidateProof.previous_of_provider_bound
<<<
  have hpv : cv tr tt (s+(107+Vt Lp Lv Ls kt)) tprev≤2^22 := by
===
  have hpv : cv tr tt (s+(107+Vt Lp Lv Ls kt)) tprev≤2^25 := by
>>>

-- @override ZkFormal.NearV3.Assembly.ReceiptCandidateProof.repaired_local_base
theorem repaired_local_base_d1 (h : ZkFormal.NearV3.D1.RcptD1.LocalD1 tr tt pub) :
    ZkFormal.NearV3.D1.RcptD1.LocalD1 tr tt pub := h

-- @override ZkFormal.NearV3.Assembly.ReceiptCandidateProof.deposit_previous_row
/-- Previous-version order with the 14-bit age `r + T0 − tprev` (Delta/Age14): no modular
wrap below `P − 2^25`, whatever `r`. -/
theorem deposit_previous_row_d1 {pos : Nat} (hp : pos<tr.height tt)
    (hs : tr.cell tt pos sDEP=1) (hf : tr.cell tt pos fs=1)
    (ht : cv tr tt pos tprev≤2^25) : cv tr tt pos tprev≤cv tr tt pos r+ZkFormal.NearV3.D1.RcptD1.t0V pub := by
  have he := ZkFormal.NearV3.D1.RcptD1.age_row hL hp
  obtain ⟨hb,hlt⟩ := bitsX_eval_d1 hL hp 52 14 (by decide)
  rw [hs,hf,hb,cell_eq_cast tr tt pos r,cell_eq_cast tr tt pos tprev] at he
  have eq : ((cv tr tt pos r+ZkFormal.NearV3.D1.RcptD1.t0V pub:Nat):Fp)=
      ((cv tr tt pos tprev+bitsVal (fun j=>cv tr tt pos (xb j)) 52 14:Nat):Fp) := by
    rw [natCast_add,natCast_add];grind
  have := ZkFormal.NearV3.D1.RcptD1.le_of_cast_eq (by unfold P; omega) eq
  omega

-- @override ZkFormal.NearV3.Assembly.ReceiptCandidateProof.deposit_previous_provider_bound
theorem deposit_previous_provider_bound_d1 {pos : Nat} (hp : pos<tr.height tt)
    (hs : tr.cell tt pos sDEP=1) (hf : tr.cell tt pos fs=1)
    (ht : cv tr tt pos tprev≤2^25) : cv tr tt pos tprev≤cv tr tt pos r+ZkFormal.NearV3.D1.RcptD1.t0V pub :=
  deposit_previous_row_d1 hL hp hs hf ht

-- @override ZkFormal.NearV3.Assembly.ReceiptCandidateProof.repaired_first_receiver_q
theorem repaired_first_receiver_q_d1 {pos : Nat}
    (h : ZkFormal.NearV3.D1.RcptD1.LocalD1 tr tt pub)
    (hp : pos<tr.height tt) (hs : tr.cell tt pos sV=1) (hf : tr.cell tt pos fs=1) :
    cv tr tt pos q<128 := by
  have he := h.constr pos hp RoutingQCandidate.qBound ZkFormal.NearV3.D1.RcptD1.qBound_mem
  obtain ⟨hb,hl⟩ := bitsX_eval_d1 h hp 12 7 (by decide)
  simp only [RoutingQCandidate.qBound,eval_mul3,eval_c,eval_sub,hs,hf] at he
  rw [hb,cell_eq_cast tr tt pos q] at he
  have eq : (cv tr tt pos q:Fp)=((bitsVal (fun j=>cv tr tt pos (xb j)) 12 7:Nat):Fp) := by grind
  have hn := ofNat_inj (tr.cell tt pos q).toNat_lt (by unfold P;omega) eq
  simp only [cv] at *
  omega

-- @override ZkFormal.NearV3.Assembly.ReceiptCandidateProof.ListChain.total_bounds
theorem ListChain.total_bounds_d1 {s e : Nat} {bs : List ListBlock} (h : ListChain tr tt s bs e) :
    (bs.map fun B => B.receipts.length).sum<P ∧
    8+(bs.map fun B => B.refundBytes tr tt).sum<P := by
  have hn := receipt_counts_le_rows bs
  have hr := h.rows
  have he := (ListChain.last_row_d1 hL h).2.1
  have hH := height_le_d1 hL
  have hb : (bs.map fun B => B.refundBytes tr tt).sum≤(bs.map ListBlock.rows).sum := by
    have hw : ∀ B∈bs,B.refundBytes tr tt≤B.rows := fun B hB => ListBlockWf.refund_le_rows_d1 hL (h.blocks B hB)
    clear hn hr he h hH
    induction bs with
    | nil => simp
    | cons B bs ih =>
      have hB := hw B (by simp)
      have ht := ih (by intro C hC; exact hw C (by simp [hC]))
      simp only [List.map_cons,List.sum_cons]
      omega
  unfold P
  omega

/-- Both totals are at most the table height `2^22` (D1: room for the offsets `M0`, `O0`). -/
theorem ListChain.total_bounds22_d1 {s e : Nat} {bs : List ListBlock} (h : ListChain tr tt s bs e) :
    (bs.map fun B => B.receipts.length).sum≤2^22 ∧
    (bs.map fun B => B.refundBytes tr tt).sum≤2^22 := by
  have hn := receipt_counts_le_rows bs
  have hr := h.rows
  have he := (ListChain.last_row_d1 hL h).2.1
  have hH := height_le_d1 hL
  have hb : (bs.map fun B => B.refundBytes tr tt).sum≤(bs.map ListBlock.rows).sum := by
    have hw : ∀ B∈bs,B.refundBytes tr tt≤B.rows := fun B hB => ListBlockWf.refund_le_rows_d1 hL (h.blocks B hB)
    clear hn hr he h hH
    induction bs with
    | nil => simp
    | cons B bs ih =>
      have hB := hw B (by simp)
      have ht := ih (by intro C hC; exact hw C (by simp [hC]))
      simp only [List.map_cons,List.sum_cons]
      omega
  omega

-- @override ZkFormal.NearV3.Assembly.ReceiptCandidateProof.ListChain.final_totals
/-- The end constraints with the D1 offsets: `PH_N = count + M0` (Delta/Count) and
`PH_BLEN = O0 + refund bytes` (Delta/Body), in the field. -/
theorem ListChain.final_totals_d1 {e : Nat} {bs : List ListBlock} (h : ListChain tr tt 0 bs e) :
    nPubE.eval tr tt (e-1) pub=(((bs.map fun B => B.receipts.length).sum+ZkFormal.NearV3.D1.RcptD1.m0V pub:Nat):Fp) ∧
    blenE.eval tr tt (e-1) pub=((ZkFormal.NearV3.D1.RcptD1.o0V pub+(bs.map fun B => B.refundBytes tr tt).sum:Nat):Fp) := by
  obtain ⟨he,hH,hl⟩ := ListChain.last_row_d1 hL h
  have hc := ZkFormal.NearV3.D1.RcptD1.count_last hL (q:=e-1) (by omega)
  have hb := con_d1 hL (r:=e-1) (by omega)
    (e:=.mul (c lastR) (sub (c o2End) blenE)) (mem_en (by simp [cEnd]))
  simp only [eval_mul,eval_sub,eval_c,hl] at hb
  rw [hl] at hc
  have hz := first0_d1 hL (by omega : 0<tr.height tt)
  have hn := ListChain.terminal_count_d1 hL h
  have ho := ListChain.terminal_body_d1 hL h
  rw [hz.2.1] at hn
  rw [hz.2.2] at ho
  rw [natCast_add,natCast_add]
  grind

-- @override ZkFormal.NearV3.Assembly.ReceiptCandidateProof.ListChain.natural_count
/-- Exact count with `M0` (Delta/Count). -/
theorem ListChain.natural_count_d1 {e : Nat} {bs : List ListBlock} (h : ListChain tr tt 0 bs e)
    (hp : leN' (pubBytes pub PH_N 4)<P)
    (hc : ∀ i,i<4 → pubNat pub (PH_N+i)<256) :
    (bs.map fun B => B.receipts.length).sum+ZkFormal.NearV3.D1.RcptD1.m0V pub=leN' (pubBytes pub PH_N 4) := by
  have hf := (ListChain.final_totals_d1 hL h).1
  have he := public_u32_eval tr tt (e-1) pub PH_N hc
  change nPubE.eval tr tt (e-1) pub=_ at he
  rw [he] at hf
  have hb := (ListChain.total_bounds22_d1 hL h).1
  have hm := hL.ext.2.1
  exact (ofNat_inj hp (by unfold P; omega) hf).symm

-- @override ZkFormal.NearV3.Assembly.ReceiptCandidateProof.ListChain.natural_body
/-- Exact body length from `O0` (Delta/Body). -/
theorem ListChain.natural_body_d1 {e : Nat} {bs : List ListBlock} (h : ListChain tr tt 0 bs e)
    (hp : leN' (pubBytes pub PH_BLEN 4)<P)
    (hb : ∀ i,i<4 → pubNat pub (PH_BLEN+i)<256) :
    ZkFormal.NearV3.D1.RcptD1.o0V pub+(bs.map fun B => B.refundBytes tr tt).sum=leN' (pubBytes pub PH_BLEN 4) := by
  have hf := (ListChain.final_totals_d1 hL h).2
  have he := public_u32_eval tr tt (e-1) pub PH_BLEN hb
  change blenE.eval tr tt (e-1) pub=_ at he
  rw [he] at hf
  have hs := (ListChain.total_bounds22_d1 hL h).2
  have ho := hL.ext.2.2.2
  exact (ofNat_inj hp (by unfold P; omega) hf).symm

-- @override ZkFormal.NearV3.Assembly.ReceiptCandidateProof.ListChain.view_wf
/-- **The D1 table-level facts** (`RcptV3WfD1`). -/
theorem ListChain.view_wf_d1 {e : Nat} {bs : List ListBlock} (h : ListChain tr tt 0 bs e)
    (hp : ReceiptPublicRanges pub)
    (hprovider : ∀ B∈bs, ∀ y∈B.receipts, (rcptOf tr tt y).tprev≤2^25) :
    ZkFormal.NearV3.D1.RcptD1.RcptV3WfD1 pub (bs.map (ListBlock.view tr tt)) := by
  refine ⟨(ListChain.view_header_facts_d1 hL h).1,ListChain.view_tokens_d1 hL h hprovider,?_,
    (ListChain.view_header_facts_d1 hL h).2.1,?_,ListChain.view_canon_d1 hL h⟩
  · intro hb
    rw [flat_views_length]
    exact ListChain.natural_count_d1 hL h hp.count hb
  · intro hb
    rw [ZkFormal.NearV3.D1.RcptD1.flat_views_bodyG]
    exact ListChain.natural_body_d1 hL h hp.body hb

-- @patch ZkFormal.NearV3.Assembly.ReceiptCandidateProof.ListChain.bytes_full
<<<
      ((chainByteMsgs tr tt pub bs 0 0 8).map Msg.toFp) := by
  have hH := height_ge_d1 hL
  have h0 := first0_d1 hL (by omega)
  have ht := ListChain.bytes_traffic_d1 hL h 0 0 8 (by simpa using ListChain.length_lt_P_d1 hL h) h0.1 h0.2.1 h0.2.2
===
      ((chainByteMsgs tr tt pub bs 0 0 (ZkFormal.NearV3.D1.RcptD1.o0V pub)).map Msg.toFp) := by
  have hH := height_ge_d1 hL
  have h0 := first0_d1 hL (by omega)
  have ht := ListChain.bytes_traffic_d1 hL h 0 0 (ZkFormal.NearV3.D1.RcptD1.o0V pub)
    (by simpa using ListChain.length_lt_P_d1 hL h) h0.1 h0.2.1 h0.2.2
>>>

-- @override ZkFormal.NearV3.Assembly.ReceiptCandidateProof.ListChain.bytes_view
/-- Complete BYTES sends: the D1 sends (refund bodies from `O0`). -/
theorem ListChain.bytes_view_d1 {e : Nat} {bs : List ListBlock} (h : ListChain tr tt 0 bs e) (t0 m0 : Nat) :
    ((List.range (tr.height tt)).flatMap
      (fun q => rowTraffic RcptV3.interactions tr tt q pub B_BYTES true)).Perm
      ((ZkFormal.NearV3.D1.RcptD1.rcptSends3G (ZkFormal.NearV3.D1.RcptD1.o0V pub) t0 m0 pub
        (bs.map (ListBlock.view tr tt)) B_BYTES).map Msg.toFp) := by
  have hh := ListChain.bytes_full_d1 hL h
  rw [ZkFormal.NearV3.D1.RcptD1.chainByteMsgs_eq_viewG _ t0 m0] at hh
  exact hh

-- @override ZkFormal.NearV3.Assembly.ReceiptCandidateProof.ListChain.bytes_view_traffic
theorem ListChain.bytes_view_traffic_d1 {e : Nat} {bs : List ListBlock} (h : ListChain tr tt 0 bs e)
    (t0 m0 : Nat) (m : List Fp) :
    tableBusCount RcptV3.interactions tr tt pub B_BYTES true m=
      ((ZkFormal.NearV3.D1.RcptD1.rcptSends3G (ZkFormal.NearV3.D1.RcptD1.o0V pub) t0 m0 pub
        (bs.map (ListBlock.view tr tt)) B_BYTES).map Msg.toFp).count m ∧
    tableBusCount RcptV3.interactions tr tt pub B_BYTES false m=
      ((rcptRecvs3 (bs.map (ListBlock.view tr tt)) B_BYTES).map Msg.toFp).count m := by
  constructor
  · rw [tableBusCount_eq]
    exact (ListChain.bytes_view_d1 hL h t0 m0).count_eq m
  · rw [tableBusCount_eq,bytes_receive_empty,view_bytes_receive_empty]
    rfl

-- @patch ZkFormal.NearV3.Assembly.ReceiptCandidateProof.ListChain.view_traffic
<<<
theorem ListChain.view_traffic_d1 {e : Nat} {bs : List ListBlock} (h : ListChain tr tt 0 bs e) :
    TableTraffic RcptV3.interactions tr tt pub (rcptTraffic3 pub (bs.map (ListBlock.view tr tt))) := by
  unfold TableTraffic rcptTraffic3
  intro bus m
  by_cases h0 : bus=B_BYTES
  · subst bus
    exact ListChain.bytes_view_traffic_d1 hL h m
===
theorem ListChain.view_traffic_d1 {e : Nat} {bs : List ListBlock} (h : ListChain tr tt 0 bs e) :
    TableTraffic RcptV3.interactions tr tt pub
      (ZkFormal.NearV3.D1.RcptD1.rcptTraffic3G (ZkFormal.NearV3.D1.RcptD1.o0V pub) 0 0 pub
        (bs.map (ListBlock.view tr tt))) := by
  unfold TableTraffic ZkFormal.NearV3.D1.RcptD1.rcptTraffic3G
  intro bus m
  by_cases h0 : bus=B_BYTES
  · subst bus
    exact ListChain.bytes_view_traffic_d1 hL h 0 0 m
  simp only [ZkFormal.NearV3.D1.RcptD1.sends3G_eq _ _ _ h0]
>>>

