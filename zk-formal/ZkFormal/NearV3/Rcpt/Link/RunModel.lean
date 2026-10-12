import ZkFormal.NearV3.Rcpt.Link.RunSplit
import ZkFormal.Near.Spec.SoundAccount
import ZkFormal.Near.Spec.Good

/-!
# ZkFormal.NearV3.Rcpt.Link.RunModel — the receipt ledger on a slot-valued trie family

Record-free core of the receipt half of `m.Valid.run` (v1's `Spec/Good` + `Spec/SoundRun`
generalized to D0's system receipts and an abstract trie).  A `RunModel` is

* the receipts `rs` in applied order and the value slot `slot r` each one's account walk ends at;
* the decoded pre-state account `acc0 k` of each slot, and the raw pre-state bytes `base k`
  of the slots no receipt writes;
* a **trie family** `T : (Nat → Bytes) → PTrie` — the main trie after the scheduler step with
  slot `k` holding `v k`.

`TrieOk M` is the interface to the trie link (lane v3-link): for every receipt `r` and every
slot assignment `v`, the account key `get`s / `find`s `v (slot r)`, `set` replaces exactly that
slot, and a system gas refund (`signer = receiver`) finds an absent or `FullAccess` access key.

`RcptOk3 ctx M r` are the per-receipt arithmetic facts (v1's `RcptOk`; the burn / surplus /
token bounds only for non-system receipts).  Then:

* `accAt ctx r` — the accumulator before receipt `r` (trie `T (valsAt r)`, the first `r`
  outcomes / refunds, `r·G` gas, `tokAt r` tokens);
* **`step`** — `ledgerStep ctx (accAt r) (rc r) = some (accAt (r+1))`;
* **`ledgerAll_eq`** — `ledgerAll ctx (accAt 0) rs = some (accAt |rs|)`.
-/

namespace ZkFormal.NearV3.RcptLink

open NearSpec NearSpec.TransferV1 NearSpecV3 ZkFormal.Near

def dfltReceipt : Receipt := ⟨[], [], [], [], ⟨0, []⟩, 0, 0⟩

structure RunModel where
  rs : List Receipt
  slot : Nat → Nat
  acc0 : Nat → Account
  /-- pre-state value bytes of the slots no receipt writes (access keys, …) -/
  base : Nat → Bytes
  T : (Nat → Bytes) → PTrie

namespace RunModel
variable (M : RunModel) (ctx : ApplyCtx)

def rc (r : Nat) : Receipt := M.rs.getD r dfltReceipt

def isSys (r : Nat) : Bool := (M.rc r).predecessorId == AccountId.system

/-- Amount of slot `k` before receipt `r`. -/
def amtAt (k : Nat) : Nat → Nat
  | 0 => (M.acc0 k).amount
  | r + 1 => amtAt k r + (if M.slot r = k then (M.rc r).deposit else 0)

/-- Slot `k` is some receipt's account slot. -/
def written (k : Nat) : Bool := (List.range M.rs.length).any (fun r => M.slot r == k)

/-- Value bytes of slot `k` before receipt `r`. -/
def valsAt (r k : Nat) : Bytes :=
  if M.written k then Account.encode { M.acc0 k with amount := M.amtAt k r } else M.base k

def bctx : Ctx := ⟨ctx.height, ctx.gasPrice⟩

/-- Tokens burnt by receipt `r` (system receipts burn nothing). -/
def burnt (r : Nat) : Nat := if M.isSys r then 0 else burntOf ctx.gasPrice (M.rc r)

def tokAt : Nat → Nat
  | 0 => 0
  | r + 1 => tokAt r + M.burnt ctx r

def refundOf (r : Nat) : List Receipt :=
  if M.isSys r then [] else
    if surplusOf ctx.gasPrice (M.rc r) = 0 then [] else
      [gasRefundReceipt (M.rc r) ctx.height (surplusOf ctx.gasPrice (M.rc r))]

def outcomeOf (r : Nat) : Outcome :=
  { id := (M.rc r).receiptId, receiptIds := (M.refundOf ctx r).map Receipt.receiptId,
    gasBurnt := Params.G, tokensBurnt := M.burnt ctx r, executorId := (M.rc r).receiverId }

/-- The accumulator before receipt `r`. -/
def accAt (r : Nat) : Acc :=
  ⟨M.T (M.valsAt r), (List.range r).map (M.outcomeOf ctx),
   (List.range r).flatMap (M.refundOf ctx), r * Params.G, M.tokAt ctx r⟩

def upd (v : Nat → Bytes) (k : Nat) (b : Bytes) : Nat → Bytes := fun j => if j = k then b else v j

/-- `v` has the lengths of the initial values. -/
def LenPres (v : Nat → Bytes) : Prop := ∀ k, (v k).length = (M.valsAt 0 k).length

/-- The trie link's interface. -/
structure TrieOk : Prop where
  get : ∀ r, r < M.rs.length → ∀ v, M.LenPres v → (M.T v).get (accountKeyPath (M.rc r).receiverId) = some (v (M.slot r))
  find : ∀ r, r < M.rs.length → ∀ v, M.LenPres v →
    (M.T v).find (accountKeyPath (M.rc r).receiverId) = some (some (v (M.slot r)))
  /-- only for value families with the initial lengths and a same-length new value (a trie
  update may restructure the trie depending on value lengths) -/
  set : ∀ r, r < M.rs.length → ∀ v, M.LenPres v → ∀ b, b.length = (v (M.slot r)).length →
    (M.T v).set (accountKeyPath (M.rc r).receiverId) b = some (M.T (upd v (M.slot r) b))
  ak : ∀ r, r < M.rs.length → M.isSys r = true → (M.rc r).signerId = (M.rc r).receiverId →
    ∃ o, (M.T (M.valsAt r)).find (keyAccessKey (M.rc r).receiverId (M.rc r).signerPk) = some o ∧
      (o = none ∨ ∃ ak, o = some ak ∧ ak.length = 9 ∧ ak.getD 8 0 = 1)

/-- Per-receipt arithmetic (receipt `r`, slot `slot r`). -/
structure RcptOk3 (r : Nat) : Prop where
  dec : ∃ raw, Account.decode raw = some (M.acc0 (M.slot r))
  amt_lt : M.amtAt (M.slot r) r + (M.rc r).deposit < Params.u128Max
  tot_lt : M.amtAt (M.slot r) r + (M.rc r).deposit + (M.acc0 (M.slot r)).locked < Params.two128
  stake : Params.storageAmountPerByte * (M.acc0 (M.slot r)).storageUsage ≤
            M.amtAt (M.slot r) r + (M.rc r).deposit + (M.acc0 (M.slot r)).locked ∨
          (M.acc0 (M.slot r)).storageUsage ≤ Params.zeroBalanceStorageLimit
  burnt_lt : M.isSys r = false → burntOf ctx.gasPrice (M.rc r) < Params.two128
  surplus_lt : M.isSys r = false → surplusOf ctx.gasPrice (M.rc r) < Params.two128
  tok_lt : M.isSys r = false → M.tokAt ctx r + burntOf ctx.gasPrice (M.rc r) < Params.two128

theorem written_slot {r : Nat} (hr : r < M.rs.length) : M.written (M.slot r) = true := by
  simp only [written, List.any_eq_true, List.mem_range, beq_iff_eq]
  exact ⟨r, hr, rfl⟩

theorem valsAt_succ {r : Nat} (hr : r < M.rs.length) :
    M.valsAt (r + 1) = upd (M.valsAt r) (M.slot r)
      (Account.encode { M.acc0 (M.slot r) with amount := M.amtAt (M.slot r) r + (M.rc r).deposit }) := by
  funext j
  by_cases h : j = M.slot r
  · subst h; simp [valsAt, amtAt, upd, M.written_slot hr]
  · have h' : M.slot r ≠ j := fun x => h x.symm
    simp [valsAt, amtAt, upd, h, h']

theorem valsAt_lenPres (r : Nat) : M.LenPres (M.valsAt r) := by
  intro k
  simp only [valsAt]
  split <;> simp [Account.encode, u128, u64, leN_length]

theorem dec_valsAt {r : Nat} (hr : r < M.rs.length) (hok : M.RcptOk3 ctx r) :
    Account.decode (M.valsAt r (M.slot r)) =
      some { M.acc0 (M.slot r) with amount := M.amtAt (M.slot r) r } := by
  simp only [valsAt, M.written_slot hr, ↓reduceIte]
  obtain ⟨raw, hA⟩ := hok.dec
  obtain ⟨_, hl, hch, hsu, _⟩ := Sound.decode_wf hA
  exact Sound.decode_encode _ (by have := hok.amt_lt; simp only; omega) hl hch hsu

theorem accAt_succ (r : Nat) : M.accAt ctx (r + 1) =
    ⟨M.T (M.valsAt (r + 1)), (List.range r).map (M.outcomeOf ctx) ++ [M.outcomeOf ctx r],
     (List.range r).flatMap (M.refundOf ctx) ++ M.refundOf ctx r, r * Params.G + Params.G,
     M.tokAt ctx r + M.burnt ctx r⟩ := by
  simp only [accAt, List.range_succ, List.map_append, List.map_cons, List.map_nil,
    List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, Nat.succ_mul, tokAt]

/-- **One receipt.** -/
theorem step (hT : M.TrieOk) {r : Nat} (hr : r < M.rs.length) (hok : M.RcptOk3 ctx r) :
    ledgerStep ctx (M.accAt ctx r) (M.rc r) = some (M.accAt ctx (r + 1)) := by
  have hdec := M.dec_valsAt ctx hr hok
  have h1 := hok.amt_lt
  have h2 := hok.tot_lt
  have h3 := hok.stake
  have hs : (decide (M.amtAt (M.slot r) r + (M.rc r).deposit + (M.acc0 (M.slot r)).locked ≥
      Params.storageAmountPerByte * (M.acc0 (M.slot r)).storageUsage) ||
      decide ((M.acc0 (M.slot r)).storageUsage ≤ Params.zeroBalanceStorageLimit)) = true := by
    rcases h3 with h3 | h3 <;> simp [h3]
  have hset := hT.set r hr (M.valsAt r) (M.valsAt_lenPres r)
    (Account.encode { M.acc0 (M.slot r) with amount := M.amtAt (M.slot r) r + (M.rc r).deposit })
    (by simp [valsAt, M.written_slot hr, Account.encode, u128, u64, leN_length])
  rw [← valsAt_succ M hr] at hset
  rw [accAt_succ]
  unfold ledgerStep
  by_cases hsys : M.isSys r = true
  · have hsys' : ((M.rc r).predecessorId == AccountId.system) = true := hsys
    have hb : M.burnt ctx r = 0 := by simp [burnt, hsys]
    have hrf : M.refundOf ctx r = [] := by simp [refundOf, hsys]
    simp only [hsys', ↓reduceIte, hb, hrf, Nat.add_zero, List.append_nil]
    have hout : M.outcomeOf ctx r = (⟨(M.rc r).receiptId, [], Params.G, 0, (M.rc r).receiverId⟩ : Outcome) := by
      simp [outcomeOf, hrf, hb]
    rw [hout]
    dsimp only at hset hdec
    have hfind := hT.find r hr (M.valsAt r) (M.valsAt_lenPres r)
    unfold applySystemReceipt
    by_cases he : (M.rc r).signerId = (M.rc r).receiverId
    · obtain ⟨o, ho, hoo⟩ := hT.ak r hr hsys he
      rcases hoo with rfl | ⟨ak, rfl, hl9, h81⟩
      · simp [accAt, hfind, hdec, Nat.not_le.mpr h1, Nat.not_le.mpr h2, hs, he, ho, hset, bind,
          Except.bind, pure, Except.pure]
      · have h8 : ak[8]'(by omega) = 1 := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)] at h81
          simpa using h81
        simp [accAt, hfind, hdec, Nat.not_le.mpr h1, Nat.not_le.mpr h2, hs, he, ho, hset, bind,
          Except.bind, pure, Except.pure, hl9, h8]
    · simp [accAt, hfind, hdec, Nat.not_le.mpr h1, Nat.not_le.mpr h2, hs, he, hset, bind,
        Except.bind, pure, Except.pure]
  · have hns : M.isSys r = false := by simpa using hsys
    have hsys' : ((M.rc r).predecessorId == AccountId.system) = false := hns
    have h4 := hok.burnt_lt hns
    have h5 := hok.surplus_lt hns
    have h6 := hok.tok_lt hns
    have hb : M.burnt ctx r = burntOf ctx.gasPrice (M.rc r) := by simp [burnt, hns]
    simp only [hsys', Bool.false_eq_true, ↓reduceIte, hb]
    dsimp only at hset hdec
    have hget := hT.get r hr (M.valsAt r) (M.valsAt_lenPres r)
    simp only [burntOf, surplusOf, burnPrice] at h4 h5 h6
    simp only [applyReceipt, accAt, hget, hdec]
    simp only [Nat.not_le.mpr h1, Nat.not_le.mpr h2, ↓reduceIte]
    simp only [hs, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Nat.not_le.mpr h6]
    rw [hset]
    split
    · rename_i hc
      exact absurd hc (by
        simp only [Bool.or_eq_true, not_or]; exact ⟨by simpa using h4, by simpa using h5⟩)
    simp only [Option.some.injEq]
    simp [outcomeOf, refundOf, hns, burntOf, surplusOf, burnPrice, hb]
    by_cases hz : Params.G * ((M.rc r).gasPrice - min (M.rc r).gasPrice ctx.gasPrice) = 0 <;>
      simp [hz]

end RunModel

namespace RunModel
variable (M : RunModel) (ctx : ApplyCtx)

theorem rc_getElem {r : Nat} (hr : r < M.rs.length) : M.rc r = M.rs[r] := by
  simp [rc, List.getD_eq_getElem?_getD, hr]

/-- **The ledger run** from `accAt r` over the remaining receipts. -/
theorem ledgerAll_from (hT : M.TrieOk) (hok : ∀ r, r < M.rs.length → M.RcptOk3 ctx r) :
    ∀ m r, r + m = M.rs.length →
      ledgerAll ctx (M.accAt ctx r) (M.rs.drop r) = some (M.accAt ctx M.rs.length)
  | 0, r, h => by
    simp only [Nat.add_zero] at h; subst h; simp [ledgerAll]
  | m + 1, r, h => by
    have hr : r < M.rs.length := by omega
    rw [List.drop_eq_getElem_cons hr, ← M.rc_getElem hr]
    simp only [ledgerAll, M.step ctx hT hr (hok r hr)]
    exact ledgerAll_from hT hok m (r + 1) (by omega)

/-- **The ledger run** of all receipts. -/
theorem ledgerAll_eq (hT : M.TrieOk) (hok : ∀ r, r < M.rs.length → M.RcptOk3 ctx r) :
    ledgerAll ctx (M.accAt ctx 0) M.rs = some (M.accAt ctx M.rs.length) := by
  simpa using M.ledgerAll_from ctx hT hok M.rs.length 0 (by omega)

end RunModel

end ZkFormal.NearV3.RcptLink
