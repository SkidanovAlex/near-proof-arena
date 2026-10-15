import NearSpecV3.TxD1

/-!
# `ZkFormal.NearV3.D1.Extract.Akm.Parse` — the borsh readers on a window of bytes

Pure lemmas: for the byte window `win f q m = [f q, …, f (q+m−1)]`, the readers of
`NearSpecV3.Wire` consume a prefix and leave the window's rest.
-/

namespace ZkFormal.NearV3.D1.AkmProof

open NearSpec NearSpecV3

def win (f : Nat → UInt8) (q m : Nat) : List UInt8 := (List.range' q m).map f

theorem win_zero (f : Nat → UInt8) (q : Nat) : win f q 0 = [] := rfl

theorem win_succ (f : Nat → UInt8) (q m : Nat) : win f q (m + 1) = f q :: win f (q + 1) m := by
  simp [win, List.range'_succ]

theorem win_append (f : Nat → UInt8) (q a b : Nat) : win f q (a + b) = win f q a ++ win f (q + a) b := by
  induction a generalizing q with
  | zero => simp [win_zero]
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega, win_succ, ih, win_succ, List.cons_append,
      show q + 1 + a = q + (a + 1) by omega]

theorem takeN_win (f : Nat → UInt8) : ∀ (w q m : Nat), w ≤ m →
    takeN w (win f q m) = some (win f q w, win f (q + w) (m - w))
  | 0, q, m, _ => by simp [takeN, win_zero]
  | w + 1, q, m, h => by
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [win_succ, takeN, takeN_win f w (q + 1) m' (by omega), win_succ]
    simp only [Option.map_some]
    rw [show q + 1 + w = q + (w + 1) by omega, show m' - w = m' + 1 - (w + 1) by omega]

theorem takeAcc_eq : ∀ (n : Nat) (acc bs : List UInt8),
    takeAcc n acc bs = (takeN n bs).map fun (h, t) => (acc.reverse ++ h, t)
  | 0, acc, bs => by
    simp only [takeAcc, takeN, Option.map_some, List.append_nil]
    congr 2
    have g : ∀ (l a : List UInt8), revAppend l a = l.reverse ++ a := by
      intro l; induction l with
      | nil => intro a; rfl
      | cons x l ih => intro a; simp [revAppend, ih]
    rw [g]; simp
  | _ + 1, _, [] => by simp [takeAcc, takeN]
  | n + 1, acc, b :: bs => by
    simp only [takeAcc, takeN, takeAcc_eq n (b :: acc) bs]
    cases takeN n bs <;> simp

theorem takeT_eq (n : Nat) (bs : List UInt8) : takeT n bs = takeN n bs := by
  unfold takeT; rw [takeAcc_eq]; cases takeN n bs <;> simp

/-- The little-endian value of a window. -/
def winVal (f : Nat → UInt8) (q w : Nat) : Nat := leNat (win f q w)

theorem readLE_win (f : Nat → UInt8) (w q m : Nat) (h : w ≤ m) :
    readLE w (win f q m) = some (winVal f q w, win f (q + w) (m - w)) := by
  simp [readLE, takeN_win f w q m h, winVal]

theorem pU_win (f : Nat → UInt8) (w q m : Nat) (h : w ≤ m) (s : String) :
    lift s (readLE w) (win f q m) = .ok (winVal f q w, win f (q + w) (m - w)) := by
  simp [lift, readLE_win f w q m h]

theorem pU8_win (f : Nat → UInt8) (q m : Nat) (h : 1 ≤ m) (s : String) :
    pU8 s (win f q m) = .ok (winVal f q 1, win f (q + 1) (m - 1)) := pU_win f 1 q m h s
theorem pU16_win (f : Nat → UInt8) (q m : Nat) (h : 2 ≤ m) (s : String) :
    pU16 s (win f q m) = .ok (winVal f q 2, win f (q + 2) (m - 2)) := pU_win f 2 q m h s
theorem pU32_win (f : Nat → UInt8) (q m : Nat) (h : 4 ≤ m) (s : String) :
    pU32 s (win f q m) = .ok (winVal f q 4, win f (q + 4) (m - 4)) := pU_win f 4 q m h s
theorem pU64_win (f : Nat → UInt8) (q m : Nat) (h : 8 ≤ m) (s : String) :
    pU64 s (win f q m) = .ok (winVal f q 8, win f (q + 8) (m - 8)) := pU_win f 8 q m h s
theorem pU128_win (f : Nat → UInt8) (q m : Nat) (h : 16 ≤ m) (s : String) :
    pU128 s (win f q m) = .ok (winVal f q 16, win f (q + 16) (m - 16)) := pU_win f 16 q m h s

theorem winVal_one (f : Nat → UInt8) (q : Nat) : winVal f q 1 = (f q).toNat := by
  simp [winVal, win, leNat]

theorem winVal_four (f : Nat → UInt8) (q : Nat) : winVal f q 4 =
    (f q).toNat + 256 * (f (q + 1)).toNat + 65536 * (f (q + 2)).toNat + 16777216 * (f (q + 3)).toNat := by
  simp [winVal, win, leNat, List.range'_succ, Nat.add_assoc]; omega

/-- `pString` on a window: length `n` (a `u32` read), then `n` bytes that are UTF-8. -/
theorem pString_win (f : Nat → UInt8) (q m n : Nat) (s : String) (h4 : 4 + n ≤ m)
    (hn : winVal f q 4 = n) (hu : utf8Ok (win f (q + 4) n) = true) :
    pString s (win f q m) = .ok (win f (q + 4) n, win f (q + 4 + n) (m - 4 - n)) := by
  simp only [pString, pBytes, lift, readBytesT]
  rw [show readU32 (win f q m) = some (winVal f q 4, win f (q + 4) (m - 4)) from readLE_win f 4 q m (by omega),
    hn]
  simp only
  rw [takeT_eq, takeN_win f n (q + 4) (m - 4) (by omega)]
  simp only [bind, Except.bind, hu, ite_true, pure, Except.pure]

end ZkFormal.NearV3.D1.AkmProof
