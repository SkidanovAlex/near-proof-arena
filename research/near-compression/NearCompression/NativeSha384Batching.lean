import NearCompression.SHA384TranscriptCommit

/-! Operational model of the native SHA384-v4 pending observation buffer.
The hash is arbitrary: these statements preserve routing and order, not QROM
security, collision resistance, or equivalence to the old v2 transcript. -/
namespace NearCompression

structure NativeSha384State where
  seed : List UInt8
  pending : List UInt8
  cursor : Nat
  deriving DecidableEq

def nativeSha384Domain : List UInt8 :=
  [110, 101, 97, 114, 112, 114, 111, 111, 102, 45, 110, 97, 116, 105, 118, 101, 45, 115, 104, 97, 51, 56, 52, 45, 101, 120, 116, 49, 50, 45, 118, 52]

def nativeSha384Frame (tag : UInt8) (parts : List (List UInt8)) : List UInt8 :=
  nativeSha384Domain ++ [tag] ++
    (parts.map (fun p => NearSpec.leN 8 p.length ++ p)).flatten

def nativeSha384Observe (s : NativeSha384State) (bytes : List UInt8) : NativeSha384State :=
  {seed:=s.seed,pending:=s.pending++bytes,cursor:=12}

def nativeSha384Flush (hash : List UInt8 → List UInt8) (s : NativeSha384State) : NativeSha384State :=
  if s.pending=[] then s else
    {seed:=hash (nativeSha384Frame 3 [s.seed,s.pending]),pending:=[],cursor:=12}

/-- Adjacent observations preserve the exact ordered concatenation, even for
empty chunks. This does not commute observations or merge across challenges. -/
theorem native_sha384_observe_concat (s : NativeSha384State) (a b : List UInt8) :
    nativeSha384Observe (nativeSha384Observe s a) b = nativeSha384Observe s (a++b) := by
  simp [nativeSha384Observe,List.append_assoc]

/-- The runtime flush consumes every pending byte once, hashes the explicit
field-observation domain and clears all previously available challenge words. -/
theorem native_sha384_flush_nonempty (hash : List UInt8 → List UInt8)
    (s : NativeSha384State) (nonempty : s.pending≠[]) :
    nativeSha384Flush hash s =
      {seed:=hash (nativeSha384Frame 3 [s.seed,s.pending]),pending:=[],cursor:=12} := by
  simp [nativeSha384Flush,nonempty]

theorem native_sha384_flush_idempotent (hash : List UInt8 → List UInt8) (s : NativeSha384State) :
    nativeSha384Flush hash (nativeSha384Flush hash s)=nativeSha384Flush hash s := by
  by_cases h : s.pending=[] <;> simp [nativeSha384Flush,h]

/-- A whole sequence of encoded fields reaches the flush in its original order.
The length bound needed for injective u64 framing is a separate obligation. -/
theorem native_sha384_observe_many_pending (s : NativeSha384State) (chunks : List (List UInt8)) :
    (chunks.foldl nativeSha384Observe s).pending=s.pending++chunks.flatten := by
  induction chunks generalizing s with
  | nil => simp
  | cons a rest ih =>
    simp only [List.foldl_cons]
    rw [ih]
    simp [nativeSha384Observe,List.append_assoc]

theorem native_sha384_observe_many_seed (s : NativeSha384State) (chunks : List (List UInt8)) :
    (chunks.foldl nativeSha384Observe s).seed=s.seed := by
  induction chunks generalizing s with
  | nil => rfl
  | cons a rest ih => simpa [nativeSha384Observe] using ih (nativeSha384Observe s a)

/-- Combining the actual accumulation and flush operations fixes the exact hash
input. No theorem about arbitrary or unchecked byte encoders is assumed here. -/
theorem native_sha384_batch_hash_input (hash : List UInt8 → List UInt8)
    (s : NativeSha384State) (chunks : List (List UInt8))
    (nonempty : s.pending++chunks.flatten≠[]) :
    (nativeSha384Flush hash (chunks.foldl nativeSha384Observe s)).seed=
      hash (nativeSha384Frame 3 [s.seed,s.pending++chunks.flatten]) := by
  rw [native_sha384_flush_nonempty hash _ (by
    rw [native_sha384_observe_many_pending];exact nonempty)]
  simp only [native_sha384_observe_many_pending,native_sha384_observe_many_seed]

/-- Fixed-width Merkle encoding used by the native v4 implementation. -/
def nativeSha384NodeFrame (left right : List UInt8) : List UInt8 :=
  [78,80,81,52,78,79,68,69] ++ (left++right)

theorem native_sha384_node_frame_injective (l r l' r' : List UInt8)
    (hl : l.length=48) (hl' : l'.length=48)
    (same : nativeSha384NodeFrame l r=nativeSha384NodeFrame l' r') :
    l=l' ∧ r=r' := by
  have payload : l++r=l'++r' := List.append_cancel_left same
  exact List.append_inj payload (hl.trans hl'.symm)

theorem native_sha384_node_message_length (l r : List UInt8)
    (hl : l.length=48) (hr : r.length=48) :
    (nativeSha384NodeFrame l r).length=104 := by
  simp [nativeSha384NodeFrame,hl,hr]

/-- One block of standard SHA384 padding: 104 bytes plus 0x80, seven zero
bytes and the 16-byte length suffix is exactly128bytes. -/
theorem native_sha384_node_one_block (l r : List UInt8)
    (hl : l.length=48) (hr : r.length=48) :
    (nativeSha384NodeFrame l r).length+1+7+16=128 := by
  rw [native_sha384_node_message_length l r hl hr]

/-- Node encodings cannot equal any transcript/leaf frame: their initial byte
is N=78 whereas the general profile domain begins with n=110. -/
theorem native_sha384_node_domain_disjoint (l r : List UInt8) (tag : UInt8)
    (parts : List (List UInt8)) :
    nativeSha384NodeFrame l r ≠ nativeSha384Frame tag parts := by
  intro same
  have first := congrArg List.head? same
  have different : (some (78 : UInt8)) ≠ some (110 : UInt8) := by decide
  simp only [nativeSha384NodeFrame,nativeSha384Frame,nativeSha384Domain,List.cons_append,List.head?_cons] at first
  exact different first

end NearCompression
