import NearCompression.HostPersistence

/-! Backend persistence for argument loops and charged data access. -/
namespace NearCompression
open NearSpecV3.Wasm

theorem host_real_for_in_list {B : Type} (xs : List Nat) (b : B)
    (f : Nat → B → HM (ForInStep B)) (hf : ∀ i a, HostKeepsReal (f i a)) :
    HostKeepsReal (forIn xs b f) := by
  induction xs generalizing b with
  | nil => exact host_real_pure b
  | cons x xs ih =>
    simp only [List.forIn_cons]
    apply host_real_bind
    · exact hf x b
    intro out
    cases out with
    | done b => exact host_real_pure b
    | yield b => exact ih b

theorem host_real_for_in {B : Type} (range : Std.Legacy.Range) (b : B)
    (f : Nat → B → HM (ForInStep B)) (hf : ∀ i a, HostKeepsReal (f i a)) :
    HostKeepsReal (forIn range b f) := by
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  exact host_real_for_in_list _ b f hf

theorem host_real_pop_args (n : Nat) : HostKeepsReal (popArgs n) := by
  unfold popArgs
  apply host_real_bind
  · apply host_real_for_in
    intro i out
    apply host_real_get_bind
    intro s hs
    change (popN s).2.real.isSome = true
    rw [pop_n_real]
    exact hs
  intro out
  dsimp only
  split
  · exact host_real_pure _
  · exact host_real_throw _

theorem host_real_push_ret (v : Nat) (is64 : Bool) : HostKeepsReal (pushRet v is64) := by
  unfold pushRet
  apply host_real_modify
  intro s hs
  split <;> exact hs

theorem host_real_charged_read (base byte : Cost) (ptr len : Nat) :
    HostKeepsReal (chargedRead base byte ptr len) := by
  unfold chargedRead
  apply host_real_bind
  · unfold payBaseH; exact host_real_with_gas _
  intro _
  apply host_real_bind
  · unfold payPerH; exact host_real_with_gas _
  intro _
  apply host_real_get_bind
  intro s hs
  split
  · exact hs
  · exact hs

theorem host_real_read_mem (ptr len : Nat) : HostKeepsReal (readMemH ptr len) := by
  change HostKeepsReal (chargedRead C.readMemoryBase C.readMemoryByte ptr len)
  with_reducible exact host_real_charged_read C.readMemoryBase C.readMemoryByte ptr len

theorem host_real_register_body (s : St) (real : s.real.isSome = true) (id : Nat) (d : ByteArray) :
    (hostFinalState ((registerWriteBody s id d).run s)).real.isSome = true := by
  unfold registerWriteBody
  dsimp only
  repeat' (split <;> (try simp_all only []))
  all_goals exact real

theorem host_real_charged_register (base byte : Cost) (id : Nat) (d : ByteArray)
    (chargeBytes : Bool) : HostKeepsReal (chargedRegisterWrite base byte id d chargeBytes) := by
  unfold chargedRegisterWrite
  apply host_real_bind
  · unfold payBaseH; exact host_real_with_gas _
  intro _
  split
  · apply host_real_bind
    · unfold payPerH; exact host_real_with_gas _
    intro _
    apply host_real_get_bind
    intro s hs
    exact host_real_register_body s hs id d
  · apply host_real_get_bind
    intro s hs
    exact host_real_register_body s hs id d

theorem host_real_reg_set (id : Nat) (d : ByteArray) (chargeBytes : Bool) :
    HostKeepsReal (regSetH id d chargeBytes) := by
  change HostKeepsReal (chargedRegisterWrite C.writeRegisterBase C.writeRegisterByte id d chargeBytes)
  with_reducible exact host_real_charged_register C.writeRegisterBase C.writeRegisterByte id d chargeBytes

theorem host_real_charged_return {A : Type} (base byte : Cost) (len : Nat) (value : A) :
    HostKeepsReal (chargedReturn base byte len value) := by
  unfold chargedReturn
  apply host_real_bind
  · unfold payBaseH; exact host_real_with_gas _
  intro _
  apply host_real_bind
  · unfold payPerH; exact host_real_with_gas _
  intro _
  exact host_real_pure value

theorem host_real_reg_get (id : Nat) : HostKeepsReal (regGetH id) := by
  unfold regGetH
  apply host_real_get_bind
  intro s hs
  split
  · rename_i idx bytes found
    change (hostFinalState ((chargedReturn C.readRegisterBase C.readRegisterByte bytes.size bytes).run s)).real.isSome = true
    have hp : HostKeepsReal (chargedReturn C.readRegisterBase C.readRegisterByte bytes.size bytes) := by
      with_reducible exact host_real_charged_return C.readRegisterBase C.readRegisterByte bytes.size bytes
    exact hp s hs
  · exact hs

theorem host_real_mem_or_reg (ptr len : Nat) : HostKeepsReal (memOrRegH ptr len) := by
  unfold memOrRegH
  split
  · exact host_real_reg_get ptr
  · exact host_real_read_mem ptr len

theorem for_in_preserves_real : ∀ (xs : List Nat)
    (f : (x : Nat) → x ∈ xs → St → St) (s : St),
    (∀ x hx u, (f x hx u).real = u.real) →
    (forIn' (m := Id) xs s fun x hx st => ForInStep.yield (f x hx st)).real = s.real
  | [], _, _, _ => rfl
  | x :: xs, f, s, hf => by
    simp only [List.forIn'_cons]
    exact (for_in_preserves_real xs (fun y hy => f y (List.mem_cons_of_mem _ hy))
      (f x (by simp) s) (fun y hy u => hf y _ u)).trans (hf x _ s)

theorem write_bytes_real (s : St) (ptr : Nat) (d : ByteArray) :
    (writeBytes s ptr d).real = s.real := by
  unfold writeBytes
  simp only [Id.run, Std.Legacy.Range.forIn'_eq_forIn'_range']
  apply for_in_preserves_real
  intro x hx u
  rfl

theorem host_real_charged_memory_write (base byte : Cost) (ptr : Nat) (d : ByteArray) :
    HostKeepsReal (chargedMemoryWrite base byte ptr d) := by
  unfold chargedMemoryWrite
  apply host_real_bind
  · unfold payBaseH; exact host_real_with_gas _
  intro _
  apply host_real_bind
  · unfold payPerH; exact host_real_with_gas _
  intro _
  apply host_real_get_bind
  intro s hs
  split
  · exact hs
  · change (writeBytes s ptr d).real.isSome = true
    rw [write_bytes_real]
    exact hs

theorem host_real_write_mem (ptr : Nat) (d : ByteArray) : HostKeepsReal (writeMemH ptr d) := by
  change HostKeepsReal (chargedMemoryWrite C.writeMemoryBase C.writeMemoryByte ptr d)
  with_reducible exact host_real_charged_memory_write C.writeMemoryBase C.writeMemoryByte ptr d

end NearCompression
