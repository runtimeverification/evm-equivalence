import EvmYul.EVM.Semantics


open EvmYul

namespace UInt256

section

set_option linter.deprecated false

variable {n : ℕ}

theorem val_eq (h : n < UInt256.size): ↑(UInt256.ofNat n).1 = n := by
  aesop (add simp [UInt256.ofNat, Id.run, Fin.ofNat])
        (add safe (by omega))

theorem ofNat_eq: UInt256.ofNat n = ⟨Fin.ofNat n⟩ := by
  aesop (add simp [UInt256.ofNat])

theorem ofNat_toNat (n_le_size : n < UInt256.size) :
  (UInt256.ofNat n).toNat = n := by
  aesop (add simp [UInt256.ofNat, UInt256.toNat, Id.run, dbgTrace, Fin.ofNat])

@[simp]
theorem sub_0 {n : UInt256} : n - .ofNat 0 = n := by
  match n with
  | UInt256.mk (Fin.mk val isLT) =>
  simp [UInt256.ofNat, Id.run, HSub.hSub, Sub.sub, UInt256.sub]
  simp [UInt256.size, Fin.ofNat, Fin.sub]; assumption
  -- Alternatively:
  /- simp [UInt256.ofNat]; split; try contradiction
  simp [Id.run, HSub.hSub, Sub.sub, UInt256.sub]
  simp [Fin.sub]; rw [Nat.mod_eq_iff_lt]; assumption; simp [UInt256.size] -/

@[simp]
theorem zero_add: .ofNat 0 + .ofNat n = UInt256.ofNat n := by
  simp [UInt256.ofNat, Id.run, dbgTrace, Fin.ofNat, HAdd.hAdd]
  simp [Add.add, UInt256.add, Fin.add_def]

end

end UInt256

@[simp]
theorem isCreate_false {τ : OperationType} (opcode : Operation τ) (noCreate : opcode ≠ Operation.CREATE) (noCreate2 : opcode ≠ Operation.CREATE2):
  opcode.isCreate = false := by
  cases opc: opcode <;> rw [Operation.isCreate]; next op =>
  cases op <;> aesop
