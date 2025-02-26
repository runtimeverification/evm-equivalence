import EvmYul.UInt256

open EvmYul

theorem UInt256.val_eq (n : ℕ) (h : n < UInt256.size): ↑(UInt256.ofNat n).1 = n := by
  rw [Fin.val, UInt256.val]; simp [UInt256.ofNat]; split
  . rw [Nat.lt_iff_le_not_le] at h; cases h; contradiction
  . simp [Id.run, Fin.ofNat]; assumption

theorem UInt256.ofNat_eq (n : ℕ) (h : n < UInt256.size):
UInt256.ofNat n = ⟨Fin.ofNat n⟩ := by
  simp [UInt256.ofNat]; split
  . rw [Nat.lt_iff_le_not_le] at h; cases h; contradiction
  . simp [Id.run]
