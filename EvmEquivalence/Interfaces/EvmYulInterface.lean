import EvmYul.UInt256

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

theorem ofNat_toNat (h : n < UInt256.size): (UInt256.ofNat n).toNat = n := by
  have le_fls : (UInt256.size ≤ n) = False := by aesop
  simp [UInt256.ofNat, Id.run, Fin.ofNat, UInt256.toNat]; split <;> try simp_all
  simp_all [UInt256.size]

end

end UInt256
