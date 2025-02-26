import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Lattice

theorem le_fls_of_lt {n m : Nat} (h : n < m) : (m ≤ n) = False := by
  simp [eq_iff_iff, iff_false, not_le]; assumption

theorem Int.mod_cast (n m : Int) (le0n: 0 ≤ n) (le0m : 0 ≤ m):
  n % m = ↑((Int.toNat n) % (Int.toNat m)) := by
  simp_all [sup_of_le_left]
