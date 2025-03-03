import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Lattice
import Aesop

theorem le_fls_of_lt {n m : Nat} (h : n < m) : (m ≤ n) = False := by aesop

theorem Int.mod_cast {n m : Int} (le0n: 0 ≤ n) (le0m : 0 ≤ m):
  n % m = ↑((Int.toNat n) % (Int.toNat m)) := by aesop
