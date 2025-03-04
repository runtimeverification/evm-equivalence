import Mathlib.Order.Lattice
import Aesop

theorem Int.mod_cast {n m : Int} (le0n: 0 ≤ n) (le0m : 0 ≤ m):
  n % m = ↑((Int.toNat n) % (Int.toNat m)) := by aesop
