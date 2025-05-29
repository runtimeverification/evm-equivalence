import Batteries.Data.ByteArray
import Mathlib.Order.Lattice
import Aesop

namespace ByteArray

theorem append_array_data (a b : Array UInt8) :
  ({data := a ++ b} : ByteArray)  = {data := a} ++ { data := b} := by
  have := data_append {data := a} {data := b}; simp_all only [ByteArray.data, ←this]

theorem push_size (b : ByteArray) (u : UInt8) :
  (b.push u).size = b.size + 1 := by aesop

theorem append_empty (b : ByteArray) : b  ++ .empty = b := by aesop

theorem cons_eq_append (h : UInt8) (t : List UInt8) :
  ({ data := { toList := h :: t } } : ByteArray) =
  { data := { toList := [h] } } ++ { data := { toList := t } } := by aesop

theorem toList_loop_empty :
  toList.loop { data := { toList := [] } } 0 [] = [] := by
  rw [toList.loop]; simp [size]

theorem toList_empty :
  ({ data := { toList := [] } } : ByteArray).toList = [] := by
  simp [toList, toList_loop_empty]

end ByteArray

namespace Array

theorem extract_of_size_le {α} {as : Array α} {i j : Nat} (h : as.size ≤ j) :
    as.extract i j = as.extract i as.size := by aesop

end Array

namespace List

theorem loop_size_add (l : List UInt8) (b : ByteArray) :
  (List.toByteArray.loop l b).size =
  (List.toByteArray.loop l .empty).size + b.size := by
  induction l generalizing b <;> simp [List.toByteArray.loop]
  rename_i _ _ ih; rw [ih, ByteArray.push_size, ←Nat.add_assoc]
  (conv => rhs; rw [ih]; simp); omega

theorem toByteArray_cons_size (h : UInt8) (t : List UInt8) :
  (h :: t).toByteArray.size = t.toByteArray.size + 1 := by
  simp [List.toByteArray, List.toByteArray.loop]
  induction t; aesop
  simp [List.toByteArray.loop]; rw [loop_size_add]
  (conv=> rhs; rw [loop_size_add]); simp

theorem size_length_eq (l : List UInt8) :
  l.toByteArray.size = l.length := by
  induction l <;> aesop (add simp [toByteArray_cons_size])

end List

namespace Axioms

namespace ByteArray

/--
 This should be proved at some point
-/
axiom toList_eq (l : List UInt8) : ByteArray.toList ⟨⟨l⟩⟩ = l

end ByteArray

end Axioms
