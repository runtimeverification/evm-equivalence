/-
This file provides a proving interface for the KEVM definitions.
Some of the contents of this file may be ported to a utils file in the future.
 -/

import EvmYul.UInt256
import EvmEquivalence.KEVM2Lean.Func

open EvmYul

namespace KEVMInterface

-- Someunctions are uninterpreted for now, so we have to axiomatize the behavior
-- For functions that are defined, the axioms are theorems

-- Behavior for `ite`
theorem iteMap {SortSort : Type} (c : SortBool) (x1 x2 : SortSort) :
  kite c x1 x2  = ite c x1 x2 := by cases c <;> rfl

-- Behavior for `«_?Int_»`
theorem plusIntIsSome (n m : SortInt): «_+Int_» n m = some (n + m) := by rfl

def «_+Int'_» (n m : SortInt) : SortInt :=
  («_+Int_» n m).get (by simp [plusIntIsSome])

theorem subIntIsSome (n m : SortInt): «_-Int_» n m = some (n - m) := by rfl

def «_-Int'_» (n m : SortInt) : SortInt :=
  («_-Int_» n m).get (by simp [subIntIsSome])

theorem mulIntIsSome (n m : SortInt): «_*Int_» n m = some (n * m) := by rfl

def «_*Int'_» (n m : SortInt) : SortInt :=
  («_*Int_» n m).get (by simp [mulIntIsSome])

-- Behavior for `chop`
axiom chopIsSome : ∀ n : SortInt, chop n = some (n % UInt256.size)

noncomputable def chop' (n : SortInt) : SortInt :=
  (chop n).get (by simp [chopIsSome])

-- Utils to aid in proofs
def SortGas.val (g : SortGas) : SortInt :=
  match g with | .inj_SortInt x => x

theorem subGas_def (g₁ g₂ : SortGas) :
  «_-Gas__GAS-SYNTAX_Gas_Gas_Gas»  g₁ g₂ = SortGas.inj_SortInt («_-Int'_» (SortGas.val g₁) (SortGas.val g₂)) := by rfl

end KEVMInterface
