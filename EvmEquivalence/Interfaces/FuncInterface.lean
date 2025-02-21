/-
This file provides a proving interface for the KEVM function definitions.
Some of the contents of this file may be ported to a utils file in the future.
 -/

import EvmYul.UInt256
import EvmEquivalence.KEVM2Lean.Func

open EvmYul

namespace KEVMInterface

-- Some functions are uninterpreted for now, so we have to axiomatize the behavior
-- For functions that are defined, the axioms are theorems

-- Behavior for `ite`
theorem iteMap {SortSort : Type} (c : SortBool) (x1 x2 : SortSort) :
  kite c x1 x2  = ite c x1 x2 := by cases c <;> rfl

-- Behavior for `«_?Int_»`
theorem plusIntIsSome (n m : SortInt): «_+Int_» n m = some (n + m) := by rfl

def «_+Int'_» (n m : SortInt) : SortInt :=
  («_+Int_» n m).get (by simp [plusIntIsSome])

theorem plusInt_def (n m : SortInt) : «_+Int'_» n m = n + m := by rfl

theorem subIntIsSome (n m : SortInt): «_-Int_» n m = some (n - m) := by rfl

def «_-Int'_» (n m : SortInt) : SortInt :=
  («_-Int_» n m).get (by simp [subIntIsSome])

theorem subInt_def (n m : SortInt) : «_-Int'_» n m = n - m := by rfl

theorem mulIntIsSome (n m : SortInt): «_*Int_» n m = some (n * m) := by rfl

def «_*Int'_» (n m : SortInt) : SortInt :=
  («_*Int_» n m).get (by simp [mulIntIsSome])

theorem mulInt_def (n m : SortInt) : «_*Int'_» n m = n * m := by rfl

-- Behavior for `chop`
axiom chopIsSome : ∀ n : SortInt, chop n = some (n % UInt256.size)

noncomputable def chop' (n : SortInt) : SortInt :=
  (chop n).get (by simp [chopIsSome])

-- Utils to aid in proofs
def SortGas.val (g : SortGas) : SortInt :=
  match g with | .inj_SortInt x => x

theorem subGas_def (g₁ g₂ : SortGas) :
  «_-Gas__GAS-SYNTAX_Gas_Gas_Gas»  g₁ g₂ = SortGas.inj_SortInt («_-Int'_» (SortGas.val g₁) (SortGas.val g₂)) := by rfl

-- Behavior of `«_==K_»` and `«_=/=K_»`
axiom Keq_def (k₁ k₂ : SortK) : «_==K_» k₁ k₂ = some (k₁ == k₂)
axiom Kneq_def (k₁ k₂ : SortK) : «_=/=K_» k₁ k₂ = some (k₁ != k₂)

-- Behavior of `_orBool_` and `_andBool_`
axiom orBool_def (b₁ b₂ : SortBool) : _orBool_ b₁ b₂ = some (b₁ || b₂)
axiom andBool_def (b₁ b₂ : SortBool) : _andBool_ b₁ b₂ = some (b₁ && b₂)
axiom notBool_def (b : SortBool) : notBool_ b = some (!b)

end KEVMInterface
