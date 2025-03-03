/-
This file provides a proving interface for the KEVM function definitions.
Some of the contents of this file may be ported to a utils file in the future.
 -/

import EvmYul.UInt256
import EvmEquivalence.KEVM2Lean.Func
import EvmEquivalence.StateMap

open EvmYul
open StateMap

namespace KEVMInterface

-- Some functions are uninterpreted for now, so we have to axiomatize the behavior
-- For functions that are defined, the axioms are theorems

-- Behavior for `ite`
theorem iteMap {SortSort : Type} (c : SortBool) (x1 x2 : SortSort) :
  kite c x1 x2  = ite c x1 x2 := by aesop

section

variable {m n : SortInt}

-- Behavior for `«_?Int_»`
theorem plusIntIsSome : «_+Int_» n m = some (n + m) := rfl

def «_+Int'_» (n m : SortInt) : SortInt :=
  («_+Int_» n m).get rfl

theorem plusInt_def : «_+Int'_» n m = n + m := rfl

theorem subIntIsSome : «_-Int_» n m = some (n - m) := rfl

def «_-Int'_» (n m : SortInt) : SortInt :=
  («_-Int_» n m).get rfl

theorem subInt_def : «_-Int'_» n m = n - m := rfl

theorem mulIntIsSome : «_*Int_» n m = some (n * m) := rfl

def «_*Int'_» (n m : SortInt) : SortInt :=
  («_*Int_» n m).get rfl

theorem mulInt_def : «_*Int'_» n m = n * m := rfl

-- Behavior for `chop`
--`_modInt_` is still uninterpreted
theorem chopIsSome : chop n = some (n % UInt256.size) := by sorry

noncomputable def chop' (n : SortInt) : SortInt :=
  (chop n).get (by simp [chopIsSome])

theorem chop_def (n : SortInt) : chop' n = n % UInt256.size := by
  aesop (add simp [chop', chopIsSome])

end

-- Utils to aid in proofs
def SortGas.val (g : SortGas) : SortInt := g.1

section

variable {g₁ g₂ : SortGas}

theorem subGas_def :
  «_-Gas__GAS-SYNTAX_Gas_Gas_Gas»  g₁ g₂ = SortGas.inj_SortInt («_-Int'_» (SortGas.val g₁) (SortGas.val g₂)) := rfl

theorem leGas_def :
  «_<=Gas__GAS-SYNTAX_Bool_Gas_Gas»  g₁ g₂ = «_<=Int_» (SortGas.val g₁) (SortGas.val g₂) := rfl

end

-- TODO: Add to a specific `axioms` namespace when enough functions have been interpreted

-- Behavior of `«_==K_»` and `«_=/=K_»`
axiom Keq_def (k₁ k₂ : SortK) : «_==K_» k₁ k₂ = some (k₁ == k₂)
axiom Kneq_def (k₁ k₂ : SortK) : «_=/=K_» k₁ k₂ = some (k₁ != k₂)

-- Behavior of `_orBool_` and `_andBool_`
axiom orBool_def (b₁ b₂ : SortBool) : _orBool_ b₁ b₂ = some (b₁ || b₂)
axiom andBool_def (b₁ b₂ : SortBool) : _andBool_ b₁ b₂ = some (b₁ && b₂)
axiom notBool_def (b : SortBool) : notBool_ b = some (!b)

-- Behavior of `«#sizeWordStack»`
-- Reasoning-friendly #sizeWordStack
def wsLength (ws : SortWordStack) : ℕ :=
  match ws with
  | .«.WordStack_EVM-TYPES_WordStack» => 0
  | .«_:__EVM-TYPES_WordStack_Int_WordStack» _ ws => wsLength ws + 1

theorem sizeWordStackNotEmpty {n w : SortInt} {ws : SortWordStack} :
  sizeWordStackAux (.«_:__EVM-TYPES_WordStack_Int_WordStack» w ws) n =
  sizeWordStackAux ws (n + 1) := by
  simp [sizeWordStackAux, _432555e, _75897fa, plusIntIsSome]

theorem sizeWordStack_add_one {w n : SortInt} {ws : SortWordStack} :
  sizeWordStackAux (.«_:__EVM-TYPES_WordStack_Int_WordStack» w ws) n = do
  let val0 ← sizeWordStackAux ws n
  let val1 ← «_+Int_» 1 val0
  return val1 := by
  revert n
  induction ws <;> simp_all [sizeWordStackAux, _432555e, _75897fa, plusIntIsSome]; introv; ring

theorem sizeWordStackAuxAdd {n : SortInt} {ws : SortWordStack} :
  sizeWordStackAux ws (n + 1) = do
  let a ← sizeWordStackAux ws n
  let b ← «_+Int_» 1 a
  return b := by
  rw [←sizeWordStackNotEmpty (w := 0), sizeWordStack_add_one]

theorem sizeWordStackIsSome {ws : SortWordStack} :
  «#sizeWordStack» ws = some (wsLength ws) := by
  unfold «#sizeWordStack» _c0f9e27
  induction' ws
  . aesop (add simp [sizeWordStackAux, _432555e])
  . aesop (add simp [sizeWordStack_add_one, wsLength]) (add safe (by ring))

theorem wsLength_eq_length_wordStackMap {ws : SortWordStack} :
  wsLength ws = List.length (wordStackMap ws) := by
  induction ws <;> simp_all [wsLength]

theorem sizeWordStack_def {ws : SortWordStack} :
  «#sizeWordStack» ws = some (List.length (wordStackMap ws)) :=
  wsLength_eq_length_wordStackMap ▸ sizeWordStackIsSome

end KEVMInterface
