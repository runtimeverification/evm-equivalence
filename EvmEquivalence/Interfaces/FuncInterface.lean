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
--`_modInt_` is still uninterpreted
theorem chopIsSome (n : SortInt) : chop n = some (n % UInt256.size) := by sorry

noncomputable def chop' (n : SortInt) : SortInt :=
  (chop n).get (by simp [chopIsSome])

theorem chop_def (n : SortInt) : chop' n = n % UInt256.size := by
  simp [chop', Option.get]; split; rename_i _ _ _ _ eq _; simp_all [chopIsSome]

-- Utils to aid in proofs
def SortGas.val (g : SortGas) : SortInt :=
  match g with | .inj_SortInt x => x

theorem subGas_def (g₁ g₂ : SortGas) :
  «_-Gas__GAS-SYNTAX_Gas_Gas_Gas»  g₁ g₂ = SortGas.inj_SortInt («_-Int'_» (SortGas.val g₁) (SortGas.val g₂)) := by rfl

theorem leGas_def (g₁ g₂ : SortGas) :
  «_<=Gas__GAS-SYNTAX_Bool_Gas_Gas»  g₁ g₂ = «_<=Int_» (SortGas.val g₁) (SortGas.val g₂) := by rfl

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
  | .«_:__EVM-TYPES_WordStack_Int_WordStack» _ ws => 1 + wsLength ws

theorem sizeWordStackNotEmpty (n w : SortInt) (ws : SortWordStack) :
  sizeWordStackAux (.«_:__EVM-TYPES_WordStack_Int_WordStack» w ws) n =
  sizeWordStackAux ws (n + 1) := by
  simp [sizeWordStackAux, _432555e, _75897fa, plusIntIsSome]

theorem sizeWordStack_add_one (w : SortInt) (ws : SortWordStack) :
  ∀ n, sizeWordStackAux (.«_:__EVM-TYPES_WordStack_Int_WordStack» w ws) n = do
  let val0 ← sizeWordStackAux ws n
  let val1 ← «_+Int_» 1 val0
  return val1 := by
  induction ws <;> simp_all [sizeWordStackAux, _432555e, _75897fa, plusIntIsSome, Int.add_comm]

theorem sizeWordStackAuxAdd (n : SortInt) (n_nonneg: 0 ≤ n) :
  ∀ ws, sizeWordStackAux ws (n + 1) = do
  let a ← sizeWordStackAux ws n
  let b ← «_+Int_» 1 a
  return b := by
  cases n <;> try contradiction
  rename_i n; cases n
  . intro ws
    rw [←(sizeWordStackNotEmpty (Int.ofNat 0))]
    rw [(sizeWordStack_add_one _ ws (Int.ofNat 0))]; exact 0
  . rename_i n ;intro ws
    rw [←(sizeWordStackNotEmpty (Int.ofNat (n + 1)))]
    rw [(sizeWordStack_add_one _ ws (Int.ofNat (n + 1)))]; exact 0

theorem sizeWordStackIsSome (ws : SortWordStack) :
  «#sizeWordStack» ws = some (wsLength ws) := by
  induction ws with
  | «.WordStack_EVM-TYPES_WordStack» =>
    simp [wsLength, «#sizeWordStack», _c0f9e27, sizeWordStackAux, _432555e, _75897fa]
  | «_:__EVM-TYPES_WordStack_Int_WordStack» w wss ih =>
    rw [«#sizeWordStack», _c0f9e27] at *
    simp_all only [Option.pure_def, Option.bind_eq_bind, Option.bind_some]
    rw [sizeWordStack_add_one, ih]
    aesop

theorem wsLength_def (ws : SortWordStack) :
  wsLength ws = List.length (wordStackMap ws) := by
  induction ws <;> simp_all [wsLength, wordStackMap, Nat.add_comm]

theorem sizeWordStack_def (ws : SortWordStack) :
  «#sizeWordStack» ws = some (List.length (wordStackMap ws)) := by
  rw [sizeWordStackIsSome, wsLength_def]

end KEVMInterface
