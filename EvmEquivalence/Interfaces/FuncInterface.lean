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
-- `Ite` not present in the moment
/- theorem iteMap {SortSort : Type} (c : SortBool) (x1 x2 : SortSort) :
  kite c x1 x2  = ite c x1 x2 := by aesop -/

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

/-
`«_-Gas__GAS-SYNTAX_Gas_Gas_Gas»` and `«_<=Gas__GAS-SYNTAX_Bool_Gas_Gas»` not present at the moment
 -/
/- section

variable {g₁ g₂ : SortGas}

theorem subGas_def :
  «_-Gas__GAS-SYNTAX_Gas_Gas_Gas»  g₁ g₂ = SortGas.inj_SortInt («_-Int'_» (SortGas.val g₁) (SortGas.val g₂)) := rfl

theorem leGas_def :
  «_<=Gas__GAS-SYNTAX_Bool_Gas_Gas»  g₁ g₂ = «_<=Int_» (SortGas.val g₁) (SortGas.val g₂) := rfl

end -/

-- TODO: Add to a specific `axioms` namespace when enough functions have been interpreted

-- Behavior of `«_==K_»` and `«_=/=K_»`
axiom Keq_def (k₁ k₂ : SortK) : «_==K_» k₁ k₂ = some (k₁ == k₂)
axiom Kneq_def (k₁ k₂ : SortK) : «_=/=K_» k₁ k₂ = some (k₁ != k₂)

-- Behavior of `==Int` and `=/=Int`
axiom IntEq_def (n m : SortInt) : «_==Int_» n m = some (n == m)
axiom IntNEq_def (n m : SortInt) : «_=/=Int_» n m = some (n != m)

-- Behavior of `_orBool_` and `_andBool_`
axiom orBool_def (b₁ b₂ : SortBool) : _orBool_ b₁ b₂ = some (b₁ || b₂)
axiom andBool_def (b₁ b₂ : SortBool) : _andBool_ b₁ b₂ = some (b₁ && b₂)
axiom notBool_def (b : SortBool) : notBool_ b = some (!b)

-- Behavior of arithmetical comparisons
axiom ltInt_def (n m : SortInt) : «_<Int_» n m = some (decide (n < m))

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
  let val1 ← «_+Int_» val0 1
  return val1 := by
  revert n
  induction ws <;> simp_all [sizeWordStackAux, _432555e, _75897fa, plusIntIsSome]

theorem sizeWordStackAuxAdd {n : SortInt} {ws : SortWordStack} :
  sizeWordStackAux ws (n + 1) = do
  let a ← sizeWordStackAux ws n
  let b ← «_+Int_» a 1
  return b := by
  rw [←sizeWordStackNotEmpty (w := 0), sizeWordStack_add_one]

theorem sizeWordStackIsSome {ws : SortWordStack} :
  sizeWordStackAux ws 0 = some (wsLength ws) := by
  unfold sizeWordStackAux
  induction' ws
  . aesop (add simp [sizeWordStackAux, _432555e])
  . simp_all [sizeWordStack_add_one, wsLength]; rewrite [←sizeWordStackAux] at *
    aesop (add simp [sizeWordStack_add_one])

theorem wsLength_eq_length_wordStackMap {ws : SortWordStack} :
  wsLength ws = List.length (wordStackMap ws) := by
  induction ws <;> simp_all [wsLength]

theorem sizeWordStack_def {ws : SortWordStack} :
  sizeWordStackAux ws 0 = some (List.length (wordStackMap ws)) :=
  wsLength_eq_length_wordStackMap ▸ sizeWordStackIsSome


-- Behavior of `AccountCellMapItem`
-- TODO: Complete or delete
/--
Note that this function is dependent on the current implementation of `SortAccountCellMap`

The current implementation is `List (SortAcctIDCell × SortAccountCell)` but
this might change in the future
-/
def accountCellMapItem_def (x0 : SortAcctIDCell) (x1 : SortAccountCell) : Option SortAccountCellMap :=
  some (⟨[(x0, x1)]⟩)

-- Behavior of `kite`
@[simp]
theorem kite_def {SortSort : Type} (cnd : SortBool) (true_branch false_branch: SortSort) :
  kite cnd true_branch false_branch = ite cnd true_branch false_branch := by
  aesop

-- Behavior of K's `in_keys` function
-- NOTE: These functions depend on the dummy implementation as maps
-- being `List (Key × Value)`
def keys {K V : Type} (l : List (K × V)) : List K :=
  List.map (λ pair => pair.1) l

def inKeys_compute (map : SortMap) (key : SortInt) : Bool :=
  List.elem (inj key) (keys map.coll)

@[simp]
axiom Axioms.inKeys_def (map : SortMap) (key : SortInt) :
  «_in_keys(_)_MAP_Bool_KItem_Map» (inj ((inj key) : SortAccount)) map =
  some (inKeys_compute map key)

-- Behavior of `#inStorage`
noncomputable def inStorage_compute (map : SortMap) (acc key : SortInt) : Bool :=
  match «Map:lookup» map (inj ((@inj SortInt SortAccount) acc)) with
  | none => false
  | some a => match «#inStorageAux1» a key with
    | none => false
    | some b => if inKeys_compute map acc then b else false

@[simp]
theorem inStorage_def {ACCESSEDSTORAGE_CELL : SortMap} {ID_CELL W0 : SortInt} :
  «#inStorage» ACCESSEDSTORAGE_CELL ((@inj SortInt SortAccount) ID_CELL) W0 = some (inStorage_compute ACCESSEDSTORAGE_CELL ID_CELL W0) := by
  aesop (add simp [«#inStorage», _dbb1f9e, _8d90a32, Option.bind, inStorage_compute])

-- Helper theorems

@[simp]
theorem inj_ID_CELL (ID_CELL : SortInt) : @inj SortInt SortAccount instInjSortIntSortAccount ID_CELL = .inj_SortInt ID_CELL := rfl

@[simp]
theorem accountAddressIsSome (n : ℕ) (size : n < AccountAddress.size) : AccountAddress.ofNat n = ⟨n, size⟩ := by
  simp [AccountAddress.ofNat, Fin.ofNat]; aesop

end KEVMInterface
