import EvmYul.EVM.Semantics
import EvmEquivalence.KEVM2Lean.Sorts
import EvmEquivalence.KEVM2Lean.Inj
import EvmEquivalence.KEVM2Lean.Func
import EvmEquivalence.KEVM2Lean.Rewrite
import EvmEquivalence.Interfaces.EvmYulInterface
import EvmEquivalence.Interfaces.Axioms
import EvmEquivalence.Utils.IntUtils

open EvmYul
open EVM

set_option linter.deprecated false

/- Getters for accessing cells from the Generated Top Cell -/

namespace SortGeneratedTopCell

variable (tc : SortGeneratedTopCell)

@[simp]
def evm :SortEvmCell := tc.kevm.ethereum.evm

@[simp]
def callState : SortCallStateCell := tc.kevm.ethereum.evm.callState

@[simp]
def wordStackCell : SortWordStackCell := tc.kevm.ethereum.evm.callState.wordStack

@[simp]
def pc : SortPcCell := tc.kevm.ethereum.evm.callState.pc

@[simp]
def gas : SortGasCell := tc.kevm.ethereum.evm.callState.gas

@[simp]
def program : SortProgramCell := tc.kevm.ethereum.evm.callState.program

@[simp]
def output : SortOutputCell := tc.kevm.ethereum.evm.output

@[simp]
def accessedStorage : SortAccessedStorageCell := tc.kevm.ethereum.evm.substate.accessedStorage

@[simp]
def refund : SortRefundCell := tc.kevm.ethereum.evm.substate.refund

@[simp]
def accounts : SortAccountsCell := tc.kevm.ethereum.network.accounts

@[simp]
def Iₐ : SortIdCell := tc.kevm.ethereum.evm.callState.id

end SortGeneratedTopCell

namespace SortKItem

/- KItem projections to subsorts -/
@[simp]
def toAccountSort (k : SortKItem) : Option SortAccount :=
  match k with
  | .inj_SortAccount acc => some acc
  | _ => none

/- Subsort projections to KItem -/
@[simp]
def ofAccountSort(acc : SortAccount) : SortKItem :=
  SortKItem.inj_SortAccount acc

end SortKItem

open SortKItem

namespace StateMap

/- Maps from K types to EvmYul types -/
abbrev intMap (n : SortInt) : UInt256 := UInt256.toSigned n

@[simp]
def wordStackMap (ws : SortWordStack) : Stack UInt256 :=
  match ws with
  | .«.WordStack_EVM-TYPES_WordStack» => []
  | .«_:__EVM-TYPES_WordStack_Int_WordStack» w ws => intMap w :: (wordStackMap ws)

@[simp]
def wordStackCellMap (wsc : SortWordStackCell) : Stack UInt256 :=
  wordStackMap wsc.val

@[simp]
def pcCellMap (pcc : SortPcCell) : UInt256 :=
  intMap pcc.val

@[simp]
def gasMap (gs : SortGas) : UInt256 :=
  match gs with | .inj_SortInt g => intMap g

@[simp]
def gasCellMap (gc : SortGasCell) : UInt256 :=
  gasMap gc.val

@[simp]
def accountAddressMap (acc : SortAccount) : AccountAddress :=
  match acc with
  | .«.Account_EVM-TYPES_Account» => 0
  | .inj_SortInt n => AccountAddress.ofNat (Int.toNat n)

@[simp]
def idMap (idc : SortIdCell) : AccountAddress :=
  accountAddressMap idc.val

@[simp]
def acctIDMap (aid : SortAcctIDCell) : AccountAddress :=
  AccountAddress.ofNat (Int.toNat aid.val)

@[simp]
noncomputable def storageMap (stor : SortStorageCell) : Storage :=
  Axioms.SortStorageCellMap stor

@[simp]
noncomputable def transStorageMap (tstor : SortTransientStorageCell) : Storage :=
  Axioms.SortTransientStorageCellMap tstor

@[simp]
def accCodeMap (code : SortAccountCode) : ByteArray :=
  match code with | SortAccountCode.inj_SortBytes code => code

/- Note that Origin Storage Cell (`origStorage`) is not needed from `SortAccountCell` -/
@[simp]
noncomputable def accountMap (acc : SortAccountCell) : Account where
  nonce := intMap acc.nonce.val
  balance := intMap acc.balance.val
  storage := storageMap acc.storage
  code := accCodeMap acc.code.val
  tstorage := transStorageMap acc.transientStorage

/--
**State Mapping**: Mapping KEVM states to EvmYul states

We temporarely require the `symState` argument since we don't map the entire KEVM state yet

The following data structures are axiomatically mapped:
1. `Substate.accessedStorageKeys`:
  The `EvmYul` data representation for this is an `RBSet`, which is hard to reason about.
  The mapping will remain an axiom until a better reasoning interface is provided or we have time to implement it
2. `State.accountMap`: Similar reasons as above
-/
noncomputable def stateMap (symState : EVM.State) (tc : SortGeneratedTopCell) : EVM.State :=
  {symState with
  stack := wordStackCellMap tc.wordStackCell
  pc := pcCellMap tc.pc
  gasAvailable := gasCellMap tc.gas
  executionEnv := {symState.executionEnv with
                code := tc.program.val,
                codeOwner := idMap tc.Iₐ}
  accountMap := Axioms.SortAccountsCellMap tc.accounts
  substate := {symState.substate with
            accessedStorageKeys :=  Axioms.SortAccessedStorageCellMap tc.accessedStorage
            refundBalance := intMap tc.refund.val
           }
  returnData := tc.output.val
  }

/- State Mapping Results -/
/- Theorems to make life easier -/

theorem intMap_sub_dist {n m : SortInt} (le_m_n : m <= n) (pos : 0 <= m) (size : n < UInt256.size) :
  intMap (n - m) = intMap n - intMap m := by
  unfold intMap UInt256.toSigned; split <;> rename_i a b h
  . cases cn : n with
    | ofNat p => cases m with
                | ofNat q =>
                simp_all [Int.ofNat]
                rw [←Int.ofNat_sub, Int.ofNat_inj] at h <;> try assumption
                simp only [←h, HSub.hSub, Sub.sub, UInt256.sub, Fin.sub]
                aesop (add simp [UInt256.ofNat_eq, UInt256.size, Fin.ofNat])
                      (add safe (by omega))
                | negSucc q => aesop
    | negSucc p =>
      have _ : 0 ≤ n := by apply (Int.le_trans pos le_m_n)
      aesop
  . rw [←sub_nonneg, h] at le_m_n; contradiction

theorem intMap_add_dist {n m : SortInt} (nh : 0 ≤ n) (mh : 0 ≤ m) :
  intMap ((n + m) % ↑UInt256.size) = intMap n + intMap m := by
  unfold intMap UInt256.toSigned
  split; rename_i h p mod_eq
  . split <;> split <;> rename_i h' q j l <;> try contradiction
    . simp_all only [Int.ofNat_eq_coe, Int.ofNat_add_ofNat]
      rw [Int.mod_cast, Int.toNat_ofNat, Int.ofNat_inj] at * <;> try simp
      . aesop (add simp [UInt256.ofNat, UInt256.size, Id.run, dbgTrace, Fin.ofNat])
              (add safe (by congr 1))
      . aesop (add safe (by omega))
  . have mod_nonneg: 0 ≤ (n + m) % ↑UInt256.size := by
      rw [Int.mod_def']; apply Int.emod_nonneg; simp [UInt256.size]
    simp_all

theorem intMap_toNat {n : SortInt} (nh : 0 ≤ n) (size : n < UInt256.size) :
  (intMap n).toNat = n.toNat := by
  aesop (add simp [intMap, Int.toNat, UInt256.toSigned, Int.toNat_ofNat, UInt256.ofNat_toNat])

end StateMap

open StateMap

namespace Axioms

/--
This axiom states that if an account is in an `AccountCellMap`, then
`Batteries.RBMap.find?` finds it in the image of the axiomatized mapping

The second element of `AccountCellMapItem` is provided embedded in `accCellMap_def` for
ease of use when proving theorems
 -/
axiom findAccountInAccountCellMap
  {ID_CELL : SortInt}
  {balance : SortBalanceCell}
  {code : SortCodeCell}
  {STORAGE_CELL ORIG_STORAGE_CELL : SortMap}
  {tstorage : SortTransientStorageCell}
  {nonce : SortNonceCell}
  {accCellMap dotVar accCellMap2 : SortAccountCellMap}
  (accCellMap_def : AccountCellMapItem { val := ID_CELL } {
    acctID := { val := ID_CELL },
    balance := balance,
    code := code,
    storage := { val := STORAGE_CELL },
    origStorage := { val := ORIG_STORAGE_CELL },
    transientStorage := tstorage,
    nonce := nonce } = some accCellMap)
  (accCellMap2_def : _AccountCellMap_ accCellMap dotVar = some accCellMap2) :
  Batteries.RBMap.find? (Axioms.SortAccountsCellMap { val := accCellMap2 }) (AccountAddress.ofNat (Int.toNat ID_CELL)) = some (StateMap.accountMap {
    acctID := { val := ID_CELL },
    balance := balance,
    code := code,
    storage := { val := STORAGE_CELL },
    origStorage := { val := ORIG_STORAGE_CELL },
    transientStorage := tstorage,
    nonce := nonce })

/--
Expected behavior of `SortAccountsCellMap` w.r.t. `Batteries.RBMap.find?`

This axiom states that
- Given an `accountsCell` (`accCellMap2`) containing an account identifiable by `ID_CELL` (`acc`)
- The (axiomatic) mapping of `accCellMap2` contains the mapping of `acc`
- And, in particular, `RBMap.find?` correctly finds the mapped `acc` if provided with the mapped `ID_CELL`
 -/
axiom accountsCell_map_find?
  {ID_CELL : SortInt}
  {balance : SortBalanceCell}
  {code : SortCodeCell}
  {STORAGE_CELL ORIG_STORAGE_CELL : SortMap}
  {tstorage : SortTransientStorageCell}
  {nonce : SortNonceCell}
  {accCellMap dotVar accCellMap2 : SortAccountCellMap}
  (acc : SortAccountCell)
  (acc_def : acc = {
    acctID := { val := ID_CELL },
    balance := balance,
    code := code,
    storage := { val := STORAGE_CELL },
    origStorage := { val := ORIG_STORAGE_CELL },
    transientStorage := tstorage,
    nonce := nonce })
  (accCellMap_def : AccountCellMapItem { val := ID_CELL } acc = some accCellMap)
  (accCellMap2_def : _AccountCellMap_ accCellMap dotVar = some accCellMap2) :
  Batteries.RBMap.find? (Axioms.SortAccountsCellMap { val := accCellMap2 }) (AccountAddress.ofNat (Int.toNat ID_CELL)) = some (StateMap.accountMap acc)

/--
Expected behavior of `SortAccountsCellMap` w.r.t. `Batteries.RBMap.insert`

This axiom states that
- Given an `accountsCell` (`initCellMap`) containing an account identifiable by `ID_CELL` (`initAccount`) with symbolic storage `STORAGE_CELL`
- Given an updated `accountsCell` (`updatedCellMap`) consisting of `initAccount` with an updated `STORAGE_CELL` which contains the symbolic (`key`, `value`) pair (`stor_update`)
- `RBMap.insert`ing the mapped (`key`, `value`) pair into the (axiomatically) mapped `initCellMap` equals to the (axiomatic) mapping of `updatedCellMap`
 -/
axiom accountsCell_map_insert
  {ID_CELL key value : SortInt}
  {balance : SortBalanceCell}
  {code : SortCodeCell}
  {tstorage : SortTransientStorageCell}
  {nonce : SortNonceCell}
  {ACCESSEDSTORAGE_CELL ORIG_STORAGE_CELL STORAGE_CELL stor_update : SortMap}
  {emptySet kitemToSet keySet fullSet : SortSet}
  {kitemLookup : SortKItem}
  {dotvar initAccount initCellMap updatedAccount updatedCellMap : SortAccountCellMap}
  (defn_Val34 : «.Set» = some emptySet)
  (defn_Val35 : «Map:lookupOrDefault» ACCESSEDSTORAGE_CELL ((@inj SortInt SortKItem) ID_CELL) ((@inj SortSet SortKItem) emptySet) = some kitemLookup)
  (defn_Val36 : «project:Set» (SortK.kseq kitemLookup SortK.dotk) = some kitemToSet)
  (defn_Val37 : SetItem ((@inj SortInt SortKItem) key) = some keySet)
  (defn_Val38 : «_|Set__SET_Set_Set_Set» kitemToSet keySet = some fullSet)
  (defn_Val40 : «Map:update» STORAGE_CELL ((@inj SortInt SortKItem) key) ((@inj SortInt SortKItem) value) = some stor_update)
  (defn_Val41 : AccountCellMapItem { val := ID_CELL } {
    acctID := { val := ID_CELL },
    balance := balance,
    code := code,
    storage := { val := stor_update },
    origStorage := { val := ORIG_STORAGE_CELL },
    transientStorage := tstorage,
    nonce := nonce } = some updatedAccount)
  (defn_Val42 : _AccountCellMap_ updatedAccount dotvar = some updatedCellMap)
  (defn_Val19 : AccountCellMapItem { val := ID_CELL } {
    acctID := { val := ID_CELL },
    balance := balance,
    code := code,
    storage := { val := STORAGE_CELL },
    origStorage := { val := ORIG_STORAGE_CELL },
    transientStorage := tstorage,
    nonce := nonce } = some initAccount)
  (defn_Val20 : _AccountCellMap_ initAccount dotvar = some initCellMap)
  (ownerAcc : Account)
  :
  Batteries.RBMap.insert (Axioms.SortAccountsCellMap { val := initCellMap }) (accountAddressMap (inj ID_CELL))
    (ownerAcc.updateStorage (intMap key) (intMap value)) =
  Axioms.SortAccountsCellMap { val := updatedCellMap }

/--
Expected behavior of `SortAccessedStorageCellMap` w.r.t. `Batteries.RBSet.insert`

This axiom states that
- Given a symbolic map of accessed storage keys `ACCESSEDSTORAGE_CELL`
- Given an update of `ACCESSEDSTORAGE_CELL` containing the account `ID_CELL` and the key `key` (`stor_update`)
- `RBMap.insert`ing the mapped pair (`ID_CELL`, `key`) into the (axiomatically) mapped `ACCESSEDSTORAGE_CELL` equals to the (axiomatic) mapping of `stor_update`
 -/
axiom accessedStorageCell_map_insert
    {ID_CELL key : SortInt}
  {ACCESSEDSTORAGE_CELL stor_update : SortMap}
  {emptySet kitemToSet keySet fullSet : SortSet}
  {kitemLookup : SortKItem}
  (defn_Val34 : «.Set» = some emptySet)
  (defn_Val35 : «Map:lookupOrDefault» ACCESSEDSTORAGE_CELL ((@inj SortInt SortKItem) ID_CELL) ((@inj SortSet SortKItem) emptySet) = some kitemLookup)
  (defn_Val36 : «project:Set» (SortK.kseq kitemLookup SortK.dotk) = some kitemToSet)
  (defn_Val37 : SetItem ((@inj SortInt SortKItem) key) = some keySet)
  (defn_Val38 : «_|Set__SET_Set_Set_Set» kitemToSet keySet = some fullSet)
  (defn_Val39 : «Map:update» ACCESSEDSTORAGE_CELL ((@inj SortInt SortKItem) ID_CELL) ((@inj SortSet SortKItem) fullSet) = some stor_update) :
  (Axioms.SortAccessedStorageCellMap { val := ACCESSEDSTORAGE_CELL }).insert
    (AccountAddress.ofNat (Int.toNat ID_CELL), intMap key) =
  Axioms.SortAccessedStorageCellMap { val := stor_update }

end Axioms
