import EvmYul.EVM.Semantics
import EvmEquivalence.KEVM2Lean.Sorts
import EvmEquivalence.KEVM2Lean.Inj
import EvmEquivalence.KEVM2Lean.Func
import EvmEquivalence.KEVM2Lean.Rewrite
import EvmEquivalence.Interfaces.EvmYulInterface
import EvmEquivalence.Interfaces.Axioms
import EvmEquivalence.Utils.IntUtils

/-! # State Map

Mapping KEVM to EvmYul states.
-/

open EvmYul
open EVM

set_option linter.deprecated false


/-! ## `SortGeneratedTopCell` Getters

Getters for accessing cells from the Generated Top Cell.
-/

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

@[simp]
def isStatic : SortStaticCell := tc.kevm.ethereum.evm.callState.static

@[simp]
def memoryUsed : SortMemoryUsedCell := tc.kevm.ethereum.evm.callState.memoryUsed

@[simp]
def memory : SortLocalMemCell := tc.kevm.ethereum.evm.callState.localMem

@[simp]
def origin : SortOriginCell := tc.kevm.ethereum.evm.origin

@[simp]
def caller : SortCallerCell := tc.kevm.ethereum.evm.callState.caller

@[simp]
def gasPrice : SortGasPriceCell := tc.kevm.ethereum.evm.gasPrice

@[simp]
def coinbase : SortCoinbaseCell := tc.kevm.ethereum.evm.block.coinbase

@[simp]
def timestamp : SortTimestampCell := tc.kevm.ethereum.evm.block.timestamp

@[simp]
def mixhash : SortMixHashCell := tc.kevm.ethereum.evm.block.mixHash

@[simp]
def number : SortNumberCell := tc.kevm.ethereum.evm.block.number

@[simp]
def gaslimit : SortGasLimitCell := tc.kevm.ethereum.evm.block.gasLimit

@[simp]
def chainid : SortChainIDCell := tc.kevm.ethereum.network.chainID

end SortGeneratedTopCell

namespace SortKItem

/-- KItem projections to subsorts -/
@[simp]
def toAccountSort (k : SortKItem) : Option SortAccount :=
  match k with
  | .inj_SortAccount acc => some acc
  | _ => none

/-- Subsort projections to KItem -/
@[simp]
def ofAccountSort(acc : SortAccount) : SortKItem :=
  SortKItem.inj_SortAccount acc

end SortKItem

open SortKItem

namespace StateMap

/-! ## Type Mapping

Maps from K types to EvmYul types.
-/

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
def gasMap : SortGas → UInt256
  | .inj_SortInt g => intMap g

@[simp]
def gasCellMap (gc : SortGasCell) : UInt256 :=
  gasMap gc.val

@[simp]
def accountAddressMap : SortAccount → AccountAddress
  | .«.Account_EVM-TYPES_Account» => 0
  | .inj_SortInt n => AccountAddress.ofNat (Int.toNat n)

@[simp]
def idMap (idc : SortIdCell) : AccountAddress :=
  accountAddressMap idc.val

@[simp]
noncomputable def storageMap (stor : SortStorageCell) : Storage :=
  Axioms.SortStorageCellMap stor

@[simp]
noncomputable def transStorageMap (tstor : SortTransientStorageCell) : Storage :=
  Axioms.SortTransientStorageCellMap tstor

@[simp]
def accCodeMap : SortAccountCode → ByteArray
  | .inj_SortBytes code => code

/- Note that Origin Storage Cell (`origStorage`) is not needed from `SortAccountCell` -/
@[simp]
noncomputable def accountMap (acc : SortAccountCell) : Account where
  nonce := intMap acc.nonce.val
  balance := intMap acc.balance.val
  storage := storageMap acc.storage
  code := accCodeMap acc.code.val
  tstorage := transStorageMap acc.transientStorage

@[simp]
noncomputable def substate_map (sc : SortSubstateCell) (s : Substate) : Substate :=
  match sc with
  | .mk
    _ --selfDestruct
    _ --log
    refund
    _ --accessedAccounts
    accessedStorage
    _ --createdAccounts
    => {s with
         accessedStorageKeys :=  Axioms.SortAccessedStorageCellMap accessedStorage
         refundBalance := intMap refund.val}

@[simp]
def memory_map : SortLocalMemCell → ByteArray | .mk b => b

/- Maps from parts of the Generated Top Cell to EvmYul structures -/

@[simp]
def blockHeader_map (tc : SortGeneratedTopCell) (s : EVM.State) : BlockHeader :=
  {s.executionEnv.header with
    beneficiary := .ofNat <| Int.toNat tc.coinbase.val
    timestamp := Int.toNat tc.timestamp.val
    number := Int.toNat tc.number.val
    prevRandao := intMap tc.mixhash.val
    gasLimit := Int.toNat tc.gaslimit.val
  }

@[simp]
def executionEnv_map (tc : SortGeneratedTopCell) (s : EVM.State) : ExecutionEnv :=
  {s.executionEnv with
    codeOwner := idMap tc.Iₐ
    source := accountAddressMap tc.caller.val
    sender := accountAddressMap tc.origin.val
    code := tc.program.val,
    gasPrice := Int.toNat tc.gasPrice.val
    header := blockHeader_map tc s
    perm := !tc.isStatic.val}

/-! ## State Map

The function mapping KEVM states to EvmYul states.
-/

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
  executionEnv := executionEnv_map tc symState
  accountMap := Axioms.SortAccountsCellMap tc.accounts
  substate := {symState.substate with
            accessedStorageKeys :=  Axioms.SortAccessedStorageCellMap tc.accessedStorage
            refundBalance := intMap tc.refund.val
           }
  returnData := tc.output.val
  activeWords := intMap tc.memoryUsed.val
  memory := memory_map tc.memory
  }

/-! ## State Mapping Results

Theorems to make life easier.
-/

theorem intMap_sub_dist {n m : SortInt} (le_m_n : m <= n) (pos : 0 <= m) (size : n < UInt256.size) :
  intMap (n - m) = intMap n - intMap m := by
  unfold intMap UInt256.toSigned; split <;> rename_i a b h
  . cases cn : n with
    | ofNat p => cases m with
                | ofNat q =>
                simp_all
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

/-! ## State Map Axioms

Axioms that have to do with the axiomatic state mapping.
-/

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
  :
  Batteries.RBMap.insert (Axioms.SortAccountsCellMap { val := initCellMap }) (accountAddressMap (inj ID_CELL))
    ((accountMap {
    acctID := { val := ID_CELL },
    balance := balance,
    code := code,
    storage := { val := STORAGE_CELL },
    origStorage := { val := ORIG_STORAGE_CELL },
    transientStorage := tstorage,
    nonce := nonce }).updateStorage (intMap key) (intMap value)) =
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

/--
Mapping a `SortStorageCell` through `Axioms.SortStorageCellMap` results
in an equivalence of behavior between K's `lookup` function and EvmYul's `findD`.
Provided that `lookup` results in `some result`.
-/
axiom lookup_mapped_storage (storage : SortMap) (key result : SortInt) (_ : lookup storage key = some result):
  Batteries.RBMap.findD (Axioms.SortStorageCellMap { val := storage }) (intMap key) { val := 0 } = intMap result


/--
Mapping a `SortAccessedStorageCell` through `Axioms.SortAccessedStorageCellMap` results
in an equivalence of behavior between K's `«#inStorage»` function and EvmYul's `RBSet.contains`.
-/
axiom contains_accessedStorage_map
  {contained : Bool}
  {stor : SortMap}
  {acc key : SortInt}
  (_ : «#inStorage» stor (SortAccount.inj_SortInt acc) key = some contained):
  (Axioms.SortAccessedStorageCellMap { val := stor }).contains
  (AccountAddress.ofNat (Int.toNat acc), intMap key) = contained

end Axioms
