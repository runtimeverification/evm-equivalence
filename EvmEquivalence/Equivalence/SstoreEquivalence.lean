import EvmEquivalence.Summaries.SstoreSummary
import EvmEquivalence.Interfaces.EvmYulInterface
import EvmEquivalence.Interfaces.GasInterface
import EvmEquivalence.Interfaces.FuncInterface
import EvmEquivalence.StateMap

open EvmYul
open StateMap
open KEVMInterface
open SstoreSummary

namespace SstoreOpcodeEquivalence

def sstoreLHS
  {ACCESSEDSTORAGE_CELL : SortMap}
  {GAS_CELL ID_CELL PC_CELL REFUND_CELL W0 W1 : SortInt}
  {K_CELL : SortK}
  {SCHEDULE_CELL : SortSchedule}
  {USEGAS_CELL : SortBool}
  {WS : SortWordStack}
  {_DotVar0 : SortGeneratedCounterCell}
  {_DotVar6 _Val20 : SortAccountCellMap}
  {_Gen0 : SortProgramCell}
  {_Gen1 : SortJumpDestsCell}
  {_Gen10 : SortLogCell}
  {_Gen11 : SortAccessedAccountsCell}
  {_Gen12 : SortCreatedAccountsCell}
  {_Gen13 : SortOutputCell}
  {_Gen14 : SortStatusCodeCell}
  {_Gen15 : SortCallStackCell}
  {_Gen16 : SortInterimStatesCell}
  {_Gen17 : SortTouchedAccountsCell}
  {_Gen18 : SortVersionedHashesCell}
  {_Gen19 : SortGasPriceCell}
  {_Gen2 : SortCallerCell}
  {_Gen20 : SortOriginCell}
  {_Gen21 : SortBlockhashesCell}
  {_Gen22 : SortBlockCell}
  {_Gen23 : SortBalanceCell}
  {_Gen24 : SortCodeCell}
  {_Gen25 : SortTransientStorageCell}
  {_Gen26 : SortNonceCell}
  {_Gen27 : SortChainIDCell}
  {_Gen28 : SortTxOrderCell}
  {_Gen29 : SortTxPendingCell}
  {_Gen3 : SortCallDataCell}
  {_Gen30 : SortMessagesCell}
  {_Gen31 : SortWithdrawalsPendingCell}
  {_Gen32 : SortWithdrawalsOrderCell}
  {_Gen33 : SortWithdrawalsCell}
  {_Gen34 : SortExitCodeCell}
  {_Gen35 : SortModeCell}
  {_Gen4 : SortCallValueCell}
  {_Gen5 : SortLocalMemCell}
  {_Gen6 : SortMemoryUsedCell}
  {_Gen7 : SortCallGasCell}
  {_Gen8 : SortCallDepthCell}
  {_Gen9 : SortSelfDestructCell} : SortGeneratedTopCell :=
  { kevm := {
      k := { val := SortK.kseq ((@inj SortInternalOp SortKItem) (SortInternalOp.«#next[_]_EVM_InternalOp_MaybeOpCode» ((@inj SortBinStackOp SortMaybeOpCode) SortBinStackOp.SSTORE_EVM_BinStackOp))) K_CELL },
      exitCode := _Gen34,
      mode := _Gen35,
      schedule := { val := SCHEDULE_CELL },
      useGas := { val := USEGAS_CELL },
      ethereum := {
        evm := {
          output := _Gen13,
          statusCode := _Gen14,
          callStack := _Gen15,
          interimStates := _Gen16,
          touchedAccounts := _Gen17,
          callState := {
            program := _Gen0,
            jumpDests := _Gen1,
            id := { val := (@inj SortInt SortAccount) ID_CELL },
            caller := _Gen2,
            callData := _Gen3,
            callValue := _Gen4,
            wordStack := { val := SortWordStack.«_:__EVM-TYPES_WordStack_Int_WordStack» W0 (SortWordStack.«_:__EVM-TYPES_WordStack_Int_WordStack» W1 WS) },
            localMem := _Gen5,
            pc := { val := PC_CELL },
            gas := { val := (@inj SortInt SortGas) GAS_CELL },
            memoryUsed := _Gen6,
            callGas := _Gen7,
            static := { val := false },
            callDepth := _Gen8 },
          versionedHashes := _Gen18,
          substate := {
            selfDestruct := _Gen9,
            log := _Gen10,
            refund := { val := REFUND_CELL },
            accessedAccounts := _Gen11,
            accessedStorage := { val := ACCESSEDSTORAGE_CELL },
            createdAccounts := _Gen12 },
          gasPrice := _Gen19,
          origin := _Gen20,
          blockhashes := _Gen21,
          block := _Gen22 },
        network := {
          chainID := _Gen27,
          accounts := { val := _Val20 },
          txOrder := _Gen28,
          txPending := _Gen29,
          messages := _Gen30,
          withdrawalsPending := _Gen31,
          withdrawalsOrder := _Gen32,
          withdrawals := _Gen33 } } },
    generatedCounter := _DotVar0 }

def sstoreRHS
  { _Val39 _Val40 : SortMap}
  { ID_CELL _Val1 _Val10 _Val11 _Val13 _Val2 _Val21 _Val22 _Val23 _Val24 _Val25 _Val27 _Val28 _Val29 _Val3 _Val30 _Val31 _Val32 _Val33 _Val6 _Val7 _Val8 _Val9 : SortInt}
  {K_CELL : SortK}
  {SCHEDULE_CELL : SortSchedule}
  {_Val0 _Val12 _Val14 _Val15 _Val16 _Val17 _Val18 _Val26 _Val4 _Val5 : SortBool}
  {WS : SortWordStack}
  {_DotVar0 : SortGeneratedCounterCell}
  {_DotVar6 _Val19 _Val20 _Val41 _Val42 : SortAccountCellMap}
  {_Gen0 : SortProgramCell}
  {_Gen1 : SortJumpDestsCell}
  {_Gen10 : SortLogCell}
  {_Gen11 : SortAccessedAccountsCell}
  {_Gen12 : SortCreatedAccountsCell}
  {_Gen13 : SortOutputCell}
  {_Gen14 : SortStatusCodeCell}
  {_Gen15 : SortCallStackCell}
  {_Gen16 : SortInterimStatesCell}
  {_Gen17 : SortTouchedAccountsCell}
  {_Gen18 : SortVersionedHashesCell}
  {_Gen19 : SortGasPriceCell}
  {_Gen2 : SortCallerCell}
  {_Gen20 : SortOriginCell}
  {_Gen21 : SortBlockhashesCell}
  {_Gen22 : SortBlockCell}
  {_Gen23 : SortBalanceCell}
  {_Gen24 : SortCodeCell}
  {_Gen25 : SortTransientStorageCell}
  {_Gen26 : SortNonceCell}
  {_Gen27 : SortChainIDCell}
  {_Gen28 : SortTxOrderCell}
  {_Gen29 : SortTxPendingCell}
  {_Gen3 : SortCallDataCell}
  {_Gen30 : SortMessagesCell}
  {_Gen31 : SortWithdrawalsPendingCell}
  {_Gen32 : SortWithdrawalsOrderCell}
  {_Gen33 : SortWithdrawalsCell}
  {_Gen34 : SortExitCodeCell}
  {_Gen35 : SortModeCell}
  {_Gen4 : SortCallValueCell}
  {_Gen5 : SortLocalMemCell}
  {_Gen6 : SortMemoryUsedCell}
  {_Gen7 : SortCallGasCell}
  {_Gen8 : SortCallDepthCell}
  {_Gen9 : SortSelfDestructCell}
  {_Val34 _Val36 _Val37 _Val38 : SortSet}
  {_Val35 : SortKItem} : SortGeneratedTopCell :=
  { kevm := {
      k := { val := K_CELL },
      exitCode := _Gen34,
      mode := _Gen35,
      schedule := { val := SCHEDULE_CELL },
      useGas := { val := true },
      ethereum := {
        evm := {
          output := _Gen13,
          statusCode := _Gen14,
          callStack := _Gen15,
          interimStates := _Gen16,
          touchedAccounts := _Gen17,
          callState := {
            program := _Gen0,
            jumpDests := _Gen1,
            id := { val := (@inj SortInt SortAccount) ID_CELL },
            caller := _Gen2,
            callData := _Gen3,
            callValue := _Gen4,
            wordStack := { val := WS },
            localMem := _Gen5,
            pc := { val := _Val21 },
            gas := { val := (@inj SortInt SortGas) _Val29 },
            memoryUsed := _Gen6,
            callGas := _Gen7,
            static := { val := false },
            callDepth := _Gen8 },
          versionedHashes := _Gen18,
          substate := {
            selfDestruct := _Gen9,
            log := _Gen10,
            refund := { val := _Val33 },
            accessedAccounts := _Gen11,
            accessedStorage := { val := _Val39 },
            createdAccounts := _Gen12 },
          gasPrice := _Gen19,
          origin := _Gen20,
          blockhashes := _Gen21,
          block := _Gen22 },
        network := {
          chainID := _Gen27,
          accounts := { val := _Val42 },
          txOrder := _Gen28,
          txPending := _Gen29,
          messages := _Gen30,
          withdrawalsPending := _Gen31,
          withdrawalsOrder := _Gen32,
          withdrawals := _Gen33 } } },
    generatedCounter := _DotVar0 }

theorem rw_sstoreLHS_sstoreRHS
  {ACCESSEDSTORAGE_CELL ORIG_STORAGE_CELL STORAGE_CELL _Val39 _Val40 : SortMap}
  {GAS_CELL ID_CELL PC_CELL REFUND_CELL W0 W1 _Val1 _Val10 _Val11 _Val13 _Val2 _Val21 _Val22 _Val23 _Val24 _Val25 _Val27 _Val28 _Val29 _Val3 _Val30 _Val31 _Val32 _Val33 _Val6 _Val7 _Val8 _Val9 : SortInt}
  {K_CELL : SortK}
  {SCHEDULE_CELL : SortSchedule}
  {USEGAS_CELL _Val0 _Val12 _Val14 _Val15 _Val16 _Val17 _Val18 _Val26 _Val4 _Val5 : SortBool}
  {WS : SortWordStack}
  {_DotVar0 : SortGeneratedCounterCell}
  {_DotVar6 _Val19 _Val20 _Val41 _Val42 : SortAccountCellMap}
  {_Gen0 : SortProgramCell}
  {_Gen1 : SortJumpDestsCell}
  {_Gen10 : SortLogCell}
  {_Gen11 : SortAccessedAccountsCell}
  {_Gen12 : SortCreatedAccountsCell}
  {_Gen13 : SortOutputCell}
  {_Gen14 : SortStatusCodeCell}
  {_Gen15 : SortCallStackCell}
  {_Gen16 : SortInterimStatesCell}
  {_Gen17 : SortTouchedAccountsCell}
  {_Gen18 : SortVersionedHashesCell}
  {_Gen19 : SortGasPriceCell}
  {_Gen2 : SortCallerCell}
  {_Gen20 : SortOriginCell}
  {_Gen21 : SortBlockhashesCell}
  {_Gen22 : SortBlockCell}
  {_Gen23 : SortBalanceCell}
  {_Gen24 : SortCodeCell}
  {_Gen25 : SortTransientStorageCell}
  {_Gen26 : SortNonceCell}
  {_Gen27 : SortChainIDCell}
  {_Gen28 : SortTxOrderCell}
  {_Gen29 : SortTxPendingCell}
  {_Gen3 : SortCallDataCell}
  {_Gen30 : SortMessagesCell}
  {_Gen31 : SortWithdrawalsPendingCell}
  {_Gen32 : SortWithdrawalsOrderCell}
  {_Gen33 : SortWithdrawalsCell}
  {_Gen34 : SortExitCodeCell}
  {_Gen35 : SortModeCell}
  {_Gen4 : SortCallValueCell}
  {_Gen5 : SortLocalMemCell}
  {_Gen6 : SortMemoryUsedCell}
  {_Gen7 : SortCallGasCell}
  {_Gen8 : SortCallDepthCell}
  {_Gen9 : SortSelfDestructCell}
  {_Val34 _Val36 _Val37 _Val38 : SortSet}
  {_Val35 : SortKItem}
  (defn_Val0 : «_<<_>>_SCHEDULE_Bool_ScheduleFlag_Schedule» SortScheduleFlag.Ghasaccesslist_SCHEDULE_ScheduleFlag SCHEDULE_CELL = some _Val0)
  (defn_Val1 : lookup STORAGE_CELL W0 = some _Val1)
  (defn_Val2 : lookup ORIG_STORAGE_CELL W0 = some _Val2)
  (defn_Val3 : Csstore SCHEDULE_CELL W1 _Val1 _Val2 = some _Val3)
  (defn_Val4 : «_<=Int_» _Val3 GAS_CELL = some _Val4)
  (defn_Val5 : «#inStorage» ACCESSEDSTORAGE_CELL ((@inj SortInt SortAccount) ID_CELL) W0 = some _Val5)
  (defn_Val6 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gcoldsload_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val6)
  (defn_Val7 : kite _Val5 0 _Val6 = some _Val7)
  (defn_Val8 : lookup STORAGE_CELL W0 = some _Val8)
  (defn_Val9 : lookup ORIG_STORAGE_CELL W0 = some _Val9)
  (defn_Val10 : Csstore SCHEDULE_CELL W1 _Val8 _Val9 = some _Val10)
  (defn_Val11 : «_-Int_» GAS_CELL _Val10 = some _Val11)
  (defn_Val12 : «_<=Int_» _Val7 _Val11 = some _Val12)
  (defn_Val13 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gcallstipend_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val13)
  (defn_Val14 : «_<Int_» _Val13 GAS_CELL = some _Val14)
  (defn_Val15 : _andBool_ _Val12 _Val14 = some _Val15)
  (defn_Val16 : _andBool_ _Val4 _Val15 = some _Val16)
  (defn_Val17 : _andBool_ _Val0 _Val16 = some _Val17)
  (defn_Val18 : _andBool_ USEGAS_CELL _Val17 = some _Val18)
  (defn_Val19 : AccountCellMapItem { val := ID_CELL } {
    acctID := { val := ID_CELL },
    balance := _Gen23,
    code := _Gen24,
    storage := { val := STORAGE_CELL },
    origStorage := { val := ORIG_STORAGE_CELL },
    transientStorage := _Gen25,
    nonce := _Gen26 } = some _Val19)
  (defn_Val20 : _AccountCellMap_ _Val19 _DotVar6 = some _Val20)
  (defn_Val21 : «_+Int_» PC_CELL 1 = some _Val21)
  (defn_Val22 : lookup STORAGE_CELL W0 = some _Val22)
  (defn_Val23 : lookup ORIG_STORAGE_CELL W0 = some _Val23)
  (defn_Val24 : Csstore SCHEDULE_CELL W1 _Val22 _Val23 = some _Val24)
  (defn_Val25 : «_-Int_» GAS_CELL _Val24 = some _Val25)
  (defn_Val26 : «#inStorage» ACCESSEDSTORAGE_CELL ((@inj SortInt SortAccount) ID_CELL) W0 = some _Val26)
  (defn_Val27 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gcoldsload_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val27)
  (defn_Val28 : kite _Val26 0 _Val27 = some _Val28)
  (defn_Val29 : «_-Int_» _Val25 _Val28 = some _Val29)
  (defn_Val30 : lookup STORAGE_CELL W0 = some _Val30)
  (defn_Val31 : lookup ORIG_STORAGE_CELL W0 = some _Val31)
  (defn_Val32 : Rsstore SCHEDULE_CELL W1 _Val30 _Val31 = some _Val32)
  (defn_Val33 : «_+Int_» REFUND_CELL _Val32 = some _Val33)
  (defn_Val34 : «.Set» = some _Val34)
  (defn_Val35 : «Map:lookupOrDefault» ACCESSEDSTORAGE_CELL ((@inj SortInt SortKItem) ID_CELL) ((@inj SortSet SortKItem) _Val34) = some _Val35)
  (defn_Val36 : «project:Set» (SortK.kseq _Val35 SortK.dotk) = some _Val36)
  (defn_Val37 : SetItem ((@inj SortInt SortKItem) W0) = some _Val37)
  (defn_Val38 : «_|Set__SET_Set_Set_Set» _Val36 _Val37 = some _Val38)
  (defn_Val39 : «Map:update» ACCESSEDSTORAGE_CELL ((@inj SortInt SortKItem) ID_CELL) ((@inj SortSet SortKItem) _Val38) = some _Val39)
  (defn_Val40 : «Map:update» STORAGE_CELL ((@inj SortInt SortKItem) W0) ((@inj SortInt SortKItem) W1) = some _Val40)
  (defn_Val41 : AccountCellMapItem { val := ID_CELL } {
    acctID := { val := ID_CELL },
    balance := _Gen23,
    code := _Gen24,
    storage := { val := _Val40 },
    origStorage := { val := ORIG_STORAGE_CELL },
    transientStorage := _Gen25,
    nonce := _Gen26 } = some _Val41)
  (defn_Val42 : _AccountCellMap_ _Val41 _DotVar6 = some _Val42)
  (req : _Val18 = true) :
  Rewrites
  (@sstoreLHS ACCESSEDSTORAGE_CELL GAS_CELL ID_CELL PC_CELL REFUND_CELL W0 W1 K_CELL SCHEDULE_CELL USEGAS_CELL WS _DotVar0 _DotVar6 _Val20 _Gen0 _Gen1 _Gen10 _Gen11 _Gen12 _Gen13 _Gen14 _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2 _Gen20 _Gen21 _Gen22 _Gen23 _Gen24 _Gen25 _Gen26 _Gen27 _Gen28 _Gen29 _Gen3 _Gen30 _Gen31 _Gen32 _Gen33 _Gen34 _Gen35 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 _Gen9)
  (@sstoreRHS  _Val39 _Val40  ID_CELL _Val1 _Val10 _Val11 _Val13 _Val2 _Val21 _Val22 _Val23 _Val24 _Val25 _Val27 _Val28 _Val29 _Val3 _Val30 _Val31 _Val32 _Val33 _Val6 _Val7 _Val8 _Val9 K_CELL SCHEDULE_CELL _Val0 _Val12 _Val14 _Val15 _Val16 _Val17 _Val18 _Val26 _Val4 _Val5 WS _DotVar0 _DotVar6 _Val19 _Val20 _Val41 _Val42 _Gen0 _Gen1 _Gen10 _Gen11 _Gen12 _Gen13 _Gen14 _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2 _Gen20 _Gen21 _Gen22 _Gen23 _Gen24 _Gen25 _Gen26 _Gen27 _Gen28 _Gen29 _Gen3 _Gen30 _Gen31 _Gen32 _Gen33 _Gen34 _Gen35 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 _Gen9 _Val34 _Val36 _Val37 _Val38 _Val35) := by
  apply (@Rewrites.SSTORE_SUMMARY_SSTORE_SUMMARY_1 ACCESSEDSTORAGE_CELL ORIG_STORAGE_CELL STORAGE_CELL _Val39 _Val40 GAS_CELL ID_CELL PC_CELL REFUND_CELL W0 W1 _Val1 _Val10 _Val11 _Val13 _Val2 _Val21 _Val22 _Val23 _Val24 _Val25 _Val27 _Val28 _Val29 _Val3 _Val30 _Val31 _Val32 _Val33 _Val6 _Val7 _Val8 _Val9 K_CELL SCHEDULE_CELL USEGAS_CELL _Val0 _Val12 _Val14 _Val15 _Val16 _Val17 _Val18 _Val26 _Val4 _Val5 WS _DotVar0 _DotVar6 _Val19 _Val20 _Val41 _Val42 _Gen0 _Gen1 _Gen10 _Gen11 _Gen12 _Gen13 _Gen14 _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2 _Gen20 _Gen21 _Gen22 _Gen23 _Gen24 _Gen25 _Gen26 _Gen27 _Gen28 _Gen29 _Gen3 _Gen30 _Gen31 _Gen32 _Gen33 _Gen34 _Gen35 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 _Gen9 _Val34 _Val36 _Val37 _Val38 _Val35)
  all_goals assumption

theorem sstore_prestate_equiv
  {ACCESSEDSTORAGE_CELL : SortMap}
  {GAS_CELL ID_CELL PC_CELL REFUND_CELL W0 W1 : SortInt}
  {K_CELL : SortK}
  {SCHEDULE_CELL : SortSchedule}
  {USEGAS_CELL : SortBool}
  {WS : SortWordStack}
  {_DotVar0 : SortGeneratedCounterCell}
  {_DotVar6 _Val20 : SortAccountCellMap}
  {_Gen0 : SortProgramCell}
  {_Gen1 : SortJumpDestsCell}
  {_Gen10 : SortLogCell}
  {_Gen11 : SortAccessedAccountsCell}
  {_Gen12 : SortCreatedAccountsCell}
  {_Gen13 : SortOutputCell}
  {_Gen14 : SortStatusCodeCell}
  {_Gen15 : SortCallStackCell}
  {_Gen16 : SortInterimStatesCell}
  {_Gen17 : SortTouchedAccountsCell}
  {_Gen18 : SortVersionedHashesCell}
  {_Gen19 : SortGasPriceCell}
  {_Gen2 : SortCallerCell}
  {_Gen20 : SortOriginCell}
  {_Gen21 : SortBlockhashesCell}
  {_Gen22 : SortBlockCell}
  {_Gen23 : SortBalanceCell}
  {_Gen24 : SortCodeCell}
  {_Gen25 : SortTransientStorageCell}
  {_Gen26 : SortNonceCell}
  {_Gen27 : SortChainIDCell}
  {_Gen28 : SortTxOrderCell}
  {_Gen29 : SortTxPendingCell}
  {_Gen3 : SortCallDataCell}
  {_Gen30 : SortMessagesCell}
  {_Gen31 : SortWithdrawalsPendingCell}
  {_Gen32 : SortWithdrawalsOrderCell}
  {_Gen33 : SortWithdrawalsCell}
  {_Gen34 : SortExitCodeCell}
  {_Gen35 : SortModeCell}
  {_Gen4 : SortCallValueCell}
  {_Gen5 : SortLocalMemCell}
  {_Gen6 : SortMemoryUsedCell}
  {_Gen7 : SortCallGasCell}
  {_Gen8 : SortCallDepthCell}
  {_Gen9 : SortSelfDestructCell}
  (symState : EVM.State):
  let lhs := @sstoreLHS ACCESSEDSTORAGE_CELL GAS_CELL ID_CELL PC_CELL REFUND_CELL W0 W1 K_CELL SCHEDULE_CELL USEGAS_CELL WS _DotVar0 _DotVar6 _Val20 _Gen0 _Gen1 _Gen10 _Gen11 _Gen12 _Gen13 _Gen14 _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2 _Gen20 _Gen21 _Gen22 _Gen23 _Gen24 _Gen25 _Gen26 _Gen27 _Gen28 _Gen29 _Gen3 _Gen30 _Gen31 _Gen32 _Gen33 _Gen34 _Gen35 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 _Gen9
  stateMap symState lhs =
  {symState with
    stack := (intMap W0) :: (intMap W1) :: wordStackMap WS
    pc := intMap PC_CELL
    gasAvailable := intMap GAS_CELL
    executionEnv := {symState.executionEnv with
                  code := _Gen0.val,
                  codeOwner := accountAddressMap ((@inj SortInt SortAccount) ID_CELL)
                  perm := true},
    substate := {symState.substate with
            accessedStorageKeys :=  Axioms.SortAccessedStorageCellMap (SortGeneratedTopCell.accessedStorage lhs)
            refundBalance := intMap REFUND_CELL
           }
    returnData := _Gen13.val
    accountMap := Axioms.SortAccountsCellMap lhs.accounts
    } := by rfl

-- Behavior of `Csstore`
def Csstore_compute (value stor_val ostor_val : SortInt) : SortInt :=
  if stor_val = value ∨ ¬ostor_val = stor_val then 100 else
  if ostor_val = 0 then 20000 else 2900

@[simp]
theorem Csstore_def {value stor_val ostor_val : SortInt}:
  Csstore SortSchedule.CANCUN_EVM value stor_val ostor_val =
  some (Csstore_compute value stor_val ostor_val) := by
  unfold Csstore GAS_FEES_Csstore_new
  simp [Option.bind, IntEq_def, IntNEq_def, orBool_def]; rfl

/--
Remaining gas after deducting to `gas` the cost of executing `sstore`
- `map` will be the accessed storage map
- `value` is the stored value
- `stor_val` is the current value in storage
- `ostor_val` is the value from the origin storage
- `acc` is the account in question
- `key` is where the value will be stored

The addition is because this whole expression is to be deducted from the
current gas available
 -/
noncomputable def sstore_gas (map : SortMap) (value stor_val ostor_val acc key: SortInt) : SortInt :=
  (Csstore_compute value stor_val ostor_val) + ite (inStorage_compute map acc key) 0 2100

theorem sstore_gas_pos (map : SortMap) (value stor_val ostor_val acc key: SortInt) :
  0 < sstore_gas map value stor_val ostor_val acc key := by
  aesop (add simp [sstore_gas, Csstore_compute])

/--
Computational content of `GAS_FEES_Rsstore_new`
The function is named `rsstore` instead of `rsstore_new` because if the
schedule is Cancun, `Rsstore` equates to this function
-/
def rsstore (new current original: SortInt) : SortInt :=
  (if (¬current = new ∧ original = current) ∧ new = 0 then 4800
  else
    (if (¬current = new ∧ ¬original = current) ∧ ¬original = 0 then
        if current = 0 then -4800 else if new = 0 then 4800 else 0
      else 0) +
      if ¬current = new ∧ original = new then (if original = 0 then 20000 else 2900) - 100 else 0)

theorem rsstore_new_def {new current original} {sched} (h : sched = .CANCUN_EVM) :
  GAS_FEES_Rsstore_new sched new current original = some (rsstore new current original) := by
  unfold GAS_FEES_Rsstore_new rsstore; split; subst h
  simp [Option.bind, IntEq_def, IntNEq_def, andBool_def, «_-Int_», «_+Int_»]

/--
`Rsstore` is `GAS_FEES_Rsstore_new` when schedule is `.CANCUN_EVM`
 -/
theorem rsstore_def {new current original} {sched} (h : sched = .CANCUN_EVM) :
  Rsstore sched new current original = some (rsstore new current original) := by
  unfold Rsstore GAS_FEES_Rsstore_new rsstore; split; subst h
  simp [Option.bind, IntEq_def, IntNEq_def, andBool_def, «_-Int_», «_+Int_»]

section Aᵣ_equivalence
variable (gas gasCost : ℕ)
variable (symStack : Stack UInt256)
variable (symPc symGasAvailable symRefund key value : UInt256)
variable (symExecLength : ℕ)
variable (symReturnData symCode : ByteArray)
variable (symAccessedStorageKeys : Batteries.RBSet (AccountAddress × UInt256) Substate.storageKeysCmp)
variable (symAccounts : AccountMap)
variable (symCodeOwner : AccountAddress)

attribute [local simp] State.lookupAccount
attribute [local simp] GasConstants.Rsclear
attribute [local simp] GasConstants.Gsreset
attribute [local simp] GasConstants.Gwarmaccess
attribute [local simp] GasConstants.Gsset

theorem Aᵣ_rsstore_eq {new /- current original -/} /- {sched} -/ {symState: EvmYul.State} /- (h : sched = .CANCUN_EVM) -/
  -- Hypothesis linking `Aᵣ` and `rsstore`
  /- (current_link : (symState.accountMap.find! symCodeOwner).storage.findD key ⟨0⟩ = intMap current)
  (original_link : (symState.σ₀.find! symCodeOwner).storage.findD key ⟨0⟩ = intMap original) -/
  (owner_exists : ¬Batteries.RBMap.find? symAccounts symCodeOwner = none):
  let ss := {symState with
             executionEnv := {symState.executionEnv with
                  code := symCode,
                  codeOwner := symCodeOwner},
              accountMap := symAccounts,
             substate := {symState.substate with
                          accessedStorageKeys := symAccessedStorageKeys
                          refundBalance := symRefund}
              }
  Aᵣ_sstore {ss with
             accountMap := accountMap_sstore ss key (intMap new),
             substate.accessedStorageKeys := accessedStorageKeys_sstore symState key,
             substate.refundBalance := Aᵣ_sstore ss key (intMap new)} key (intMap new) = symRefund +
             intMap (rsstore new (Int.ofNat ((symState.accountMap.find! symCodeOwner).storage.findD key ⟨0⟩).val.val) (Int.ofNat ((symState.σ₀.find! symCodeOwner).storage.findD key ⟨0⟩).val.val)) := by sorry
-- Commented to speed up
/-   simp [Aᵣ_sstore, rsstore]
  split <;> split <;> try split <;> simp_all [State.lookupAccount] <;> aesop
  . simp_all [Batteries.RBMap.find?_insert]
    rename_i _ _ _ h _; split at h <;> simp_all
  . rename_i n h; revert h
    split <;> split <;> split
    . aesop (add simp [UInt256.ofNat_toSigned])
    . aesop (add simp [UInt256.ofNat_toSigned])
    . aesop (add simp [UInt256.ofNat_toSigned])
    . aesop (add simp [UInt256.ofNat_toSigned])
    · sorry
    · aesop (add simp [UInt256.ofNat_toSigned])
    · sorry
    · sorry
  . sorry -/

end Aᵣ_equivalence


theorem sstore_poststate_equiv
  {ACCESSEDSTORAGE_CELL /- STORAGE_CELL ORIG_STORAGE_CELL -/ _Val39 _Val40 : SortMap}
  {GAS_CELL ID_CELL PC_CELL REFUND_CELL W0 W1 _Val1 _Val10 _Val11 _Val13 _Val2 _Val21 _Val22 _Val23 _Val24 _Val25 _Val27 _Val28 _Val29 _Val3 _Val30 _Val31 _Val32 _Val33 _Val6 _Val7 _Val8 _Val9 : SortInt}
  {K_CELL : SortK}
  {SCHEDULE_CELL : SortSchedule}
  {_Val0 _Val12 _Val14 _Val15 _Val16 _Val17 _Val18 _Val26 _Val4 _Val5 : SortBool}
  {WS : SortWordStack}
  {_DotVar0 : SortGeneratedCounterCell}
  {_DotVar6 _Val19 _Val20 _Val41 _Val42 : SortAccountCellMap}
  {_Gen0 : SortProgramCell}
  {_Gen1 : SortJumpDestsCell}
  {_Gen10 : SortLogCell}
  {_Gen11 : SortAccessedAccountsCell}
  {_Gen12 : SortCreatedAccountsCell}
  {_Gen13 : SortOutputCell}
  {_Gen14 : SortStatusCodeCell}
  {_Gen15 : SortCallStackCell}
  {_Gen16 : SortInterimStatesCell}
  {_Gen17 : SortTouchedAccountsCell}
  {_Gen18 : SortVersionedHashesCell}
  {_Gen19 : SortGasPriceCell}
  {_Gen2 : SortCallerCell}
  {_Gen20 : SortOriginCell}
  {_Gen21 : SortBlockhashesCell}
  {_Gen22 : SortBlockCell}
  {_Gen23 : SortBalanceCell}
  {_Gen24 : SortCodeCell}
  {_Gen25 : SortTransientStorageCell}
  {_Gen26 : SortNonceCell}
  {_Gen27 : SortChainIDCell}
  {_Gen28 : SortTxOrderCell}
  {_Gen29 : SortTxPendingCell}
  {_Gen3 : SortCallDataCell}
  {_Gen30 : SortMessagesCell}
  {_Gen31 : SortWithdrawalsPendingCell}
  {_Gen32 : SortWithdrawalsOrderCell}
  {_Gen33 : SortWithdrawalsCell}
  {_Gen34 : SortExitCodeCell}
  {_Gen35 : SortModeCell}
  {_Gen4 : SortCallValueCell}
  {_Gen5 : SortLocalMemCell}
  {_Gen6 : SortMemoryUsedCell}
  {_Gen7 : SortCallGasCell}
  {_Gen8 : SortCallDepthCell}
  {_Gen9 : SortSelfDestructCell}
  {_Val34 _Val36 _Val37 _Val38 : SortSet}
  {_Val35 : SortKItem}
  (defn_Val21 : «_+Int_» PC_CELL 1 = some _Val21)
  /- (defn_Val22 : lookup STORAGE_CELL W0 = some _Val22)
  (defn_Val23 : lookup ORIG_STORAGE_CELL W0 = some _Val23) -/
  (defn_Val24 : Csstore SCHEDULE_CELL W1 _Val22 _Val23 = some _Val24)
  (defn_Val25 : «_-Int_» GAS_CELL _Val24 = some _Val25)
  (defn_Val26 : «#inStorage» ACCESSEDSTORAGE_CELL ((@inj SortInt SortAccount) ID_CELL) W0 = some _Val26)
  (defn_Val27 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gcoldsload_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val27)
  (defn_Val28 : kite _Val26 0 _Val27 = some _Val28)
  (defn_Val29 : «_-Int_» _Val25 _Val28 = some _Val29)
  (defn_Val33 : «_+Int_» REFUND_CELL _Val32 = some _Val33)
  (cancun : SCHEDULE_CELL = .CANCUN_EVM)
  (symState : EVM.State) :
  let rhs := @sstoreRHS  _Val39 _Val40  ID_CELL _Val1 _Val10 _Val11 _Val13 _Val2 _Val21 _Val22 _Val23 _Val24 _Val25 _Val27 _Val28 _Val29 _Val3 _Val30 _Val31 _Val32 _Val33 _Val6 _Val7 _Val8 _Val9 K_CELL SCHEDULE_CELL _Val0 _Val12 _Val14 _Val15 _Val16 _Val17 _Val18 _Val26 _Val4 _Val5 WS _DotVar0 _DotVar6 _Val19 _Val20 _Val41 _Val42 _Gen0 _Gen1 _Gen10 _Gen11 _Gen12 _Gen13 _Gen14 _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2 _Gen20 _Gen21 _Gen22 _Gen23 _Gen24 _Gen25 _Gen26 _Gen27 _Gen28 _Gen29 _Gen3 _Gen30 _Gen31 _Gen32 _Gen33 _Gen34 _Gen35 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 _Gen9 _Val34 _Val36 _Val37 _Val38 _Val35
  stateMap symState rhs =
  {symState with
    stack := wordStackMap WS
    pc := intMap («_+Int'_» PC_CELL 1)
    gasAvailable := intMap (GAS_CELL - sstore_gas ACCESSEDSTORAGE_CELL W1 _Val22 _Val23 ID_CELL W0)
    executionEnv := {symState.executionEnv with
                  code := _Gen0.val,
                  codeOwner := accountAddressMap ((@inj SortInt SortAccount) ID_CELL)
                  perm := true},
    accountMap := Axioms.SortAccountsCellMap rhs.accounts
    substate := {symState.substate with
            accessedStorageKeys :=  Axioms.SortAccessedStorageCellMap  rhs.accessedStorage
            -- TODO: Replace `_Val32` with a more explicit computation
            -- such as `rsstore` above
            refundBalance := intMap («_+Int'_» REFUND_CELL _Val32)
           }
    returnData := _Gen13.val
  } := by
  simp_all [sstoreRHS, stateMap, «_-Int_», plusInt_def, «_+Int_», ←inj_ID_CELL]
  congr
  aesop (add simp [inj, Inj.inj, sstore_gas]) (add safe (by linarith))

theorem step_sstore_equiv
  {ACCESSEDSTORAGE_CELL ORIG_STORAGE_CELL STORAGE_CELL _Val39 _Val40 : SortMap}
  {GAS_CELL ID_CELL PC_CELL REFUND_CELL W0 W1 _Val1 _Val10 _Val11 _Val13 _Val2 _Val21 _Val22 _Val23 _Val24 _Val25 _Val27 _Val28 _Val29 _Val3 _Val30 _Val31 _Val32 _Val33 _Val6 _Val7 _Val8 _Val9 : SortInt}
  {K_CELL : SortK}
  {SCHEDULE_CELL : SortSchedule}
  {USEGAS_CELL _Val0 _Val12 _Val14 _Val15 _Val16 _Val17 _Val18 _Val26 _Val4 _Val5 : SortBool}
  {WS : SortWordStack}
  {_DotVar0 : SortGeneratedCounterCell}
  {_DotVar6 _Val19 _Val20 _Val41 _Val42 : SortAccountCellMap}
  {_Gen0 : SortProgramCell}
  {_Gen1 : SortJumpDestsCell}
  {_Gen10 : SortLogCell}
  {_Gen11 : SortAccessedAccountsCell}
  {_Gen12 : SortCreatedAccountsCell}
  {_Gen13 : SortOutputCell}
  {_Gen14 : SortStatusCodeCell}
  {_Gen15 : SortCallStackCell}
  {_Gen16 : SortInterimStatesCell}
  {_Gen17 : SortTouchedAccountsCell}
  {_Gen18 : SortVersionedHashesCell}
  {_Gen19 : SortGasPriceCell}
  {_Gen2 : SortCallerCell}
  {_Gen20 : SortOriginCell}
  {_Gen21 : SortBlockhashesCell}
  {_Gen22 : SortBlockCell}
  {_Gen23 : SortBalanceCell}
  {_Gen24 : SortCodeCell}
  {_Gen25 : SortTransientStorageCell}
  {_Gen26 : SortNonceCell}
  {_Gen27 : SortChainIDCell}
  {_Gen28 : SortTxOrderCell}
  {_Gen29 : SortTxPendingCell}
  {_Gen3 : SortCallDataCell}
  {_Gen30 : SortMessagesCell}
  {_Gen31 : SortWithdrawalsPendingCell}
  {_Gen32 : SortWithdrawalsOrderCell}
  {_Gen33 : SortWithdrawalsCell}
  {_Gen34 : SortExitCodeCell}
  {_Gen35 : SortModeCell}
  {_Gen4 : SortCallValueCell}
  {_Gen5 : SortLocalMemCell}
  {_Gen6 : SortMemoryUsedCell}
  {_Gen7 : SortCallGasCell}
  {_Gen8 : SortCallDepthCell}
  {_Gen9 : SortSelfDestructCell}
  {_Val34 _Val36 _Val37 _Val38 : SortSet}
  {_Val35 : SortKItem}
  (defn_Val0 : «_<<_>>_SCHEDULE_Bool_ScheduleFlag_Schedule» SortScheduleFlag.Ghasaccesslist_SCHEDULE_ScheduleFlag SCHEDULE_CELL = some _Val0)
  (defn_Val1 : lookup STORAGE_CELL W0 = some _Val1)
  (defn_Val2 : lookup ORIG_STORAGE_CELL W0 = some _Val2)
  (defn_Val3 : Csstore SCHEDULE_CELL W1 _Val1 _Val2 = some _Val3)
  (defn_Val4 : «_<=Int_» _Val3 GAS_CELL = some _Val4)
  (defn_Val5 : «#inStorage» ACCESSEDSTORAGE_CELL ((@inj SortInt SortAccount) ID_CELL) W0 = some _Val5)
  (defn_Val6 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gcoldsload_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val6)
  (defn_Val7 : kite _Val5 0 _Val6 = some _Val7)
  (defn_Val8 : lookup STORAGE_CELL W0 = some _Val8)
  (defn_Val9 : lookup ORIG_STORAGE_CELL W0 = some _Val9)
  (defn_Val10 : Csstore SCHEDULE_CELL W1 _Val8 _Val9 = some _Val10)
  (defn_Val11 : «_-Int_» GAS_CELL _Val10 = some _Val11)
  (defn_Val12 : «_<=Int_» _Val7 _Val11 = some _Val12)
  (defn_Val13 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gcallstipend_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val13)
  (defn_Val14 : «_<Int_» _Val13 GAS_CELL = some _Val14)
  (defn_Val15 : _andBool_ _Val12 _Val14 = some _Val15)
  (defn_Val16 : _andBool_ _Val4 _Val15 = some _Val16)
  (defn_Val17 : _andBool_ _Val0 _Val16 = some _Val17)
  (defn_Val18 : _andBool_ USEGAS_CELL _Val17 = some _Val18)
  (defn_Val19 : AccountCellMapItem { val := ID_CELL } {
    acctID := { val := ID_CELL },
    balance := _Gen23,
    code := _Gen24,
    storage := { val := STORAGE_CELL },
    origStorage := { val := ORIG_STORAGE_CELL },
    transientStorage := _Gen25,
    nonce := _Gen26 } = some _Val19)
  (defn_Val20 : _AccountCellMap_ _Val19 _DotVar6 = some _Val20)
  (defn_Val21 : «_+Int_» PC_CELL 1 = some _Val21)
  (defn_Val22 : lookup STORAGE_CELL W0 = some _Val22)
  (defn_Val23 : lookup ORIG_STORAGE_CELL W0 = some _Val23)
  (defn_Val24 : Csstore SCHEDULE_CELL W1 _Val22 _Val23 = some _Val24)
  (defn_Val25 : «_-Int_» GAS_CELL _Val24 = some _Val25)
  (defn_Val26 : «#inStorage» ACCESSEDSTORAGE_CELL ((@inj SortInt SortAccount) ID_CELL) W0 = some _Val26)
  (defn_Val27 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gcoldsload_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val27)
  (defn_Val28 : kite _Val26 0 _Val27 = some _Val28)
  (defn_Val29 : «_-Int_» _Val25 _Val28 = some _Val29)
  (defn_Val30 : lookup STORAGE_CELL W0 = some _Val30)
  (defn_Val31 : lookup ORIG_STORAGE_CELL W0 = some _Val31)
  (defn_Val32 : Rsstore SCHEDULE_CELL W1 _Val30 _Val31 = some _Val32)
  (defn_Val33 : «_+Int_» REFUND_CELL _Val32 = some _Val33)
  (defn_Val34 : «.Set» = some _Val34)
  (defn_Val35 : «Map:lookupOrDefault» ACCESSEDSTORAGE_CELL ((@inj SortInt SortKItem) ID_CELL) ((@inj SortSet SortKItem) _Val34) = some _Val35)
  (defn_Val36 : «project:Set» (SortK.kseq _Val35 SortK.dotk) = some _Val36)
  (defn_Val37 : SetItem ((@inj SortInt SortKItem) W0) = some _Val37)
  (defn_Val38 : «_|Set__SET_Set_Set_Set» _Val36 _Val37 = some _Val38)
  (defn_Val39 : «Map:update» ACCESSEDSTORAGE_CELL ((@inj SortInt SortKItem) ID_CELL) ((@inj SortSet SortKItem) _Val38) = some _Val39)
  (defn_Val40 : «Map:update» STORAGE_CELL ((@inj SortInt SortKItem) W0) ((@inj SortInt SortKItem) W1) = some _Val40)
  (defn_Val41 : AccountCellMapItem { val := ID_CELL } {
    acctID := { val := ID_CELL },
    balance := _Gen23,
    code := _Gen24,
    storage := { val := _Val40 },
    origStorage := { val := ORIG_STORAGE_CELL },
    transientStorage := _Gen25,
    nonce := _Gen26 } = some _Val41)
  (defn_Val42 : _AccountCellMap_ _Val41 _DotVar6 = some _Val42)
  (req : _Val18 = true)
  (symState : EVM.State)
  -- needed for EVM.step
  (gasCost : ℕ)
  -- Necessary assumptions for equivalence
  (cancun : SCHEDULE_CELL = .CANCUN_EVM)
  (gavailEnough : sstore_gas ACCESSEDSTORAGE_CELL W1 _Val22 _Val23 ID_CELL W0 ≤ GAS_CELL)
  (gavailSmall : GAS_CELL < ↑UInt256.size)
  (gasCostValue : gasCost = sstore_gas ACCESSEDSTORAGE_CELL W1 _Val22 _Val23 ID_CELL W0)
  (pcountSmall : PC_CELL + 1 < UInt256.size)
  (pcountNonneg : 0 ≤ PC_CELL)
  (W0ge0 : 0 ≤ W0)
  (W1ge0 : 0 ≤ W1)
  (ID_CELLSize : Int.toNat ID_CELL < AccountAddress.size):
  EVM.step_sstore (Int.toNat GAS_CELL) gasCost (stateMap symState (@sstoreLHS ACCESSEDSTORAGE_CELL GAS_CELL ID_CELL PC_CELL REFUND_CELL W0 W1 K_CELL SCHEDULE_CELL USEGAS_CELL WS _DotVar0 _DotVar6 _Val20 _Gen0 _Gen1 _Gen10 _Gen11 _Gen12 _Gen13 _Gen14 _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2 _Gen20 _Gen21 _Gen22 _Gen23 _Gen24 _Gen25 _Gen26 _Gen27 _Gen28 _Gen29 _Gen3 _Gen30 _Gen31 _Gen32 _Gen33 _Gen34 _Gen35 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 _Gen9)) =
  .ok (stateMap {symState with execLength := symState.execLength + 1} (@sstoreRHS  _Val39 _Val40  ID_CELL _Val1 _Val10 _Val11 _Val13 _Val2 _Val21 _Val22 _Val23 _Val24 _Val25 _Val27 _Val28 _Val29 _Val3 _Val30 _Val31 _Val32 _Val33 _Val6 _Val7 _Val8 _Val9 K_CELL SCHEDULE_CELL _Val0 _Val12 _Val14 _Val15 _Val16 _Val17 _Val18 _Val26 _Val4 _Val5 WS _DotVar0 _DotVar6 _Val19 _Val20 _Val41 _Val42 _Gen0 _Gen1 _Gen10 _Gen11 _Gen12 _Gen13 _Gen14 _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2 _Gen20 _Gen21 _Gen22 _Gen23 _Gen24 _Gen25 _Gen26 _Gen27 _Gen28 _Gen29 _Gen3 _Gen30 _Gen31 _Gen32 _Gen33 _Gen34 _Gen35 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 _Gen9 _Val34 _Val36 _Val37 _Val38 _Val35)) := by
  let acc : SortAccountCell := {
          acctID := { val := ID_CELL },
          balance := _Gen23,
          code := _Gen24,
          storage := { val := STORAGE_CELL },
          origStorage := { val := ORIG_STORAGE_CELL },
          transientStorage := _Gen25,
          nonce := _Gen26 }
  cases cg: (Int.toNat GAS_CELL)
  next =>
    have fls := sstore_gas_pos ACCESSEDSTORAGE_CELL W1 _Val22 _Val23 ID_CELL W0
    have _ := Int.lt_of_lt_of_le fls gavailEnough
    omega
  rw [sstore_prestate_equiv, EVM.step_sstore_summary] <;> try assumption
  rw [sstoreLHS, sstore_poststate_equiv, sstoreRHS] <;> try congr
  . simp only [accountMap_sstore, Aᵣ_sstore, State.lookupAccount]
    simp only [SortGeneratedTopCell.accounts, accountAddressMap, inj_ID_CELL]
    simp [(Axioms.accountsCell_map_find? acc (by eq_refl) defn_Val19 defn_Val20)]
    exact (Axioms.accountsCell_map_insert defn_Val34 defn_Val35 defn_Val36 defn_Val37
    defn_Val38 defn_Val40 defn_Val41 defn_Val42 defn_Val19 defn_Val20)
  . simp [State.lookupAccount]
    split
    . rename_i _ _ owner
      rw [(Axioms.accountsCell_map_find? acc)] at owner <;> first | contradiction | congr
    . constructor
      . /- Refund Cell -/
        sorry
      . rename_i _ ownerAcc findOwner
        exact (Axioms.accessedStorageCell_map_insert defn_Val34 defn_Val35
        defn_Val36 defn_Val37 defn_Val38 defn_Val39)
  . rw [(UInt256.ofNat_toSigned gasCostValue), sstore_gas] at *
    rw [cancun, Csstore_def, Option.some.injEq] at defn_Val10 defn_Val3
    aesop (add safe (by rw [intMap_sub_dist])) (add simp [Csstore_compute])
  . rw [plusInt_def, ←UInt256.add_succ_mod_size, intMap_add_dist] <;> aesop
  . aesop (add simp [ltInt_def, andBool_def]) (add safe (by linarith))

theorem X_sstore_equiv
  {ACCESSEDSTORAGE_CELL ORIG_STORAGE_CELL STORAGE_CELL _Val39 _Val40 : SortMap}
  {GAS_CELL ID_CELL PC_CELL REFUND_CELL W0 W1 _Val1 _Val10 _Val11 _Val13 _Val2 _Val21 _Val22 _Val23 _Val24 _Val25 _Val27 _Val28 _Val29 _Val3 _Val30 _Val31 _Val32 _Val33 _Val6 _Val7 _Val8 _Val9 : SortInt}
  {K_CELL : SortK}
  {SCHEDULE_CELL : SortSchedule}
  {USEGAS_CELL _Val0 _Val12 _Val14 _Val15 _Val16 _Val17 _Val18 _Val26 _Val4 _Val5 : SortBool}
  {WS : SortWordStack}
  {_DotVar0 : SortGeneratedCounterCell}
  {_DotVar6 _Val19 _Val20 _Val41 _Val42 : SortAccountCellMap}
  {_Gen0 : SortProgramCell}
  {_Gen1 : SortJumpDestsCell}
  {_Gen10 : SortLogCell}
  {_Gen11 : SortAccessedAccountsCell}
  {_Gen12 : SortCreatedAccountsCell}
  {_Gen13 : SortOutputCell}
  {_Gen14 : SortStatusCodeCell}
  {_Gen15 : SortCallStackCell}
  {_Gen16 : SortInterimStatesCell}
  {_Gen17 : SortTouchedAccountsCell}
  {_Gen18 : SortVersionedHashesCell}
  {_Gen19 : SortGasPriceCell}
  {_Gen2 : SortCallerCell}
  {_Gen20 : SortOriginCell}
  {_Gen21 : SortBlockhashesCell}
  {_Gen22 : SortBlockCell}
  {_Gen23 : SortBalanceCell}
  {_Gen24 : SortCodeCell}
  {_Gen25 : SortTransientStorageCell}
  {_Gen26 : SortNonceCell}
  {_Gen27 : SortChainIDCell}
  {_Gen28 : SortTxOrderCell}
  {_Gen29 : SortTxPendingCell}
  {_Gen3 : SortCallDataCell}
  {_Gen30 : SortMessagesCell}
  {_Gen31 : SortWithdrawalsPendingCell}
  {_Gen32 : SortWithdrawalsOrderCell}
  {_Gen33 : SortWithdrawalsCell}
  {_Gen34 : SortExitCodeCell}
  {_Gen35 : SortModeCell}
  {_Gen4 : SortCallValueCell}
  {_Gen5 : SortLocalMemCell}
  {_Gen6 : SortMemoryUsedCell}
  {_Gen7 : SortCallGasCell}
  {_Gen8 : SortCallDepthCell}
  {_Gen9 : SortSelfDestructCell}
  {_Val34 _Val36 _Val37 _Val38 : SortSet}
  {_Val35 : SortKItem}
  (defn_Val0 : «_<<_>>_SCHEDULE_Bool_ScheduleFlag_Schedule» SortScheduleFlag.Ghasaccesslist_SCHEDULE_ScheduleFlag SCHEDULE_CELL = some _Val0)
  (defn_Val1 : lookup STORAGE_CELL W0 = some _Val1)
  (defn_Val2 : lookup ORIG_STORAGE_CELL W0 = some _Val2)
  (defn_Val3 : Csstore SCHEDULE_CELL W1 _Val1 _Val2 = some _Val3)
  (defn_Val4 : «_<=Int_» _Val3 GAS_CELL = some _Val4)
  (defn_Val5 : «#inStorage» ACCESSEDSTORAGE_CELL ((@inj SortInt SortAccount) ID_CELL) W0 = some _Val5)
  (defn_Val6 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gcoldsload_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val6)
  (defn_Val7 : kite _Val5 0 _Val6 = some _Val7)
  (defn_Val8 : lookup STORAGE_CELL W0 = some _Val8)
  (defn_Val9 : lookup ORIG_STORAGE_CELL W0 = some _Val9)
  (defn_Val10 : Csstore SCHEDULE_CELL W1 _Val8 _Val9 = some _Val10)
  (defn_Val11 : «_-Int_» GAS_CELL _Val10 = some _Val11)
  (defn_Val12 : «_<=Int_» _Val7 _Val11 = some _Val12)
  (defn_Val13 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gcallstipend_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val13)
  (defn_Val14 : «_<Int_» _Val13 GAS_CELL = some _Val14)
  (defn_Val15 : _andBool_ _Val12 _Val14 = some _Val15)
  (defn_Val16 : _andBool_ _Val4 _Val15 = some _Val16)
  (defn_Val17 : _andBool_ _Val0 _Val16 = some _Val17)
  (defn_Val18 : _andBool_ USEGAS_CELL _Val17 = some _Val18)
  (defn_Val19 : AccountCellMapItem { val := ID_CELL } {
    acctID := { val := ID_CELL },
    balance := _Gen23,
    code := _Gen24,
    storage := { val := STORAGE_CELL },
    origStorage := { val := ORIG_STORAGE_CELL },
    transientStorage := _Gen25,
    nonce := _Gen26 } = some _Val19)
  (defn_Val20 : _AccountCellMap_ _Val19 _DotVar6 = some _Val20)
  (defn_Val21 : «_+Int_» PC_CELL 1 = some _Val21)
  (defn_Val22 : lookup STORAGE_CELL W0 = some _Val22)
  (defn_Val23 : lookup ORIG_STORAGE_CELL W0 = some _Val23)
  (defn_Val24 : Csstore SCHEDULE_CELL W1 _Val22 _Val23 = some _Val24)
  (defn_Val25 : «_-Int_» GAS_CELL _Val24 = some _Val25)
  (defn_Val26 : «#inStorage» ACCESSEDSTORAGE_CELL ((@inj SortInt SortAccount) ID_CELL) W0 = some _Val26)
  (defn_Val27 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gcoldsload_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val27)
  (defn_Val28 : kite _Val26 0 _Val27 = some _Val28)
  (defn_Val29 : «_-Int_» _Val25 _Val28 = some _Val29)
  (defn_Val30 : lookup STORAGE_CELL W0 = some _Val30)
  (defn_Val31 : lookup ORIG_STORAGE_CELL W0 = some _Val31)
  (defn_Val32 : Rsstore SCHEDULE_CELL W1 _Val30 _Val31 = some _Val32)
  (defn_Val33 : «_+Int_» REFUND_CELL _Val32 = some _Val33)
  (defn_Val34 : «.Set» = some _Val34)
  (defn_Val35 : «Map:lookupOrDefault» ACCESSEDSTORAGE_CELL ((@inj SortInt SortKItem) ID_CELL) ((@inj SortSet SortKItem) _Val34) = some _Val35)
  (defn_Val36 : «project:Set» (SortK.kseq _Val35 SortK.dotk) = some _Val36)
  (defn_Val37 : SetItem ((@inj SortInt SortKItem) W0) = some _Val37)
  (defn_Val38 : «_|Set__SET_Set_Set_Set» _Val36 _Val37 = some _Val38)
  (defn_Val39 : «Map:update» ACCESSEDSTORAGE_CELL ((@inj SortInt SortKItem) ID_CELL) ((@inj SortSet SortKItem) _Val38) = some _Val39)
  (defn_Val40 : «Map:update» STORAGE_CELL ((@inj SortInt SortKItem) W0) ((@inj SortInt SortKItem) W1) = some _Val40)
  (defn_Val41 : AccountCellMapItem { val := ID_CELL } {
    acctID := { val := ID_CELL },
    balance := _Gen23,
    code := _Gen24,
    storage := { val := _Val40 },
    origStorage := { val := ORIG_STORAGE_CELL },
    transientStorage := _Gen25,
    nonce := _Gen26 } = some _Val41)
  (defn_Val42 : _AccountCellMap_ _Val41 _DotVar6 = some _Val42)
  (req : _Val18 = true)
  (symState : EVM.State)
  -- Necessary assumptions for equivalence
  (cancun : SCHEDULE_CELL = .CANCUN_EVM)
  (gavailEnough : sstore_gas ACCESSEDSTORAGE_CELL W1 _Val22 _Val23 ID_CELL W0 ≤ GAS_CELL)
  (gavailSmall : GAS_CELL < ↑UInt256.size)
  /- (gasCostValue : gasCost = sstore_gas ACCESSEDSTORAGE_CELL W1 _Val22 _Val23 ID_CELL W0) -/
  (codeSstoreLHS : _Gen0 = ⟨⟨#[(0x55 : UInt8)]⟩⟩)
  (codeSstoreRHS : _Gen24 = ⟨⟨⟨#[(0x55 : UInt8)]⟩⟩⟩)
  (pcZero : PC_CELL = 0)
  (key_pos : 0 ≤ W0)
  (val_pos : 0 ≤ W1)
  (ID_CELLSize : Int.toNat ID_CELL < AccountAddress.size)
  -- TODO: Replace with a native measure for `SortWordStack` and
  -- prove this assumption via an equality theorem stating that
  -- `List.length (wordStackMap WS) = wordStackLength WS`
  (stackOk: List.length (wordStackMap WS) < 1024)
  -- This hypothesis is needed in order to have a successful run of `EVM.X`:
  (callStipendGas : GasConstants.Gcallstipend < (intMap GAS_CELL).toNat)
  :
  EVM.X false (UInt256.toNat (intMap GAS_CELL)) (stateMap symState (@sstoreLHS ACCESSEDSTORAGE_CELL GAS_CELL ID_CELL PC_CELL REFUND_CELL W0 W1 K_CELL SCHEDULE_CELL USEGAS_CELL WS _DotVar0 _DotVar6 _Val20 _Gen0 _Gen1 _Gen10 _Gen11 _Gen12 _Gen13 _Gen14 _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2 _Gen20 _Gen21 _Gen22 _Gen23 _Gen24 _Gen25 _Gen26 _Gen27 _Gen28 _Gen29 _Gen3 _Gen30 _Gen31 _Gen32 _Gen33 _Gen34 _Gen35 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 _Gen9)) =
  .ok (.success (stateMap {symState with execLength := symState.execLength + 2} (@sstoreRHS  _Val39 _Val40  ID_CELL _Val1 _Val10 _Val11 _Val13 _Val2 _Val21 _Val22 _Val23 _Val24 _Val25 _Val27 _Val28 _Val29 _Val3 _Val30 _Val31 _Val32 _Val33 _Val6 _Val7 _Val8 _Val9 K_CELL SCHEDULE_CELL _Val0 _Val12 _Val14 _Val15 _Val16 _Val17 _Val18 _Val26 _Val4 _Val5 WS _DotVar0 _DotVar6 _Val19 _Val20 _Val41 _Val42 _Gen0 _Gen1 _Gen10 _Gen11 _Gen12 ⟨.empty⟩ _Gen14 _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2 _Gen20 _Gen21 _Gen22 _Gen23 _Gen24 _Gen25 _Gen26 _Gen27 _Gen28 _Gen29 _Gen3 _Gen30 _Gen31 _Gen32 _Gen33 _Gen34 _Gen35 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 _Gen9 _Val34 _Val36 _Val37 _Val38 _Val35)) .empty ) := by
  let acc : SortAccountCell := {
          acctID := { val := ID_CELL },
          balance := _Gen23,
          code := _Gen24,
          storage := { val := STORAGE_CELL },
          origStorage := { val := ORIG_STORAGE_CELL },
          transientStorage := _Gen25,
          nonce := _Gen26 }
  let acc_updated : SortAccountCell := {
    acctID := { val := ID_CELL },
    balance := _Gen23,
    code := _Gen24,
    storage := { val := _Val40 },
    origStorage := { val := ORIG_STORAGE_CELL },
    transientStorage := _Gen25,
    nonce := _Gen26 }
  rw [pcZero, codeSstoreLHS, codeSstoreRHS, sstore_prestate_equiv, sstore_poststate_equiv] <;> try assumption
  simp
  have pc_equiv : intMap 0 = UInt256.ofNat 0 := rfl
  rw [pc_equiv, X_sstore_summary] <;> try assumption
  . congr
    . simp [State.lookupAccount, sstoreLHS, sstoreRHS]
      simp [Axioms.accountsCell_map_find? acc (by eq_refl) defn_Val19 defn_Val20]
      apply (Axioms.accountsCell_map_insert defn_Val34 defn_Val35 defn_Val36 defn_Val37 defn_Val38 defn_Val40 defn_Val41 defn_Val42 defn_Val19 defn_Val20)
    . /- Refund Cell -/
      sorry
    . /- Gas Cell -/
      rw [cancun, Csstore_def, Option.some.injEq] at defn_Val10 defn_Val3
      simp [EVM.Csstore, sstoreLHS, sstoreRHS]
      simp [GasConstants.Gwarmaccess, GasConstants.Gcoldsload, GasConstants.Gsset, GasConstants.Gsreset]
      rw [intMap_sub_dist] <;> try assumption
      . congr
        conv =>
        rhs
        simp [intMap, UInt256.toSigned]
        cases cg: (sstore_gas ACCESSEDSTORAGE_CELL W1 _Val22 _Val23 ID_CELL W0) <;> try contradiction
        next n =>
          congr
          simp [sstore_gas, Csstore_compute] at *
          sorry
        next =>
          have fls := sstore_gas_pos ACCESSEDSTORAGE_CELL W1 _Val22 _Val23 ID_CELL W0
          rw [cg] at fls; contradiction
      . aesop (add simp [sstore_gas, Csstore_compute]) (add safe (by omega))
    . aesop (add simp [plusInt_def])
  . /- We should have a theorem saying that `sstore_gas` and `Csstore` compute the same value -/
    sorry

end SstoreOpcodeEquivalence
