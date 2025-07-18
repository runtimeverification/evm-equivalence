import EvmEquivalence.Summaries.SloadSummary
import EvmEquivalence.Interfaces.EvmYulInterface
import EvmEquivalence.Interfaces.GasInterface
import EvmEquivalence.Interfaces.FuncInterface
import EvmEquivalence.StateMap

open EvmYul
open StateMap
open KEVMInterface
open SloadSummary

namespace SloadOpcodeEquivalence

def sloadLHS
  {ACCESSEDSTORAGE_CELL : SortMap}
  {GAS_CELL ID_CELL PC_CELL W0 : SortInt}
  {K_CELL : SortK}
  {SCHEDULE_CELL : SortSchedule}
  {USEGAS_CELL : SortBool}
  {WS : SortWordStack}
  {_DotVar0 : SortGeneratedCounterCell}
  {_DotVar6 _Val9 : SortAccountCellMap}
  {_Gen0 : SortProgramCell}
  {_Gen1 : SortJumpDestsCell}
  {_Gen10 : SortSelfDestructCell}
  {_Gen11 : SortLogCell}
  {_Gen12 : SortRefundCell}
  {_Gen13 : SortAccessedAccountsCell}
  {_Gen14 : SortCreatedAccountsCell}
  {_Gen15 : SortOutputCell}
  {_Gen16 : SortStatusCodeCell}
  {_Gen17 : SortCallStackCell}
  {_Gen18 : SortInterimStatesCell}
  {_Gen19 : SortTouchedAccountsCell}
  {_Gen2 : SortCallerCell}
  {_Gen20 : SortVersionedHashesCell}
  {_Gen21 : SortGasPriceCell}
  {_Gen22 : SortOriginCell}
  {_Gen23 : SortBlockhashesCell}
  {_Gen24 : SortBlockCell}
  {_Gen25 : SortBalanceCell}
  {_Gen26 : SortCodeCell}
  {_Gen27 : SortOrigStorageCell}
  {_Gen28 : SortTransientStorageCell}
  {_Gen29 : SortNonceCell}
  {_Gen3 : SortCallDataCell}
  {_Gen30 : SortChainIDCell}
  {_Gen31 : SortTxOrderCell}
  {_Gen32 : SortTxPendingCell}
  {_Gen33 : SortMessagesCell}
  {_Gen34 : SortWithdrawalsPendingCell}
  {_Gen35 : SortWithdrawalsOrderCell}
  {_Gen36 : SortWithdrawalsCell}
  {_Gen37 : SortExitCodeCell}
  {_Gen38 : SortModeCell}
  {_Gen4 : SortCallValueCell}
  {_Gen5 : SortLocalMemCell}
  {_Gen6 : SortMemoryUsedCell}
  {_Gen7 : SortCallGasCell}
  {_Gen8 : SortStaticCell}
  {_Gen9 : SortCallDepthCell} : SortGeneratedTopCell :=
  {kevm := {
        k := { val := SortK.kseq ((@inj SortInternalOp SortKItem) (SortInternalOp.«#next[_]_EVM_InternalOp_MaybeOpCode» ((@inj SortUnStackOp SortMaybeOpCode) SortUnStackOp.SLOAD_EVM_UnStackOp))) K_CELL },
        exitCode := _Gen37,
        mode := _Gen38,
        schedule := { val := SCHEDULE_CELL },
        useGas := { val := USEGAS_CELL },
        ethereum := {
          evm := {
            output := _Gen15,
            statusCode := _Gen16,
            callStack := _Gen17,
            interimStates := _Gen18,
            touchedAccounts := _Gen19,
            callState := {
              program := _Gen0,
              jumpDests := _Gen1,
              id := { val := (@inj SortInt SortAccount) ID_CELL },
              caller := _Gen2,
              callData := _Gen3,
              callValue := _Gen4,
              wordStack := { val := SortWordStack.«_:__EVM-TYPES_WordStack_Int_WordStack» W0 WS },
              localMem := _Gen5,
              pc := { val := PC_CELL },
              gas := { val := (@inj SortInt SortGas) GAS_CELL },
              memoryUsed := _Gen6,
              callGas := _Gen7,
              static := _Gen8,
              callDepth := _Gen9 },
            versionedHashes := _Gen20,
            substate := {
              selfDestruct := _Gen10,
              log := _Gen11,
              refund := _Gen12,
              accessedAccounts := _Gen13,
              accessedStorage := { val := ACCESSEDSTORAGE_CELL },
              createdAccounts := _Gen14 },
            gasPrice := _Gen21,
            origin := _Gen22,
            blockhashes := _Gen23,
            block := _Gen24 },
          network := {
            chainID := _Gen30,
            accounts := { val := _Val9 },
            txOrder := _Gen31,
            txPending := _Gen32,
            messages := _Gen33,
            withdrawalsPending := _Gen34,
            withdrawalsOrder := _Gen35,
            withdrawals := _Gen36 } } },
      generatedCounter := _DotVar0 }

def sloadRHS
  {_Val22 : SortMap}
  {ID_CELL _Val10 _Val11 _Val13 _Val14 _Val15 _Val16 _Val2 _Val3 _Val4 : SortInt}
  {K_CELL : SortK}
  {SCHEDULE_CELL : SortSchedule}
  {_Val0 _Val1 _Val12 _Val5 _Val6 _Val7 : SortBool}
  {WS : SortWordStack}
  {_DotVar0 : SortGeneratedCounterCell}
  {_DotVar6 _Val23 _Val24 _Val8 _Val9 : SortAccountCellMap}
  {_Gen0 : SortProgramCell}
  {_Gen1 : SortJumpDestsCell}
  {_Gen10 : SortSelfDestructCell}
  {_Gen11 : SortLogCell}
  {_Gen12 : SortRefundCell}
  {_Gen13 : SortAccessedAccountsCell}
  {_Gen14 : SortCreatedAccountsCell}
  {_Gen15 : SortOutputCell}
  {_Gen16 : SortStatusCodeCell}
  {_Gen17 : SortCallStackCell}
  {_Gen18 : SortInterimStatesCell}
  {_Gen19 : SortTouchedAccountsCell}
  {_Gen2 : SortCallerCell}
  {_Gen20 : SortVersionedHashesCell}
  {_Gen21 : SortGasPriceCell}
  {_Gen22 : SortOriginCell}
  {_Gen23 : SortBlockhashesCell}
  {_Gen24 : SortBlockCell}
  {_Gen25 : SortBalanceCell}
  {_Gen26 : SortCodeCell}
  {_Gen27 : SortOrigStorageCell}
  {_Gen28 : SortTransientStorageCell}
  {_Gen29 : SortNonceCell}
  {_Gen3 : SortCallDataCell}
  {_Gen30 : SortChainIDCell}
  {_Gen31 : SortTxOrderCell}
  {_Gen32 : SortTxPendingCell}
  {_Gen33 : SortMessagesCell}
  {_Gen34 : SortWithdrawalsPendingCell}
  {_Gen35 : SortWithdrawalsOrderCell}
  {_Gen36 : SortWithdrawalsCell}
  {_Gen37 : SortExitCodeCell}
  {_Gen38 : SortModeCell}
  {_Gen4 : SortCallValueCell}
  {_Gen5 : SortLocalMemCell}
  {_Gen6 : SortMemoryUsedCell}
  {_Gen7 : SortCallGasCell}
  {_Gen8 : SortStaticCell}
  {_Gen9 : SortCallDepthCell}
  {_Val17 _Val19 _Val20 _Val21 : SortSet}
  {_Val18 : SortKItem} : SortGeneratedTopCell :=
  { kevm := {
      k := { val := K_CELL },
      exitCode := _Gen37,
      mode := _Gen38,
      schedule := { val := SCHEDULE_CELL },
      useGas := { val := true },
      ethereum := {
        evm := {
          output := _Gen15,
          statusCode := _Gen16,
          callStack := _Gen17,
          interimStates := _Gen18,
          touchedAccounts := _Gen19,
          callState := {
            program := _Gen0,
            jumpDests := _Gen1,
            id := { val := (@inj SortInt SortAccount) ID_CELL },
            caller := _Gen2,
            callData := _Gen3,
            callValue := _Gen4,
            wordStack := { val := SortWordStack.«_:__EVM-TYPES_WordStack_Int_WordStack» _Val10 WS },
            localMem := _Gen5,
            pc := { val := _Val11 },
            gas := { val := (@inj SortInt SortGas) _Val16 },
            memoryUsed := _Gen6,
            callGas := _Gen7,
            static := _Gen8,
            callDepth := _Gen9 },
          versionedHashes := _Gen20,
          substate := {
            selfDestruct := _Gen10,
            log := _Gen11,
            refund := _Gen12,
            accessedAccounts := _Gen13,
            accessedStorage := { val := _Val22 },
            createdAccounts := _Gen14 },
          gasPrice := _Gen21,
          origin := _Gen22,
          blockhashes := _Gen23,
          block := _Gen24 },
        network := {
          chainID := _Gen30,
          accounts := { val := _Val24 },
          txOrder := _Gen31,
          txPending := _Gen32,
          messages := _Gen33,
          withdrawalsPending := _Gen34,
          withdrawalsOrder := _Gen35,
          withdrawals := _Gen36 } } },
      generatedCounter := _DotVar0 }

theorem rw_sloadLHS_sloadRHS
  {ACCESSEDSTORAGE_CELL STORAGE_CELL _Val22 : SortMap}
  {GAS_CELL ID_CELL PC_CELL W0 _Val10 _Val11 _Val13 _Val14 _Val15 _Val16 _Val2 _Val3 _Val4 : SortInt}
  {K_CELL : SortK}
  {SCHEDULE_CELL : SortSchedule}
  {USEGAS_CELL _Val0 _Val1 _Val12 _Val5 _Val6 _Val7 : SortBool}
  {WS : SortWordStack}
  {_DotVar0 : SortGeneratedCounterCell}
  {_DotVar6 _Val23 _Val24 _Val8 _Val9 : SortAccountCellMap}
  {_Gen0 : SortProgramCell}
  {_Gen1 : SortJumpDestsCell}
  {_Gen10 : SortSelfDestructCell}
  {_Gen11 : SortLogCell}
  {_Gen12 : SortRefundCell}
  {_Gen13 : SortAccessedAccountsCell}
  {_Gen14 : SortCreatedAccountsCell}
  {_Gen15 : SortOutputCell}
  {_Gen16 : SortStatusCodeCell}
  {_Gen17 : SortCallStackCell}
  {_Gen18 : SortInterimStatesCell}
  {_Gen19 : SortTouchedAccountsCell}
  {_Gen2 : SortCallerCell}
  {_Gen20 : SortVersionedHashesCell}
  {_Gen21 : SortGasPriceCell}
  {_Gen22 : SortOriginCell}
  {_Gen23 : SortBlockhashesCell}
  {_Gen24 : SortBlockCell}
  {_Gen25 : SortBalanceCell}
  {_Gen26 : SortCodeCell}
  {_Gen27 : SortOrigStorageCell}
  {_Gen28 : SortTransientStorageCell}
  {_Gen29 : SortNonceCell}
  {_Gen3 : SortCallDataCell}
  {_Gen30 : SortChainIDCell}
  {_Gen31 : SortTxOrderCell}
  {_Gen32 : SortTxPendingCell}
  {_Gen33 : SortMessagesCell}
  {_Gen34 : SortWithdrawalsPendingCell}
  {_Gen35 : SortWithdrawalsOrderCell}
  {_Gen36 : SortWithdrawalsCell}
  {_Gen37 : SortExitCodeCell}
  {_Gen38 : SortModeCell}
  {_Gen4 : SortCallValueCell}
  {_Gen5 : SortLocalMemCell}
  {_Gen6 : SortMemoryUsedCell}
  {_Gen7 : SortCallGasCell}
  {_Gen8 : SortStaticCell}
  {_Gen9 : SortCallDepthCell}
  {_Val17 _Val19 _Val20 _Val21 : SortSet}
  {_Val18 : SortKItem}
  (defn_Val0 : «_<<_>>_SCHEDULE_Bool_ScheduleFlag_Schedule» SortScheduleFlag.Ghasaccesslist_SCHEDULE_ScheduleFlag SCHEDULE_CELL = some _Val0)
  (defn_Val1 : «#inStorage» ACCESSEDSTORAGE_CELL ((@inj SortInt SortAccount) ID_CELL) W0 = some _Val1)
  (defn_Val2 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gwarmstorageread_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val2)
  (defn_Val3 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gcoldsload_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val3)
  (defn_Val4 : kite _Val1 _Val2 _Val3 = some _Val4)
  (defn_Val5 : «_<=Int_» _Val4 GAS_CELL = some _Val5)
  (defn_Val6 : _andBool_ _Val0 _Val5 = some _Val6)
  (defn_Val7 : _andBool_ USEGAS_CELL _Val6 = some _Val7)
  (defn_Val8 : AccountCellMapItem { val := ID_CELL } {
    acctID := { val := ID_CELL },
    balance := _Gen25,
    code := _Gen26,
    storage := { val := STORAGE_CELL },
    origStorage := _Gen27,
    transientStorage := _Gen28,
    nonce := _Gen29 } = some _Val8)
  (defn_Val9 : _AccountCellMap_ _Val8 _DotVar6 = some _Val9)
  (defn_Val10 : lookup STORAGE_CELL W0 = some _Val10)
  (defn_Val11 : «_+Int_» PC_CELL 1 = some _Val11)
  (defn_Val12 : «#inStorage» ACCESSEDSTORAGE_CELL ((@inj SortInt SortAccount) ID_CELL) W0 = some _Val12)
  (defn_Val13 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gwarmstorageread_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val13)
  (defn_Val14 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gcoldsload_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val14)
  (defn_Val15 : kite _Val12 _Val13 _Val14 = some _Val15)
  (defn_Val16 : «_-Int_» GAS_CELL _Val15 = some _Val16)
  (defn_Val17 : «.Set» = some _Val17)
  (defn_Val18 : «Map:lookupOrDefault» ACCESSEDSTORAGE_CELL ((@inj SortInt SortKItem) ID_CELL) ((@inj SortSet SortKItem) _Val17) = some _Val18)
  (defn_Val19 : «project:Set» (SortK.kseq _Val18 SortK.dotk) = some _Val19)
  (defn_Val20 : SetItem ((@inj SortInt SortKItem) W0) = some _Val20)
  (defn_Val21 : «_|Set__SET_Set_Set_Set» _Val19 _Val20 = some _Val21)
  (defn_Val22 : «Map:update» ACCESSEDSTORAGE_CELL ((@inj SortInt SortKItem) ID_CELL) ((@inj SortSet SortKItem) _Val21) = some _Val22)
  (defn_Val23 : AccountCellMapItem { val := ID_CELL } {
    acctID := { val := ID_CELL },
    balance := _Gen25,
    code := _Gen26,
    storage := { val := STORAGE_CELL },
    origStorage := _Gen27,
    transientStorage := _Gen28,
    nonce := _Gen29 } = some _Val23)
  (defn_Val24 : _AccountCellMap_ _Val23 _DotVar6 = some _Val24)
  (req : _Val7 = true) :
  Rewrites
  (@sloadLHS ACCESSEDSTORAGE_CELL GAS_CELL ID_CELL PC_CELL W0 K_CELL SCHEDULE_CELL USEGAS_CELL WS _DotVar0 _DotVar6 _Val9 _Gen0 _Gen1 _Gen10 _Gen11 _Gen12 _Gen13 _Gen14 _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2 _Gen20 _Gen21 _Gen22 _Gen23 _Gen24 _Gen25 _Gen26 _Gen27 _Gen28 _Gen29 _Gen3 _Gen30 _Gen31 _Gen32 _Gen33 _Gen34 _Gen35 _Gen36 _Gen37 _Gen38 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 _Gen9)
  (@sloadRHS _Val22 ID_CELL _Val10 _Val11 _Val13 _Val14 _Val15 _Val16 _Val2 _Val3 _Val4 K_CELL SCHEDULE_CELL _Val0 _Val1 _Val12 _Val5 _Val6 _Val7 WS _DotVar0 _DotVar6 _Val23 _Val24 _Val8 _Val9 _Gen0 _Gen1 _Gen10 _Gen11 _Gen12 _Gen13 _Gen14 _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2 _Gen20 _Gen21 _Gen22 _Gen23 _Gen24 _Gen25 _Gen26 _Gen27 _Gen28 _Gen29 _Gen3 _Gen30 _Gen31 _Gen32 _Gen33 _Gen34 _Gen35 _Gen36 _Gen37 _Gen38 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 _Gen9 _Val17 _Val19 _Val20 _Val21 _Val18) := by
  apply (@Rewrites.SLOAD_SUMMARY_SLOAD_SUMMARY_USEGAS_BERLIN ACCESSEDSTORAGE_CELL STORAGE_CELL _Val22 GAS_CELL ID_CELL PC_CELL W0 _Val10 _Val11 _Val13 _Val14 _Val15 _Val16 _Val2 _Val3 _Val4 SCHEDULE_CELL USEGAS_CELL _Val0 _Val1 _Val12 _Val5 _Val6 _Val7 _DotVar0 _DotVar6 _Val23 _Val24 _Val8)
  all_goals assumption

theorem sload_prestate_equiv
  {ACCESSEDSTORAGE_CELL : SortMap}
  {GAS_CELL ID_CELL PC_CELL W0 : SortInt}
  {K_CELL : SortK}
  {SCHEDULE_CELL : SortSchedule}
  {USEGAS_CELL : SortBool}
  {WS : SortWordStack}
  {_DotVar0 : SortGeneratedCounterCell}
  {_DotVar6 _Val9 : SortAccountCellMap}
  {_Gen0 : SortProgramCell}
  {_Gen1 : SortJumpDestsCell}
  {_Gen10 : SortSelfDestructCell}
  {_Gen11 : SortLogCell}
  {_Gen12 : SortRefundCell}
  {_Gen13 : SortAccessedAccountsCell}
  {_Gen14 : SortCreatedAccountsCell}
  {_Gen15 : SortOutputCell}
  {_Gen16 : SortStatusCodeCell}
  {_Gen17 : SortCallStackCell}
  {_Gen18 : SortInterimStatesCell}
  {_Gen19 : SortTouchedAccountsCell}
  {_Gen2 : SortCallerCell}
  {_Gen20 : SortVersionedHashesCell}
  {_Gen21 : SortGasPriceCell}
  {_Gen22 : SortOriginCell}
  {_Gen23 : SortBlockhashesCell}
  {_Gen24 : SortBlockCell}
  {_Gen25 : SortBalanceCell}
  {_Gen26 : SortCodeCell}
  {_Gen27 : SortOrigStorageCell}
  {_Gen28 : SortTransientStorageCell}
  {_Gen29 : SortNonceCell}
  {_Gen3 : SortCallDataCell}
  {_Gen30 : SortChainIDCell}
  {_Gen31 : SortTxOrderCell}
  {_Gen32 : SortTxPendingCell}
  {_Gen33 : SortMessagesCell}
  {_Gen34 : SortWithdrawalsPendingCell}
  {_Gen35 : SortWithdrawalsOrderCell}
  {_Gen36 : SortWithdrawalsCell}
  {_Gen37 : SortExitCodeCell}
  {_Gen38 : SortModeCell}
  {_Gen4 : SortCallValueCell}
  {_Gen5 : SortLocalMemCell}
  {_Gen6 : SortMemoryUsedCell}
  {_Gen7 : SortCallGasCell}
  {_Gen8 : SortStaticCell}
  {_Gen9 : SortCallDepthCell}
  (symState : EVM.State):
  let lhs := @sloadLHS ACCESSEDSTORAGE_CELL GAS_CELL ID_CELL PC_CELL W0 K_CELL SCHEDULE_CELL USEGAS_CELL WS _DotVar0 _DotVar6 _Val9 _Gen0 _Gen1 _Gen10 _Gen11 _Gen12 _Gen13 _Gen14 _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2 _Gen20 _Gen21 _Gen22 _Gen23 _Gen24 _Gen25 _Gen26 _Gen27 _Gen28 _Gen29 _Gen3 _Gen30 _Gen31 _Gen32 _Gen33 _Gen34 _Gen35 _Gen36 _Gen37 _Gen38 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 _Gen9
  stateMap symState lhs =
  {symState with
    stack := (intMap W0) :: wordStackMap WS
    pc := intMap PC_CELL
    gasAvailable := intMap GAS_CELL
    executionEnv := executionEnv_map lhs symState
    accountMap := Axioms.SortAccountsCellMap lhs.accounts
    activeWords := intMap lhs.memoryUsed.val
    memory := memory_map lhs.memory
    substate := {symState.substate with
            accessedStorageKeys :=  Axioms.SortAccessedStorageCellMap (SortGeneratedTopCell.accessedStorage lhs)
            refundBalance := intMap lhs.refund.val
           }
    returnData := _Gen15.val
    } := by rfl

theorem sload_poststate_equiv
  -- We have to include `ACCESSEDSTORAGE_CELL` as we need the original map to look up
  {ACCESSEDSTORAGE_CELL _Val22 : SortMap}
  -- We have to include `W0` as we need the key to look up
  {GAS_CELL ID_CELL PC_CELL W0 _Val10 _Val11 _Val13 _Val14 _Val15 _Val16 _Val2 _Val3 _Val4 : SortInt}
  {K_CELL : SortK}
  {SCHEDULE_CELL : SortSchedule}
  {_Val0 _Val1 _Val12 _Val5 _Val6 _Val7 : SortBool}
  {WS : SortWordStack}
  {_DotVar0 : SortGeneratedCounterCell}
  {_DotVar6 _Val23 _Val24 _Val8 _Val9 : SortAccountCellMap}
  {_Gen0 : SortProgramCell}
  {_Gen1 : SortJumpDestsCell}
  {_Gen10 : SortSelfDestructCell}
  {_Gen11 : SortLogCell}
  {_Gen12 : SortRefundCell}
  {_Gen13 : SortAccessedAccountsCell}
  {_Gen14 : SortCreatedAccountsCell}
  {_Gen15 : SortOutputCell}
  {_Gen16 : SortStatusCodeCell}
  {_Gen17 : SortCallStackCell}
  {_Gen18 : SortInterimStatesCell}
  {_Gen19 : SortTouchedAccountsCell}
  {_Gen2 : SortCallerCell}
  {_Gen20 : SortVersionedHashesCell}
  {_Gen21 : SortGasPriceCell}
  {_Gen22 : SortOriginCell}
  {_Gen23 : SortBlockhashesCell}
  {_Gen24 : SortBlockCell}
  {_Gen25 : SortBalanceCell}
  {_Gen26 : SortCodeCell}
  {_Gen27 : SortOrigStorageCell}
  {_Gen28 : SortTransientStorageCell}
  {_Gen29 : SortNonceCell}
  {_Gen3 : SortCallDataCell}
  {_Gen30 : SortChainIDCell}
  {_Gen31 : SortTxOrderCell}
  {_Gen32 : SortTxPendingCell}
  {_Gen33 : SortMessagesCell}
  {_Gen34 : SortWithdrawalsPendingCell}
  {_Gen35 : SortWithdrawalsOrderCell}
  {_Gen36 : SortWithdrawalsCell}
  {_Gen37 : SortExitCodeCell}
  {_Gen38 : SortModeCell}
  {_Gen4 : SortCallValueCell}
  {_Gen5 : SortLocalMemCell}
  {_Gen6 : SortMemoryUsedCell}
  {_Gen7 : SortCallGasCell}
  {_Gen8 : SortStaticCell}
  {_Gen9 : SortCallDepthCell}
  {_Val17 _Val19 _Val20 _Val21 : SortSet}
  {_Val18 : SortKItem}
  (defn_Val11 : «_+Int_» PC_CELL 1 = some _Val11)
  (defn_Val12 : «#inStorage» ACCESSEDSTORAGE_CELL ((@inj SortInt SortAccount) ID_CELL) W0 = some _Val12)
  (defn_Val13 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gwarmstorageread_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val13)
  (defn_Val14 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gcoldsload_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val14)
  (defn_Val15 : kite _Val12 _Val13 _Val14 = some _Val15)
  (defn_Val16 : «_-Int_» GAS_CELL _Val15 = some _Val16)
  (gasEnough : _Val15 ≤ GAS_CELL)
  (gasSmall : GAS_CELL < ↑UInt256.size)
  (cancun : SCHEDULE_CELL = .CANCUN_EVM)
  (symState : EVM.State) :
  let rhs := @sloadRHS _Val22 ID_CELL _Val10 _Val11 _Val13 _Val14 _Val15 _Val16 _Val2 _Val3 _Val4 K_CELL SCHEDULE_CELL _Val0 _Val1 _Val12 _Val5 _Val6 _Val7 WS _DotVar0 _DotVar6 _Val23 _Val24 _Val8 _Val9 _Gen0 _Gen1 _Gen10 _Gen11 _Gen12 _Gen13 _Gen14 _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2 _Gen20 _Gen21 _Gen22 _Gen23 _Gen24 _Gen25 _Gen26 _Gen27 _Gen28 _Gen29 _Gen3 _Gen30 _Gen31 _Gen32 _Gen33 _Gen34 _Gen35 _Gen36 _Gen37 _Gen38 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 _Gen9 _Val17 _Val19 _Val20 _Val21 _Val18
  stateMap symState rhs =
  {symState with
    stack := intMap _Val10 :: wordStackMap WS
    pc := intMap (PC_CELL + 1)
    gasAvailable := intMap GAS_CELL -  intMap _Val15 --(sload_gas ACCESSEDSTORAGE_CELL W0)
    executionEnv := executionEnv_map rhs symState
    accountMap := Axioms.SortAccountsCellMap rhs.accounts,
    activeWords := intMap rhs.memoryUsed.val
    memory := memory_map rhs.memory
    substate := {symState.substate with
            accessedStorageKeys :=  Axioms.SortAccessedStorageCellMap  rhs.accessedStorage
            refundBalance := intMap _Gen12.val
           }
    returnData := _Gen15.val
  } := by
  simp_all [sloadRHS, stateMap, «_-Int_», «_+Int_»]
  aesop (add simp [inj, Inj.inj]) (add safe (by rw [intMap_sub_dist]))

theorem step_sload_equiv
  {ACCESSEDSTORAGE_CELL STORAGE_CELL _Val22 : SortMap}
  {GAS_CELL ID_CELL PC_CELL W0 _Val10 _Val11 _Val13 _Val14 _Val15 _Val16 _Val2 _Val3 _Val4 : SortInt}
  {K_CELL : SortK}
  {SCHEDULE_CELL : SortSchedule}
  {USEGAS_CELL _Val0 _Val1 _Val12 _Val5 _Val6 _Val7 : SortBool}
  {WS : SortWordStack}
  {_DotVar0 : SortGeneratedCounterCell}
  {_DotVar6 _Val23 _Val24 _Val8 _Val9 : SortAccountCellMap}
  {_Gen0 : SortProgramCell}
  {_Gen1 : SortJumpDestsCell}
  {_Gen10 : SortSelfDestructCell}
  {_Gen11 : SortLogCell}
  {_Gen12 : SortRefundCell}
  {_Gen13 : SortAccessedAccountsCell}
  {_Gen14 : SortCreatedAccountsCell}
  {_Gen15 : SortOutputCell}
  {_Gen16 : SortStatusCodeCell}
  {_Gen17 : SortCallStackCell}
  {_Gen18 : SortInterimStatesCell}
  {_Gen19 : SortTouchedAccountsCell}
  {_Gen2 : SortCallerCell}
  {_Gen20 : SortVersionedHashesCell}
  {_Gen21 : SortGasPriceCell}
  {_Gen22 : SortOriginCell}
  {_Gen23 : SortBlockhashesCell}
  {_Gen24 : SortBlockCell}
  {_Gen25 : SortBalanceCell}
  {_Gen26 : SortCodeCell}
  {_Gen27 : SortOrigStorageCell}
  {_Gen28 : SortTransientStorageCell}
  {_Gen29 : SortNonceCell}
  {_Gen3 : SortCallDataCell}
  {_Gen30 : SortChainIDCell}
  {_Gen31 : SortTxOrderCell}
  {_Gen32 : SortTxPendingCell}
  {_Gen33 : SortMessagesCell}
  {_Gen34 : SortWithdrawalsPendingCell}
  {_Gen35 : SortWithdrawalsOrderCell}
  {_Gen36 : SortWithdrawalsCell}
  {_Gen37 : SortExitCodeCell}
  {_Gen38 : SortModeCell}
  {_Gen4 : SortCallValueCell}
  {_Gen5 : SortLocalMemCell}
  {_Gen6 : SortMemoryUsedCell}
  {_Gen7 : SortCallGasCell}
  {_Gen8 : SortStaticCell}
  {_Gen9 : SortCallDepthCell}
  {_Val17 _Val19 _Val20 _Val21 : SortSet}
  {_Val18 : SortKItem}
  (defn_Val0 : «_<<_>>_SCHEDULE_Bool_ScheduleFlag_Schedule» SortScheduleFlag.Ghasaccesslist_SCHEDULE_ScheduleFlag SCHEDULE_CELL = some _Val0)
  (defn_Val1 : «#inStorage» ACCESSEDSTORAGE_CELL ((@inj SortInt SortAccount) ID_CELL) W0 = some _Val1)
  (defn_Val2 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gwarmstorageread_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val2)
  (defn_Val3 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gcoldsload_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val3)
  (defn_Val4 : kite _Val1 _Val2 _Val3 = some _Val4)
  (defn_Val5 : «_<=Int_» _Val4 GAS_CELL = some _Val5)
  /- (defn_Val6 : _andBool_ _Val0 _Val5 = some _Val6) -/
  (defn_Val7 : _andBool_ USEGAS_CELL _Val6 = some _Val7)
  (defn_Val8 : AccountCellMapItem { val := ID_CELL } {
    acctID := { val := ID_CELL },
    balance := _Gen25,
    code := _Gen26,
    storage := { val := STORAGE_CELL },
    origStorage := _Gen27,
    transientStorage := _Gen28,
    nonce := _Gen29 } = some _Val8)
  (defn_Val9 : _AccountCellMap_ _Val8 _DotVar6 = some _Val9)
  (defn_Val10 : lookup STORAGE_CELL W0 = some _Val10)
  (defn_Val11 : «_+Int_» PC_CELL 1 = some _Val11)
  (defn_Val12 : «#inStorage» ACCESSEDSTORAGE_CELL ((@inj SortInt SortAccount) ID_CELL) W0 = some _Val12)
  (defn_Val13 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gwarmstorageread_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val13)
  (defn_Val14 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gcoldsload_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val14)
  (defn_Val15 : kite _Val12 _Val13 _Val14 = some _Val15)
  (defn_Val16 : «_-Int_» GAS_CELL _Val15 = some _Val16)
  (defn_Val17 : «.Set» = some _Val17)
  (defn_Val18 : «Map:lookupOrDefault» ACCESSEDSTORAGE_CELL ((@inj SortInt SortKItem) ID_CELL) ((@inj SortSet SortKItem) _Val17) = some _Val18)
  (defn_Val19 : «project:Set» (SortK.kseq _Val18 SortK.dotk) = some _Val19)
  (defn_Val20 : SetItem ((@inj SortInt SortKItem) W0) = some _Val20)
  (defn_Val21 : «_|Set__SET_Set_Set_Set» _Val19 _Val20 = some _Val21)
  (defn_Val22 : «Map:update» ACCESSEDSTORAGE_CELL ((@inj SortInt SortKItem) ID_CELL) ((@inj SortSet SortKItem) _Val21) = some _Val22)
  (defn_Val23 : AccountCellMapItem { val := ID_CELL } {
    acctID := { val := ID_CELL },
    balance := _Gen25,
    code := _Gen26,
    storage := { val := STORAGE_CELL },
    origStorage := _Gen27,
    transientStorage := _Gen28,
    nonce := _Gen29 } = some _Val23)
  (defn_Val24 : _AccountCellMap_ _Val23 _DotVar6 = some _Val24)
  (req : _Val7 = true)
  (symState : EVM.State)
  -- needed for EVM.step
  (gasCost : ℕ)
  -- Necessary assumptions for equivalence
  (cancun : SCHEDULE_CELL = .CANCUN_EVM)
  (gavailEnough : _Val15 ≤ GAS_CELL)
  (gavailSmall : GAS_CELL < ↑UInt256.size)
  (gasCostValue : gasCost = _Val15.toNat)
  (pcountSmall : PC_CELL + 1 < UInt256.size)
  (pcountNonneg : 0 ≤ PC_CELL):
  EVM.step_sload (Int.toNat GAS_CELL) gasCost (stateMap symState (@sloadLHS ACCESSEDSTORAGE_CELL GAS_CELL ID_CELL PC_CELL W0 K_CELL SCHEDULE_CELL USEGAS_CELL WS _DotVar0 _DotVar6 _Val9 _Gen0 _Gen1 _Gen10 _Gen11 _Gen12 _Gen13 _Gen14 _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2 _Gen20 _Gen21 _Gen22 _Gen23 _Gen24 _Gen25 _Gen26 _Gen27 _Gen28 _Gen29 _Gen3 _Gen30 _Gen31 _Gen32 _Gen33 _Gen34 _Gen35 _Gen36 _Gen37 _Gen38 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 _Gen9)) =
  .ok (stateMap {symState with execLength := symState.execLength + 1} (@sloadRHS _Val22 ID_CELL _Val10 _Val11 _Val13 _Val14 _Val15 _Val16 _Val2 _Val3 _Val4 K_CELL SCHEDULE_CELL _Val0 _Val1 _Val12 _Val5 _Val6 _Val7 WS _DotVar0 _DotVar6 _Val23 _Val24 _Val8 _Val9 _Gen0 _Gen1 _Gen10 _Gen11 _Gen12 _Gen13 _Gen14 _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2 _Gen20 _Gen21 _Gen22 _Gen23 _Gen24 _Gen25 _Gen26 _Gen27 _Gen28 _Gen29 _Gen3 _Gen30 _Gen31 _Gen32 _Gen33 _Gen34 _Gen35 _Gen36 _Gen37 _Gen38 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 _Gen9 _Val17 _Val19 _Val20 _Val21 _Val18)) := by
  cases cg: (Int.toNat GAS_CELL)
  next =>
    have val15_pos : 0 < _Val15 := by simp at defn_Val15; aesop
    have _ := Int.lt_of_lt_of_le val15_pos gavailEnough
    omega
  rw [sload_prestate_equiv, executionEnv_map, blockHeader_map, EVM.step_sload_summary] <;> try assumption
  rw [sloadLHS, sload_poststate_equiv, sloadRHS] <;> try congr
  . simp [State.lookupAccount, SortGeneratedTopCell.accounts, accountAddressMap]
    aesop
  . simp
    apply (Axioms.accessedStorageCell_map_insert defn_Val17 defn_Val18 defn_Val19 defn_Val20 defn_Val21 defn_Val22)
  . simp at defn_Val4; aesop (add simp [intMap])
  . rw [←UInt256.add_succ_mod_size, intMap_add_dist] <;> aesop
  . simp [State.lookupAccount]
    cases origc: _Gen27; next orig_storage =>
    rw [@Axioms.findAccountInAccountCellMap ID_CELL _Gen25 _Gen26 STORAGE_CELL orig_storage _Gen28 _Gen29 _Val8 _DotVar6 _Val9]
     <;> congr
    . simp [Account.lookupStorage]; apply Axioms.lookup_mapped_storage; assumption
    . rw [←origc]; assumption
  . omega

theorem X_sload_equiv
  {ACCESSEDSTORAGE_CELL STORAGE_CELL _Val22 : SortMap}
  {GAS_CELL ID_CELL PC_CELL W0 _Val10 _Val11 _Val13 _Val14 _Val15 _Val16 _Val2 _Val3 _Val4 : SortInt}
  {K_CELL : SortK}
  {SCHEDULE_CELL : SortSchedule}
  {USEGAS_CELL _Val0 _Val1 _Val12 _Val5 _Val6 _Val7 : SortBool}
  {WS : SortWordStack}
  {_DotVar0 : SortGeneratedCounterCell}
  {_DotVar6 _Val23 _Val24 _Val8 _Val9 : SortAccountCellMap}
  {_Gen0 : SortProgramCell}
  {_Gen1 : SortJumpDestsCell}
  {_Gen10 : SortSelfDestructCell}
  {_Gen11 : SortLogCell}
  {_Gen12 : SortRefundCell}
  {_Gen13 : SortAccessedAccountsCell}
  {_Gen14 : SortCreatedAccountsCell}
  {_Gen15 : SortOutputCell}
  {_Gen16 : SortStatusCodeCell}
  {_Gen17 : SortCallStackCell}
  {_Gen18 : SortInterimStatesCell}
  {_Gen19 : SortTouchedAccountsCell}
  {_Gen2 : SortCallerCell}
  {_Gen20 : SortVersionedHashesCell}
  {_Gen21 : SortGasPriceCell}
  {_Gen22 : SortOriginCell}
  {_Gen23 : SortBlockhashesCell}
  {_Gen24 : SortBlockCell}
  {_Gen25 : SortBalanceCell}
  {_Gen26 : SortCodeCell}
  {_Gen27 : SortOrigStorageCell}
  {_Gen28 : SortTransientStorageCell}
  {_Gen29 : SortNonceCell}
  {_Gen3 : SortCallDataCell}
  {_Gen30 : SortChainIDCell}
  {_Gen31 : SortTxOrderCell}
  {_Gen32 : SortTxPendingCell}
  {_Gen33 : SortMessagesCell}
  {_Gen34 : SortWithdrawalsPendingCell}
  {_Gen35 : SortWithdrawalsOrderCell}
  {_Gen36 : SortWithdrawalsCell}
  {_Gen37 : SortExitCodeCell}
  {_Gen38 : SortModeCell}
  {_Gen4 : SortCallValueCell}
  {_Gen5 : SortLocalMemCell}
  {_Gen6 : SortMemoryUsedCell}
  {_Gen7 : SortCallGasCell}
  {_Gen8 : SortStaticCell}
  {_Gen9 : SortCallDepthCell}
  {_Val17 _Val19 _Val20 _Val21 : SortSet}
  {_Val18 : SortKItem}
  (defn_Val0 : «_<<_>>_SCHEDULE_Bool_ScheduleFlag_Schedule» SortScheduleFlag.Ghasaccesslist_SCHEDULE_ScheduleFlag SCHEDULE_CELL = some _Val0)
  (defn_Val1 : «#inStorage» ACCESSEDSTORAGE_CELL ((@inj SortInt SortAccount) ID_CELL) W0 = some _Val1)
  (defn_Val2 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gwarmstorageread_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val2)
  (defn_Val3 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gcoldsload_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val3)
  (defn_Val4 : kite _Val1 _Val2 _Val3 = some _Val4)
  (defn_Val5 : «_<=Int_» _Val4 GAS_CELL = some _Val5)
  /- (defn_Val6 : _andBool_ _Val0 _Val5 = some _Val6) -/
  (defn_Val7 : _andBool_ USEGAS_CELL _Val6 = some _Val7)
  (defn_Val8 : AccountCellMapItem { val := ID_CELL } {
    acctID := { val := ID_CELL },
    balance := _Gen25,
    code := _Gen26,
    storage := { val := STORAGE_CELL },
    origStorage := _Gen27,
    transientStorage := _Gen28,
    nonce := _Gen29 } = some _Val8)
  (defn_Val9 : _AccountCellMap_ _Val8 _DotVar6 = some _Val9)
  (defn_Val10 : lookup STORAGE_CELL W0 = some _Val10)
  (defn_Val11 : «_+Int_» PC_CELL 1 = some _Val11)
  (defn_Val12 : «#inStorage» ACCESSEDSTORAGE_CELL ((@inj SortInt SortAccount) ID_CELL) W0 = some _Val12)
  (defn_Val13 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gwarmstorageread_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val13)
  (defn_Val14 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gcoldsload_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val14)
  (defn_Val15 : kite _Val12 _Val13 _Val14 = some _Val15)
  (defn_Val16 : «_-Int_» GAS_CELL _Val15 = some _Val16)
  (defn_Val17 : «.Set» = some _Val17)
  (defn_Val18 : «Map:lookupOrDefault» ACCESSEDSTORAGE_CELL ((@inj SortInt SortKItem) ID_CELL) ((@inj SortSet SortKItem) _Val17) = some _Val18)
  (defn_Val19 : «project:Set» (SortK.kseq _Val18 SortK.dotk) = some _Val19)
  (defn_Val20 : SetItem ((@inj SortInt SortKItem) W0) = some _Val20)
  (defn_Val21 : «_|Set__SET_Set_Set_Set» _Val19 _Val20 = some _Val21)
  (defn_Val22 : «Map:update» ACCESSEDSTORAGE_CELL ((@inj SortInt SortKItem) ID_CELL) ((@inj SortSet SortKItem) _Val21) = some _Val22)
  (defn_Val23 : AccountCellMapItem { val := ID_CELL } {
    acctID := { val := ID_CELL },
    balance := _Gen25,
    code := _Gen26,
    storage := { val := STORAGE_CELL },
    origStorage := _Gen27,
    transientStorage := _Gen28,
    nonce := _Gen29 } = some _Val23)
  (defn_Val24 : _AccountCellMap_ _Val23 _DotVar6 = some _Val24)
  (req : _Val7 = true)
  (symState : EVM.State)
  (symValidJumps : Array UInt256) -- TODO: Revisit
  -- Necessary assumptions for equivalence
  (cancun : SCHEDULE_CELL = .CANCUN_EVM)
  (gavailEnough : _Val15 < GAS_CELL)
  (gavailSmall : GAS_CELL < ↑UInt256.size)
  (codeSloadLHS : _Gen0 = ⟨⟨#[(0x54 : UInt8)]⟩⟩)
  (codeSloadRHS : _Gen26 = ⟨⟨⟨#[(0x54 : UInt8)]⟩⟩⟩)
  (pcZero : PC_CELL = 0)
  (wordStackOk : sizeWordStackAux WS 0 < some 1024)
  :
  EVM.X (UInt256.toNat (intMap GAS_CELL)) symValidJumps
  (stateMap symState (@sloadLHS ACCESSEDSTORAGE_CELL GAS_CELL ID_CELL PC_CELL W0 K_CELL SCHEDULE_CELL USEGAS_CELL WS _DotVar0 _DotVar6 _Val9 _Gen0 _Gen1 _Gen10 _Gen11 _Gen12 _Gen13 _Gen14 _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2 _Gen20 _Gen21 _Gen22 _Gen23 _Gen24 _Gen25 _Gen26 _Gen27 _Gen28 _Gen29 _Gen3 _Gen30 _Gen31 _Gen32 _Gen33 _Gen34 _Gen35 _Gen36 _Gen37 _Gen38 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 _Gen9)) =
  .ok (.success (stateMap {symState with execLength := symState.execLength + 2} (@sloadRHS _Val22 ID_CELL _Val10 _Val11 _Val13 _Val14 _Val15 _Val16 _Val2 _Val3 _Val4 K_CELL SCHEDULE_CELL _Val0 _Val1 _Val12 _Val5 _Val6 _Val7 WS _DotVar0 _DotVar6 _Val23 _Val24 _Val8 _Val9 _Gen0 _Gen1 _Gen10 _Gen11 _Gen12 _Gen13 _Gen14 ⟨.empty⟩ _Gen16 _Gen17 _Gen18 _Gen19 _Gen2 _Gen20 _Gen21 _Gen22 _Gen23 _Gen24 _Gen25 _Gen26 _Gen27 _Gen28 _Gen29 _Gen3 _Gen30 _Gen31 _Gen32 _Gen33 _Gen34 _Gen35 _Gen36 _Gen37 _Gen38 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 _Gen9 _Val17 _Val19 _Val20 _Val21 _Val18)) .empty ) := by
  rw [pcZero, codeSloadLHS, codeSloadRHS, sload_prestate_equiv, sload_poststate_equiv]
  <;> first | assumption | try linarith
  simp
  have pc_equiv : intMap 0 = UInt256.ofNat 0 := rfl
  simp [executionEnv_map, sloadLHS]
  rw [pc_equiv, X_sload_summary] <;> try simp [State.lookupAccount, sloadLHS, sloadRHS]
  <;> try assumption
  . constructor <;> constructor
    . rw [Axioms.accessedStorageCell_map_insert defn_Val17 defn_Val18 defn_Val19 defn_Val20 defn_Val21 defn_Val22]
      aesop
    . simp [EVM.Csload, GasConstants.Gwarmaccess, GasConstants.Gcoldsload]
      simp [*] at defn_Val12 defn_Val13 defn_Val14 defn_Val15; congr
      simp [←defn_Val13, ←defn_Val14, ←defn_Val15]
      rw [Axioms.contains_accessedStorage_map defn_Val12]
      aesop
    . aesop
    . cases origc: _Gen27; next orig_storage =>
      rw [@Axioms.findAccountInAccountCellMap ID_CELL _Gen25 _Gen26 STORAGE_CELL orig_storage _Gen28 _Gen29 _Val8 _DotVar6 _Val9]
      <;> congr
      . simp [Account.lookupStorage]; apply Axioms.lookup_mapped_storage; assumption
      . rw [←origc]; assumption
  . simp_all [sizeWordStack_def]
  . simp [EVM.Csload, GasConstants.Gwarmaccess, GasConstants.Gcoldsload]
    rw [Axioms.contains_accessedStorage_map defn_Val12]
    simp [cancun] at *; rw [intMap_toNat] <;> aesop (add safe (by linarith))

end SloadOpcodeEquivalence
