import EvmEquivalence.KEVM2Lean.Sorts

instance : Inj SortLogCell SortKItem where
  inj := SortKItem.inj_SortLogCell

instance : Inj SortSchedule SortKItem where
  inj := SortKItem.inj_SortSchedule

instance : Inj SortBlobGasUsedCell SortKItem where
  inj := SortKItem.inj_SortBlobGasUsedCell

instance : Inj SortCallDepthCell SortKItem where
  inj := SortKItem.inj_SortCallDepthCell

instance : Inj SortChainIDCell SortKItem where
  inj := SortKItem.inj_SortChainIDCell

instance : Inj SortWithdrawalsOrderCell SortKItem where
  inj := SortKItem.inj_SortWithdrawalsOrderCell

instance : Inj SortMsgIDCell SortKItem where
  inj := SortKItem.inj_SortMsgIDCell

instance : Inj SortSubstateCell SortKItem where
  inj := SortKItem.inj_SortSubstateCell

instance : Inj SortSigVCell SortKItem where
  inj := SortKItem.inj_SortSigVCell

instance : Inj SortTimestampCell SortKItem where
  inj := SortKItem.inj_SortTimestampCell

instance : Inj SortWithdrawalCellMap SortKItem where
  inj := SortKItem.inj_SortWithdrawalCellMap

instance : Inj SortStatusCode SortKItem where
  inj
    | SortStatusCode.inj_SortExceptionalStatusCode x => SortKItem.inj_SortExceptionalStatusCode x
    | x => SortKItem.inj_SortStatusCode x

instance : Inj SortSet SortKItem where
  inj := SortKItem.inj_SortSet

instance : Inj SortGeneratedCounterCell SortKItem where
  inj := SortKItem.inj_SortGeneratedCounterCell

instance : Inj SortTxMaxFeeCell SortKItem where
  inj := SortKItem.inj_SortTxMaxFeeCell

instance : Inj SortUseGasCell SortKItem where
  inj := SortKItem.inj_SortUseGasCell

instance : Inj SortAccountCellMap SortKItem where
  inj := SortKItem.inj_SortAccountCellMap

instance : Inj SortKevmCell SortKItem where
  inj := SortKItem.inj_SortKevmCell

instance : Inj SortCodeCell SortKItem where
  inj := SortKItem.inj_SortCodeCell

instance : Inj SortMap SortKItem where
  inj := SortKItem.inj_SortMap

instance : Inj SortScheduleConst SortKItem where
  inj := SortKItem.inj_SortScheduleConst

instance : Inj SortMixHashCell SortKItem where
  inj := SortKItem.inj_SortMixHashCell

instance : Inj SortJumpDestsCell SortKItem where
  inj := SortKItem.inj_SortJumpDestsCell

instance : Inj SortAccessedStorageCell SortKItem where
  inj := SortKItem.inj_SortAccessedStorageCell

instance : Inj SortAccessedAccountsCell SortKItem where
  inj := SortKItem.inj_SortAccessedAccountsCell

instance : Inj SortTxNonceCell SortKItem where
  inj := SortKItem.inj_SortTxNonceCell

instance : Inj SortGasPriceCell SortKItem where
  inj := SortKItem.inj_SortGasPriceCell

instance : Inj SortBlockhashesCell SortKItem where
  inj := SortKItem.inj_SortBlockhashesCell

instance : Inj SortJSON SortKItem where
  inj
    | SortJSON.inj_SortAccount x => SortKItem.inj_SortAccount x
    | SortJSON.inj_SortBool x => SortKItem.inj_SortBool x
    | SortJSON.inj_SortBytes x => SortKItem.inj_SortBytes x
    | SortJSON.inj_SortInt x => SortKItem.inj_SortInt x
    | SortJSON.inj_SortMap x => SortKItem.inj_SortMap x
    | SortJSON.inj_SortTxType x => SortKItem.inj_SortTxType x
    | x => SortKItem.inj_SortJSON x

instance : Inj SortGasLimitCell SortKItem where
  inj := SortKItem.inj_SortGasLimitCell

instance : Inj SortTransactionsRootCell SortKItem where
  inj := SortKItem.inj_SortTransactionsRootCell

instance : Inj SortBlockCell SortKItem where
  inj := SortKItem.inj_SortBlockCell

instance : Inj SortCallValueCell SortKItem where
  inj := SortKItem.inj_SortCallValueCell

instance : Inj SortWithdrawalCell SortKItem where
  inj := SortKItem.inj_SortWithdrawalCell

instance : Inj SortMode SortKItem where
  inj := SortKItem.inj_SortMode

instance : Inj SortEthereumCell SortKItem where
  inj := SortKItem.inj_SortEthereumCell

instance : Inj SortAccountCell SortKItem where
  inj := SortKItem.inj_SortAccountCell

instance : Inj SortGasUsedCell SortKItem where
  inj := SortKItem.inj_SortGasUsedCell

instance : Inj SortNonceCell SortKItem where
  inj := SortKItem.inj_SortNonceCell

instance : Inj SortOriginCell SortKItem where
  inj := SortKItem.inj_SortOriginCell

instance : Inj SortTxPendingCell SortKItem where
  inj := SortKItem.inj_SortTxPendingCell

instance : Inj SortCoinbaseCell SortKItem where
  inj := SortKItem.inj_SortCoinbaseCell

instance : Inj SortPushOp SortKItem where
  inj := SortKItem.inj_SortPushOp

instance : Inj SortAmountCell SortKItem where
  inj := SortKItem.inj_SortAmountCell

instance : Inj SortAddressCell SortKItem where
  inj := SortKItem.inj_SortAddressCell

instance : Inj SortTxGasPriceCell SortKItem where
  inj := SortKItem.inj_SortTxGasPriceCell

instance : Inj SortDifficultyCell SortKItem where
  inj := SortKItem.inj_SortDifficultyCell

instance : Inj SortCallStateCell SortKItem where
  inj := SortKItem.inj_SortCallStateCell

instance : Inj SortMessagesCell SortKItem where
  inj := SortKItem.inj_SortMessagesCell

instance : Inj SortNetworkCell SortKItem where
  inj := SortKItem.inj_SortNetworkCell

instance : Inj SortTxTypeCell SortKItem where
  inj := SortKItem.inj_SortTxTypeCell

instance : Inj SortPreviousHashCell SortKItem where
  inj := SortKItem.inj_SortPreviousHashCell

instance : Inj SortExcessBlobGasCell SortKItem where
  inj := SortKItem.inj_SortExcessBlobGasCell

instance : Inj SortTxGasLimitCell SortKItem where
  inj := SortKItem.inj_SortTxGasLimitCell

instance : Inj SortMaybeOpCode SortKItem where
  inj
    | SortMaybeOpCode.inj_SortBinStackOp x => SortKItem.inj_SortBinStackOp x
    | SortMaybeOpCode.inj_SortInternalOp x => SortKItem.inj_SortInternalOp x
    | SortMaybeOpCode.inj_SortPushOp x => SortKItem.inj_SortPushOp x

instance : Inj SortExitCodeCell SortKItem where
  inj := SortKItem.inj_SortExitCodeCell

instance : Inj SortTxChainIDCell SortKItem where
  inj := SortKItem.inj_SortTxChainIDCell

instance : Inj SortBinStackOp SortKItem where
  inj := SortKItem.inj_SortBinStackOp

instance : Inj SortTxOrderCell SortKItem where
  inj := SortKItem.inj_SortTxOrderCell

instance : Inj SortSelfDestructCell SortKItem where
  inj := SortKItem.inj_SortSelfDestructCell

instance : Inj SortJSONKey SortKItem where
  inj
    | SortJSONKey.inj_SortInt x => SortKItem.inj_SortInt x

instance : Inj SortLocalMemCell SortKItem where
  inj := SortKItem.inj_SortLocalMemCell

instance : Inj SortOmmerBlockHeadersCell SortKItem where
  inj := SortKItem.inj_SortOmmerBlockHeadersCell

instance : Inj SortWordStackCell SortKItem where
  inj := SortKItem.inj_SortWordStackCell

instance : Inj SortWithdrawalsPendingCell SortKItem where
  inj := SortKItem.inj_SortWithdrawalsPendingCell

instance : Inj SortAccountCode SortKItem where
  inj
    | SortAccountCode.inj_SortBytes x => SortKItem.inj_SortBytes x

instance : Inj SortCallStackCell SortKItem where
  inj := SortKItem.inj_SortCallStackCell

instance : Inj SortEvmCell SortKItem where
  inj := SortKItem.inj_SortEvmCell

instance : Inj SortTransientStorageCell SortKItem where
  inj := SortKItem.inj_SortTransientStorageCell

instance : Inj SortWithdrawalIDCell SortKItem where
  inj := SortKItem.inj_SortWithdrawalIDCell

instance : Inj SortCreatedAccountsCell SortKItem where
  inj := SortKItem.inj_SortCreatedAccountsCell

instance : Inj SortInterimStatesCell SortKItem where
  inj := SortKItem.inj_SortInterimStatesCell

instance : Inj SortModeCell SortKItem where
  inj := SortKItem.inj_SortModeCell

instance : Inj SortOmmersHashCell SortKItem where
  inj := SortKItem.inj_SortOmmersHashCell

instance : Inj SortGeneratedTopCell SortKItem where
  inj := SortKItem.inj_SortGeneratedTopCell

instance : Inj SortBytes SortKItem where
  inj := SortKItem.inj_SortBytes

instance : Inj SortList SortKItem where
  inj := SortKItem.inj_SortList

instance : Inj SortSigSCell SortKItem where
  inj := SortKItem.inj_SortSigSCell

instance : Inj SortCallerCell SortKItem where
  inj := SortKItem.inj_SortCallerCell

instance : Inj SortStateRootCell SortKItem where
  inj := SortKItem.inj_SortStateRootCell

instance : Inj SortMessageCell SortKItem where
  inj := SortKItem.inj_SortMessageCell

instance : Inj SortWithdrawalsCell SortKItem where
  inj := SortKItem.inj_SortWithdrawalsCell

instance : Inj SortWithdrawalsRootCell SortKItem where
  inj := SortKItem.inj_SortWithdrawalsRootCell

instance : Inj SortReceiptsRootCell SortKItem where
  inj := SortKItem.inj_SortReceiptsRootCell

instance : Inj SortTxMaxBlobFeeCell SortKItem where
  inj := SortKItem.inj_SortTxMaxBlobFeeCell

instance : Inj SortRefundCell SortKItem where
  inj := SortKItem.inj_SortRefundCell

instance : Inj SortBaseFeeCell SortKItem where
  inj := SortKItem.inj_SortBaseFeeCell

instance : Inj SortCallGasCell SortKItem where
  inj := SortKItem.inj_SortCallGasCell

instance : Inj SortOutputCell SortKItem where
  inj := SortKItem.inj_SortOutputCell

instance : Inj SortIdCell SortKItem where
  inj := SortKItem.inj_SortIdCell

instance : Inj SortBlockNonceCell SortKItem where
  inj := SortKItem.inj_SortBlockNonceCell

instance : Inj SortLogsBloomCell SortKItem where
  inj := SortKItem.inj_SortLogsBloomCell

instance : Inj SortValidatorIndexCell SortKItem where
  inj := SortKItem.inj_SortValidatorIndexCell

instance : Inj SortWordStack SortKItem where
  inj := SortKItem.inj_SortWordStack

instance : Inj SortStatusCodeCell SortKItem where
  inj := SortKItem.inj_SortStatusCodeCell

instance : Inj SortBool SortKItem where
  inj := SortKItem.inj_SortBool

instance : Inj SortSigRCell SortKItem where
  inj := SortKItem.inj_SortSigRCell

instance : Inj SortProgramCell SortKItem where
  inj := SortKItem.inj_SortProgramCell

instance : Inj SortValueCell SortKItem where
  inj := SortKItem.inj_SortValueCell

instance : Inj SortGasCell SortKItem where
  inj := SortKItem.inj_SortGasCell

instance : Inj SortAccount SortKItem where
  inj
    | SortAccount.inj_SortInt x => SortKItem.inj_SortInt x
    | x => SortKItem.inj_SortAccount x

instance : Inj SortTxVersionedHashesCell SortKItem where
  inj := SortKItem.inj_SortTxVersionedHashesCell

instance : Inj SortKCell SortKItem where
  inj := SortKItem.inj_SortKCell

instance : Inj SortToCell SortKItem where
  inj := SortKItem.inj_SortToCell

instance : Inj SortInt SortKItem where
  inj := SortKItem.inj_SortInt

instance : Inj SortIndexCell SortKItem where
  inj := SortKItem.inj_SortIndexCell

instance : Inj SortCallDataCell SortKItem where
  inj := SortKItem.inj_SortCallDataCell

instance : Inj SortTxType SortKItem where
  inj := SortKItem.inj_SortTxType

instance : Inj SortBeaconRootCell SortKItem where
  inj := SortKItem.inj_SortBeaconRootCell

instance : Inj SortAcctIDCell SortKItem where
  inj := SortKItem.inj_SortAcctIDCell

instance : Inj SortPcCell SortKItem where
  inj := SortKItem.inj_SortPcCell

instance : Inj SortTxAccessCell SortKItem where
  inj := SortKItem.inj_SortTxAccessCell

instance : Inj SortInternalOp SortKItem where
  inj := SortKItem.inj_SortInternalOp

instance : Inj SortTouchedAccountsCell SortKItem where
  inj := SortKItem.inj_SortTouchedAccountsCell

instance : Inj SortExceptionalStatusCode SortKItem where
  inj := SortKItem.inj_SortExceptionalStatusCode

instance : Inj SortGas SortKItem where
  inj
    | SortGas.inj_SortInt x => SortKItem.inj_SortInt x

instance : Inj SortStaticCell SortKItem where
  inj := SortKItem.inj_SortStaticCell

instance : Inj SortOrigStorageCell SortKItem where
  inj := SortKItem.inj_SortOrigStorageCell

instance : Inj SortExtraDataCell SortKItem where
  inj := SortKItem.inj_SortExtraDataCell

instance : Inj SortVersionedHashesCell SortKItem where
  inj := SortKItem.inj_SortVersionedHashesCell

instance : Inj SortMemoryUsedCell SortKItem where
  inj := SortKItem.inj_SortMemoryUsedCell

instance : Inj SortScheduleCell SortKItem where
  inj := SortKItem.inj_SortScheduleCell

instance : Inj SortNumberCell SortKItem where
  inj := SortKItem.inj_SortNumberCell

instance : Inj SortTxPriorityFeeCell SortKItem where
  inj := SortKItem.inj_SortTxPriorityFeeCell

instance : Inj SortAccountsCell SortKItem where
  inj := SortKItem.inj_SortAccountsCell

instance : Inj SortStorageCell SortKItem where
  inj := SortKItem.inj_SortStorageCell

instance : Inj SortBalanceCell SortKItem where
  inj := SortKItem.inj_SortBalanceCell

instance : Inj SortMessageCellMap SortKItem where
  inj := SortKItem.inj_SortMessageCellMap

instance : Inj SortJSONs SortKItem where
  inj := SortKItem.inj_SortJSONs

instance : Inj SortDataCell SortKItem where
  inj := SortKItem.inj_SortDataCell

instance : Inj SortInt SortGas where
  inj := SortGas.inj_SortInt

instance : Inj SortBytes SortJSON where
  inj := SortJSON.inj_SortBytes

instance : Inj SortTxType SortJSON where
  inj := SortJSON.inj_SortTxType

instance : Inj SortBool SortJSON where
  inj := SortJSON.inj_SortBool

instance : Inj SortAccount SortJSON where
  inj
    | SortAccount.inj_SortInt x => SortJSON.inj_SortInt x
    | x => SortJSON.inj_SortAccount x

instance : Inj SortMap SortJSON where
  inj := SortJSON.inj_SortMap

instance : Inj SortInt SortJSON where
  inj := SortJSON.inj_SortInt

instance : Inj SortInt SortJSONKey where
  inj := SortJSONKey.inj_SortInt

instance : Inj SortInternalOp SortMaybeOpCode where
  inj := SortMaybeOpCode.inj_SortInternalOp

instance : Inj SortBinStackOp SortMaybeOpCode where
  inj := SortMaybeOpCode.inj_SortBinStackOp

instance : Inj SortPushOp SortMaybeOpCode where
  inj := SortMaybeOpCode.inj_SortPushOp

instance : Inj SortInt SortAccount where
  inj := SortAccount.inj_SortInt

instance : Inj SortBytes SortAccountCode where
  inj := SortAccountCode.inj_SortBytes

instance : Inj SortExceptionalStatusCode SortStatusCode where
  inj := SortStatusCode.inj_SortExceptionalStatusCode
