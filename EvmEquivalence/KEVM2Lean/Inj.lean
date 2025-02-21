import EvmEquivalence.KEVM2Lean.Sorts

instance : Inj SortStateRootCell SortKItem where
  inj := SortKItem.inj_SortStateRootCell

instance : Inj SortMap SortKItem where
  inj := SortKItem.inj_SortMap

instance : Inj SortModeCell SortKItem where
  inj := SortKItem.inj_SortModeCell

instance : Inj SortTxNonceCell SortKItem where
  inj := SortKItem.inj_SortTxNonceCell

instance : Inj SortCallGasCell SortKItem where
  inj := SortKItem.inj_SortCallGasCell

instance : Inj SortNumberCell SortKItem where
  inj := SortKItem.inj_SortNumberCell

instance : Inj SortTxPriorityFeeCell SortKItem where
  inj := SortKItem.inj_SortTxPriorityFeeCell

instance : Inj SortAcctIDCell SortKItem where
  inj := SortKItem.inj_SortAcctIDCell

instance : Inj SortExitCodeCell SortKItem where
  inj := SortKItem.inj_SortExitCodeCell

instance : Inj SortTxMaxBlobFeeCell SortKItem where
  inj := SortKItem.inj_SortTxMaxBlobFeeCell

instance : Inj SortOriginCell SortKItem where
  inj := SortKItem.inj_SortOriginCell

instance : Inj SortCallerCell SortKItem where
  inj := SortKItem.inj_SortCallerCell

instance : Inj SortOmmersHashCell SortKItem where
  inj := SortKItem.inj_SortOmmersHashCell

instance : Inj SortMode SortKItem where
  inj := SortKItem.inj_SortMode

instance : Inj SortInternalOp SortKItem where
  inj := SortKItem.inj_SortInternalOp

instance : Inj SortGasCell SortKItem where
  inj := SortKItem.inj_SortGasCell

instance : Inj SortKevmCell SortKItem where
  inj := SortKItem.inj_SortKevmCell

instance : Inj SortAccountCellMap SortKItem where
  inj := SortKItem.inj_SortAccountCellMap

instance : Inj SortRefundCell SortKItem where
  inj := SortKItem.inj_SortRefundCell

instance : Inj SortCreatedAccountsCell SortKItem where
  inj := SortKItem.inj_SortCreatedAccountsCell

instance : Inj SortBalanceCell SortKItem where
  inj := SortKItem.inj_SortBalanceCell

instance : Inj SortTouchedAccountsCell SortKItem where
  inj := SortKItem.inj_SortTouchedAccountsCell

instance : Inj SortSelfDestructCell SortKItem where
  inj := SortKItem.inj_SortSelfDestructCell

instance : Inj SortExtraDataCell SortKItem where
  inj := SortKItem.inj_SortExtraDataCell

instance : Inj SortLogCell SortKItem where
  inj := SortKItem.inj_SortLogCell

instance : Inj SortCallStateCell SortKItem where
  inj := SortKItem.inj_SortCallStateCell

instance : Inj SortTransactionsRootCell SortKItem where
  inj := SortKItem.inj_SortTransactionsRootCell

instance : Inj SortToCell SortKItem where
  inj := SortKItem.inj_SortToCell

instance : Inj SortGeneratedTopCell SortKItem where
  inj := SortKItem.inj_SortGeneratedTopCell

instance : Inj SortStorageCell SortKItem where
  inj := SortKItem.inj_SortStorageCell

instance : Inj SortBaseFeeCell SortKItem where
  inj := SortKItem.inj_SortBaseFeeCell

instance : Inj SortCodeCell SortKItem where
  inj := SortKItem.inj_SortCodeCell

instance : Inj SortKCell SortKItem where
  inj := SortKItem.inj_SortKCell

instance : Inj SortNetworkCell SortKItem where
  inj := SortKItem.inj_SortNetworkCell

instance : Inj SortGas SortKItem where
  inj
    | SortGas.inj_SortInt x => SortKItem.inj_SortInt x

instance : Inj SortJSONKey SortKItem where
  inj
    | SortJSONKey.inj_SortInt x => SortKItem.inj_SortInt x

instance : Inj SortAccessedStorageCell SortKItem where
  inj := SortKItem.inj_SortAccessedStorageCell

instance : Inj SortTxChainIDCell SortKItem where
  inj := SortKItem.inj_SortTxChainIDCell

instance : Inj SortOrigStorageCell SortKItem where
  inj := SortKItem.inj_SortOrigStorageCell

instance : Inj SortGasLimitCell SortKItem where
  inj := SortKItem.inj_SortGasLimitCell

instance : Inj SortWordStack SortKItem where
  inj := SortKItem.inj_SortWordStack

instance : Inj SortTxPendingCell SortKItem where
  inj := SortKItem.inj_SortTxPendingCell

instance : Inj SortGeneratedCounterCell SortKItem where
  inj := SortKItem.inj_SortGeneratedCounterCell

instance : Inj SortCallDataCell SortKItem where
  inj := SortKItem.inj_SortCallDataCell

instance : Inj SortValueCell SortKItem where
  inj := SortKItem.inj_SortValueCell

instance : Inj SortTxType SortKItem where
  inj := SortKItem.inj_SortTxType

instance : Inj SortScheduleConst SortKItem where
  inj := SortKItem.inj_SortScheduleConst

instance : Inj SortTimestampCell SortKItem where
  inj := SortKItem.inj_SortTimestampCell

instance : Inj SortMessageCellMap SortKItem where
  inj := SortKItem.inj_SortMessageCellMap

instance : Inj SortWordStackCell SortKItem where
  inj := SortKItem.inj_SortWordStackCell

instance : Inj SortProgramCell SortKItem where
  inj := SortKItem.inj_SortProgramCell

instance : Inj SortPcCell SortKItem where
  inj := SortKItem.inj_SortPcCell

instance : Inj SortSigRCell SortKItem where
  inj := SortKItem.inj_SortSigRCell

instance : Inj SortWithdrawalsRootCell SortKItem where
  inj := SortKItem.inj_SortWithdrawalsRootCell

instance : Inj SortReceiptsRootCell SortKItem where
  inj := SortKItem.inj_SortReceiptsRootCell

instance : Inj SortIdCell SortKItem where
  inj := SortKItem.inj_SortIdCell

instance : Inj SortAccountCell SortKItem where
  inj := SortKItem.inj_SortAccountCell

instance : Inj SortJSON SortKItem where
  inj
    | SortJSON.inj_SortAccount x => SortKItem.inj_SortAccount x
    | SortJSON.inj_SortBool x => SortKItem.inj_SortBool x
    | SortJSON.inj_SortBytes x => SortKItem.inj_SortBytes x
    | SortJSON.inj_SortInt x => SortKItem.inj_SortInt x
    | SortJSON.inj_SortMap x => SortKItem.inj_SortMap x
    | SortJSON.inj_SortTxType x => SortKItem.inj_SortTxType x
    | x => SortKItem.inj_SortJSON x

instance : Inj SortAccessedAccountsCell SortKItem where
  inj := SortKItem.inj_SortAccessedAccountsCell

instance : Inj SortCoinbaseCell SortKItem where
  inj := SortKItem.inj_SortCoinbaseCell

instance : Inj SortStatusCode SortKItem where
  inj := SortKItem.inj_SortStatusCode

instance : Inj SortMixHashCell SortKItem where
  inj := SortKItem.inj_SortMixHashCell

instance : Inj SortTxMaxFeeCell SortKItem where
  inj := SortKItem.inj_SortTxMaxFeeCell

instance : Inj SortCallStackCell SortKItem where
  inj := SortKItem.inj_SortCallStackCell

instance : Inj SortTransientStorageCell SortKItem where
  inj := SortKItem.inj_SortTransientStorageCell

instance : Inj SortStaticCell SortKItem where
  inj := SortKItem.inj_SortStaticCell

instance : Inj SortExcessBlobGasCell SortKItem where
  inj := SortKItem.inj_SortExcessBlobGasCell

instance : Inj SortMaybeOpCode SortKItem where
  inj
    | SortMaybeOpCode.inj_SortBinStackOp x => SortKItem.inj_SortBinStackOp x
    | SortMaybeOpCode.inj_SortInternalOp x => SortKItem.inj_SortInternalOp x

instance : Inj SortBlockCell SortKItem where
  inj := SortKItem.inj_SortBlockCell

instance : Inj SortBlockNonceCell SortKItem where
  inj := SortKItem.inj_SortBlockNonceCell

instance : Inj SortTxAccessCell SortKItem where
  inj := SortKItem.inj_SortTxAccessCell

instance : Inj SortBytes SortKItem where
  inj := SortKItem.inj_SortBytes

instance : Inj SortTxGasPriceCell SortKItem where
  inj := SortKItem.inj_SortTxGasPriceCell

instance : Inj SortDifficultyCell SortKItem where
  inj := SortKItem.inj_SortDifficultyCell

instance : Inj SortBeaconRootCell SortKItem where
  inj := SortKItem.inj_SortBeaconRootCell

instance : Inj SortSchedule SortKItem where
  inj := SortKItem.inj_SortSchedule

instance : Inj SortNonceCell SortKItem where
  inj := SortKItem.inj_SortNonceCell

instance : Inj SortOutputCell SortKItem where
  inj := SortKItem.inj_SortOutputCell

instance : Inj SortBlockhashesCell SortKItem where
  inj := SortKItem.inj_SortBlockhashesCell

instance : Inj SortDataCell SortKItem where
  inj := SortKItem.inj_SortDataCell

instance : Inj SortSigVCell SortKItem where
  inj := SortKItem.inj_SortSigVCell

instance : Inj SortEvmCell SortKItem where
  inj := SortKItem.inj_SortEvmCell

instance : Inj SortInt SortKItem where
  inj := SortKItem.inj_SortInt

instance : Inj SortInterimStatesCell SortKItem where
  inj := SortKItem.inj_SortInterimStatesCell

instance : Inj SortChainIDCell SortKItem where
  inj := SortKItem.inj_SortChainIDCell

instance : Inj SortGasUsedCell SortKItem where
  inj := SortKItem.inj_SortGasUsedCell

instance : Inj SortMemoryUsedCell SortKItem where
  inj := SortKItem.inj_SortMemoryUsedCell

instance : Inj SortBool SortKItem where
  inj := SortKItem.inj_SortBool

instance : Inj SortAccountCode SortKItem where
  inj
    | SortAccountCode.inj_SortBytes x => SortKItem.inj_SortBytes x

instance : Inj SortTxOrderCell SortKItem where
  inj := SortKItem.inj_SortTxOrderCell

instance : Inj SortList SortKItem where
  inj := SortKItem.inj_SortList

instance : Inj SortSubstateCell SortKItem where
  inj := SortKItem.inj_SortSubstateCell

instance : Inj SortScheduleCell SortKItem where
  inj := SortKItem.inj_SortScheduleCell

instance : Inj SortTxGasLimitCell SortKItem where
  inj := SortKItem.inj_SortTxGasLimitCell

instance : Inj SortLogsBloomCell SortKItem where
  inj := SortKItem.inj_SortLogsBloomCell

instance : Inj SortMsgIDCell SortKItem where
  inj := SortKItem.inj_SortMsgIDCell

instance : Inj SortMessageCell SortKItem where
  inj := SortKItem.inj_SortMessageCell

instance : Inj SortGasPriceCell SortKItem where
  inj := SortKItem.inj_SortGasPriceCell

instance : Inj SortAccountsCell SortKItem where
  inj := SortKItem.inj_SortAccountsCell

instance : Inj SortAccount SortKItem where
  inj
    | SortAccount.inj_SortInt x => SortKItem.inj_SortInt x
    | x => SortKItem.inj_SortAccount x

instance : Inj SortCallValueCell SortKItem where
  inj := SortKItem.inj_SortCallValueCell

instance : Inj SortCallDepthCell SortKItem where
  inj := SortKItem.inj_SortCallDepthCell

instance : Inj SortTxVersionedHashesCell SortKItem where
  inj := SortKItem.inj_SortTxVersionedHashesCell

instance : Inj SortStatusCodeCell SortKItem where
  inj := SortKItem.inj_SortStatusCodeCell

instance : Inj SortBlobGasUsedCell SortKItem where
  inj := SortKItem.inj_SortBlobGasUsedCell

instance : Inj SortJSONs SortKItem where
  inj := SortKItem.inj_SortJSONs

instance : Inj SortLocalMemCell SortKItem where
  inj := SortKItem.inj_SortLocalMemCell

instance : Inj SortMessagesCell SortKItem where
  inj := SortKItem.inj_SortMessagesCell

instance : Inj SortEthereumCell SortKItem where
  inj := SortKItem.inj_SortEthereumCell

instance : Inj SortBinStackOp SortKItem where
  inj := SortKItem.inj_SortBinStackOp

instance : Inj SortTxTypeCell SortKItem where
  inj := SortKItem.inj_SortTxTypeCell

instance : Inj SortJumpDestsCell SortKItem where
  inj := SortKItem.inj_SortJumpDestsCell

instance : Inj SortSigSCell SortKItem where
  inj := SortKItem.inj_SortSigSCell

instance : Inj SortSet SortKItem where
  inj := SortKItem.inj_SortSet

instance : Inj SortPreviousHashCell SortKItem where
  inj := SortKItem.inj_SortPreviousHashCell

instance : Inj SortUseGasCell SortKItem where
  inj := SortKItem.inj_SortUseGasCell

instance : Inj SortOmmerBlockHeadersCell SortKItem where
  inj := SortKItem.inj_SortOmmerBlockHeadersCell

instance : Inj SortInt SortGas where
  inj := SortGas.inj_SortInt

instance : Inj SortAccount SortJSON where
  inj
    | SortAccount.inj_SortInt x => SortJSON.inj_SortInt x
    | x => SortJSON.inj_SortAccount x

instance : Inj SortInt SortJSON where
  inj := SortJSON.inj_SortInt

instance : Inj SortMap SortJSON where
  inj := SortJSON.inj_SortMap

instance : Inj SortTxType SortJSON where
  inj := SortJSON.inj_SortTxType

instance : Inj SortBytes SortJSON where
  inj := SortJSON.inj_SortBytes

instance : Inj SortBool SortJSON where
  inj := SortJSON.inj_SortBool

instance : Inj SortInt SortJSONKey where
  inj := SortJSONKey.inj_SortInt

instance : Inj SortBinStackOp SortMaybeOpCode where
  inj := SortMaybeOpCode.inj_SortBinStackOp

instance : Inj SortInternalOp SortMaybeOpCode where
  inj := SortMaybeOpCode.inj_SortInternalOp

instance : Inj SortInt SortAccount where
  inj := SortAccount.inj_SortInt

instance : Inj SortBytes SortAccountCode where
  inj := SortAccountCode.inj_SortBytes
