import EvmEquivalence.KEVM2Lean.Sorts

instance : Inj SortScheduleConst SortKItem where
  inj := SortKItem.inj_SortScheduleConst
  retr
    | SortKItem.inj_SortScheduleConst x => some x
    | _ => none

instance : Inj SortMaybeOpCode SortKItem where
  inj
    | SortMaybeOpCode.inj_SortBinStackOp x => SortKItem.inj_SortBinStackOp x
    | SortMaybeOpCode.inj_SortInternalOp x => SortKItem.inj_SortInternalOp x
    | SortMaybeOpCode.inj_SortNullStackOp x => SortKItem.inj_SortNullStackOp x
    | SortMaybeOpCode.inj_SortPushOp x => SortKItem.inj_SortPushOp x
    | SortMaybeOpCode.inj_SortTernStackOp x => SortKItem.inj_SortTernStackOp x
    | SortMaybeOpCode.inj_SortUnStackOp x => SortKItem.inj_SortUnStackOp x
  retr
    | SortKItem.inj_SortBinStackOp x => some (SortMaybeOpCode.inj_SortBinStackOp x)
    | SortKItem.inj_SortInternalOp x => some (SortMaybeOpCode.inj_SortInternalOp x)
    | SortKItem.inj_SortNullStackOp x => some (SortMaybeOpCode.inj_SortNullStackOp x)
    | SortKItem.inj_SortPushOp x => some (SortMaybeOpCode.inj_SortPushOp x)
    | SortKItem.inj_SortTernStackOp x => some (SortMaybeOpCode.inj_SortTernStackOp x)
    | SortKItem.inj_SortUnStackOp x => some (SortMaybeOpCode.inj_SortUnStackOp x)
    | SortKItem.inj_SortMaybeOpCode x => some x
    | _ => none

instance : Inj SortPushOp SortKItem where
  inj := SortKItem.inj_SortPushOp
  retr
    | SortKItem.inj_SortPushOp x => some x
    | _ => none

instance : Inj SortAmountCell SortKItem where
  inj := SortKItem.inj_SortAmountCell
  retr
    | SortKItem.inj_SortAmountCell x => some x
    | _ => none

instance : Inj SortGasCell SortKItem where
  inj := SortKItem.inj_SortGasCell
  retr
    | SortKItem.inj_SortGasCell x => some x
    | _ => none

instance : Inj SortJSONs SortKItem where
  inj := SortKItem.inj_SortJSONs
  retr
    | SortKItem.inj_SortJSONs x => some x
    | _ => none

instance : Inj SortTimestampCell SortKItem where
  inj := SortKItem.inj_SortTimestampCell
  retr
    | SortKItem.inj_SortTimestampCell x => some x
    | _ => none

instance : Inj SortBlockhashesCell SortKItem where
  inj := SortKItem.inj_SortBlockhashesCell
  retr
    | SortKItem.inj_SortBlockhashesCell x => some x
    | _ => none

instance : Inj SortEvmCell SortKItem where
  inj := SortKItem.inj_SortEvmCell
  retr
    | SortKItem.inj_SortEvmCell x => some x
    | _ => none

instance : Inj SortWithdrawalsOrderCell SortKItem where
  inj := SortKItem.inj_SortWithdrawalsOrderCell
  retr
    | SortKItem.inj_SortWithdrawalsOrderCell x => some x
    | _ => none

instance : Inj SortTxGasPriceCell SortKItem where
  inj := SortKItem.inj_SortTxGasPriceCell
  retr
    | SortKItem.inj_SortTxGasPriceCell x => some x
    | _ => none

instance : Inj SortStatusCode SortKItem where
  inj := SortKItem.inj_SortStatusCode
  retr
    | SortKItem.inj_SortStatusCode x => some x
    | _ => none

instance : Inj SortInterimStatesCell SortKItem where
  inj := SortKItem.inj_SortInterimStatesCell
  retr
    | SortKItem.inj_SortInterimStatesCell x => some x
    | _ => none

instance : Inj SortWithdrawalsRootCell SortKItem where
  inj := SortKItem.inj_SortWithdrawalsRootCell
  retr
    | SortKItem.inj_SortWithdrawalsRootCell x => some x
    | _ => none

instance : Inj SortTxPendingCell SortKItem where
  inj := SortKItem.inj_SortTxPendingCell
  retr
    | SortKItem.inj_SortTxPendingCell x => some x
    | _ => none

instance : Inj SortAccountsCell SortKItem where
  inj := SortKItem.inj_SortAccountsCell
  retr
    | SortKItem.inj_SortAccountsCell x => some x
    | _ => none

instance : Inj SortNullStackOp SortKItem where
  inj := SortKItem.inj_SortNullStackOp
  retr
    | SortKItem.inj_SortNullStackOp x => some x
    | _ => none

instance : Inj SortCallStateCell SortKItem where
  inj := SortKItem.inj_SortCallStateCell
  retr
    | SortKItem.inj_SortCallStateCell x => some x
    | _ => none

instance : Inj SortInt SortKItem where
  inj := SortKItem.inj_SortInt
  retr
    | SortKItem.inj_SortInt x => some x
    | _ => none

instance : Inj SortLogCell SortKItem where
  inj := SortKItem.inj_SortLogCell
  retr
    | SortKItem.inj_SortLogCell x => some x
    | _ => none

instance : Inj SortUnStackOp SortKItem where
  inj := SortKItem.inj_SortUnStackOp
  retr
    | SortKItem.inj_SortUnStackOp x => some x
    | _ => none

instance : Inj SortCallDataCell SortKItem where
  inj := SortKItem.inj_SortCallDataCell
  retr
    | SortKItem.inj_SortCallDataCell x => some x
    | _ => none

instance : Inj SortMixHashCell SortKItem where
  inj := SortKItem.inj_SortMixHashCell
  retr
    | SortKItem.inj_SortMixHashCell x => some x
    | _ => none

instance : Inj SortGeneratedCounterCell SortKItem where
  inj := SortKItem.inj_SortGeneratedCounterCell
  retr
    | SortKItem.inj_SortGeneratedCounterCell x => some x
    | _ => none

instance : Inj SortMode SortKItem where
  inj := SortKItem.inj_SortMode
  retr
    | SortKItem.inj_SortMode x => some x
    | _ => none

instance : Inj SortSignedness SortKItem where
  inj := SortKItem.inj_SortSignedness
  retr
    | SortKItem.inj_SortSignedness x => some x
    | _ => none

instance : Inj SortJumpDestsCell SortKItem where
  inj := SortKItem.inj_SortJumpDestsCell
  retr
    | SortKItem.inj_SortJumpDestsCell x => some x
    | _ => none

instance : Inj SortMsgIDCell SortKItem where
  inj := SortKItem.inj_SortMsgIDCell
  retr
    | SortKItem.inj_SortMsgIDCell x => some x
    | _ => none

instance : Inj SortGasPriceCell SortKItem where
  inj := SortKItem.inj_SortGasPriceCell
  retr
    | SortKItem.inj_SortGasPriceCell x => some x
    | _ => none

instance : Inj SortStorageCell SortKItem where
  inj := SortKItem.inj_SortStorageCell
  retr
    | SortKItem.inj_SortStorageCell x => some x
    | _ => none

instance : Inj SortLocalMemCell SortKItem where
  inj := SortKItem.inj_SortLocalMemCell
  retr
    | SortKItem.inj_SortLocalMemCell x => some x
    | _ => none

instance : Inj SortMessagesCell SortKItem where
  inj := SortKItem.inj_SortMessagesCell
  retr
    | SortKItem.inj_SortMessagesCell x => some x
    | _ => none

instance : Inj SortTxChainIDCell SortKItem where
  inj := SortKItem.inj_SortTxChainIDCell
  retr
    | SortKItem.inj_SortTxChainIDCell x => some x
    | _ => none

instance : Inj SortAccount SortKItem where
  inj
    | SortAccount.inj_SortInt x => SortKItem.inj_SortInt x
    | x => SortKItem.inj_SortAccount x
  retr
    | SortKItem.inj_SortInt x => some (SortAccount.inj_SortInt x)
    | SortKItem.inj_SortAccount x => some x
    | _ => none

instance : Inj SortBinStackOp SortKItem where
  inj := SortKItem.inj_SortBinStackOp
  retr
    | SortKItem.inj_SortBinStackOp x => some x
    | _ => none

instance : Inj SortEndianness SortKItem where
  inj := SortKItem.inj_SortEndianness
  retr
    | SortKItem.inj_SortEndianness x => some x
    | _ => none

instance : Inj SortStaticCell SortKItem where
  inj := SortKItem.inj_SortStaticCell
  retr
    | SortKItem.inj_SortStaticCell x => some x
    | _ => none

instance : Inj SortTxMaxFeeCell SortKItem where
  inj := SortKItem.inj_SortTxMaxFeeCell
  retr
    | SortKItem.inj_SortTxMaxFeeCell x => some x
    | _ => none

instance : Inj SortKevmCell SortKItem where
  inj := SortKItem.inj_SortKevmCell
  retr
    | SortKItem.inj_SortKevmCell x => some x
    | _ => none

instance : Inj SortTxAccessCell SortKItem where
  inj := SortKItem.inj_SortTxAccessCell
  retr
    | SortKItem.inj_SortTxAccessCell x => some x
    | _ => none

instance : Inj SortMessageCellMap SortKItem where
  inj := SortKItem.inj_SortMessageCellMap
  retr
    | SortKItem.inj_SortMessageCellMap x => some x
    | _ => none

instance : Inj SortBlockNonceCell SortKItem where
  inj := SortKItem.inj_SortBlockNonceCell
  retr
    | SortKItem.inj_SortBlockNonceCell x => some x
    | _ => none

instance : Inj SortToCell SortKItem where
  inj := SortKItem.inj_SortToCell
  retr
    | SortKItem.inj_SortToCell x => some x
    | _ => none

instance : Inj SortExitCodeCell SortKItem where
  inj := SortKItem.inj_SortExitCodeCell
  retr
    | SortKItem.inj_SortExitCodeCell x => some x
    | _ => none

instance : Inj SortIndexCell SortKItem where
  inj := SortKItem.inj_SortIndexCell
  retr
    | SortKItem.inj_SortIndexCell x => some x
    | _ => none

instance : Inj SortKCell SortKItem where
  inj := SortKItem.inj_SortKCell
  retr
    | SortKItem.inj_SortKCell x => some x
    | _ => none

instance : Inj SortMap SortKItem where
  inj := SortKItem.inj_SortMap
  retr
    | SortKItem.inj_SortMap x => some x
    | _ => none

instance : Inj SortBalanceCell SortKItem where
  inj := SortKItem.inj_SortBalanceCell
  retr
    | SortKItem.inj_SortBalanceCell x => some x
    | _ => none

instance : Inj SortScheduleCell SortKItem where
  inj := SortKItem.inj_SortScheduleCell
  retr
    | SortKItem.inj_SortScheduleCell x => some x
    | _ => none

instance : Inj SortValidatorIndexCell SortKItem where
  inj := SortKItem.inj_SortValidatorIndexCell
  retr
    | SortKItem.inj_SortValidatorIndexCell x => some x
    | _ => none

instance : Inj SortSet SortKItem where
  inj := SortKItem.inj_SortSet
  retr
    | SortKItem.inj_SortSet x => some x
    | _ => none

instance : Inj SortCallStackCell SortKItem where
  inj := SortKItem.inj_SortCallStackCell
  retr
    | SortKItem.inj_SortCallStackCell x => some x
    | _ => none

instance : Inj SortSubstateCell SortKItem where
  inj := SortKItem.inj_SortSubstateCell
  retr
    | SortKItem.inj_SortSubstateCell x => some x
    | _ => none

instance : Inj SortSigRCell SortKItem where
  inj := SortKItem.inj_SortSigRCell
  retr
    | SortKItem.inj_SortSigRCell x => some x
    | _ => none

instance : Inj SortTxTypeCell SortKItem where
  inj := SortKItem.inj_SortTxTypeCell
  retr
    | SortKItem.inj_SortTxTypeCell x => some x
    | _ => none

instance : Inj SortOutputCell SortKItem where
  inj := SortKItem.inj_SortOutputCell
  retr
    | SortKItem.inj_SortOutputCell x => some x
    | _ => none

instance : Inj SortDataCell SortKItem where
  inj := SortKItem.inj_SortDataCell
  retr
    | SortKItem.inj_SortDataCell x => some x
    | _ => none

instance : Inj SortCallGasCell SortKItem where
  inj := SortKItem.inj_SortCallGasCell
  retr
    | SortKItem.inj_SortCallGasCell x => some x
    | _ => none

instance : Inj SortTernStackOp SortKItem where
  inj := SortKItem.inj_SortTernStackOp
  retr
    | SortKItem.inj_SortTernStackOp x => some x
    | _ => none

instance : Inj SortExcessBlobGasCell SortKItem where
  inj := SortKItem.inj_SortExcessBlobGasCell
  retr
    | SortKItem.inj_SortExcessBlobGasCell x => some x
    | _ => none

instance : Inj SortBool SortKItem where
  inj := SortKItem.inj_SortBool
  retr
    | SortKItem.inj_SortBool x => some x
    | _ => none

instance : Inj SortBeaconRootCell SortKItem where
  inj := SortKItem.inj_SortBeaconRootCell
  retr
    | SortKItem.inj_SortBeaconRootCell x => some x
    | _ => none

instance : Inj SortGeneratedTopCell SortKItem where
  inj := SortKItem.inj_SortGeneratedTopCell
  retr
    | SortKItem.inj_SortGeneratedTopCell x => some x
    | _ => none

instance : Inj SortNonceCell SortKItem where
  inj := SortKItem.inj_SortNonceCell
  retr
    | SortKItem.inj_SortNonceCell x => some x
    | _ => none

instance : Inj SortOmmersHashCell SortKItem where
  inj := SortKItem.inj_SortOmmersHashCell
  retr
    | SortKItem.inj_SortOmmersHashCell x => some x
    | _ => none

instance : Inj SortNumberCell SortKItem where
  inj := SortKItem.inj_SortNumberCell
  retr
    | SortKItem.inj_SortNumberCell x => some x
    | _ => none

instance : Inj SortBlockCell SortKItem where
  inj := SortKItem.inj_SortBlockCell
  retr
    | SortKItem.inj_SortBlockCell x => some x
    | _ => none

instance : Inj SortBlobGasUsedCell SortKItem where
  inj := SortKItem.inj_SortBlobGasUsedCell
  retr
    | SortKItem.inj_SortBlobGasUsedCell x => some x
    | _ => none

instance : Inj SortCallDepthCell SortKItem where
  inj := SortKItem.inj_SortCallDepthCell
  retr
    | SortKItem.inj_SortCallDepthCell x => some x
    | _ => none

instance : Inj SortTxNonceCell SortKItem where
  inj := SortKItem.inj_SortTxNonceCell
  retr
    | SortKItem.inj_SortTxNonceCell x => some x
    | _ => none

instance : Inj SortTxMaxBlobFeeCell SortKItem where
  inj := SortKItem.inj_SortTxMaxBlobFeeCell
  retr
    | SortKItem.inj_SortTxMaxBlobFeeCell x => some x
    | _ => none

instance : Inj SortSelfDestructCell SortKItem where
  inj := SortKItem.inj_SortSelfDestructCell
  retr
    | SortKItem.inj_SortSelfDestructCell x => some x
    | _ => none

instance : Inj SortJSON SortKItem where
  inj
    | SortJSON.inj_SortAccount x => SortKItem.inj_SortAccount x
    | SortJSON.inj_SortBool x => SortKItem.inj_SortBool x
    | SortJSON.inj_SortBytes x => SortKItem.inj_SortBytes x
    | SortJSON.inj_SortInt x => SortKItem.inj_SortInt x
    | SortJSON.inj_SortMap x => SortKItem.inj_SortMap x
    | SortJSON.inj_SortTxType x => SortKItem.inj_SortTxType x
    | x => SortKItem.inj_SortJSON x
  retr
    | SortKItem.inj_SortAccount x => some (SortJSON.inj_SortAccount x)
    | SortKItem.inj_SortBool x => some (SortJSON.inj_SortBool x)
    | SortKItem.inj_SortBytes x => some (SortJSON.inj_SortBytes x)
    | SortKItem.inj_SortInt x => some (SortJSON.inj_SortInt x)
    | SortKItem.inj_SortMap x => some (SortJSON.inj_SortMap x)
    | SortKItem.inj_SortTxType x => some (SortJSON.inj_SortTxType x)
    | SortKItem.inj_SortJSON x => some x
    | _ => none

instance : Inj SortAccountCell SortKItem where
  inj := SortKItem.inj_SortAccountCell
  retr
    | SortKItem.inj_SortAccountCell x => some x
    | _ => none

instance : Inj SortStateRootCell SortKItem where
  inj := SortKItem.inj_SortStateRootCell
  retr
    | SortKItem.inj_SortStateRootCell x => some x
    | _ => none

instance : Inj SortWithdrawalCell SortKItem where
  inj := SortKItem.inj_SortWithdrawalCell
  retr
    | SortKItem.inj_SortWithdrawalCell x => some x
    | _ => none

instance : Inj SortGasUsedCell SortKItem where
  inj := SortKItem.inj_SortGasUsedCell
  retr
    | SortKItem.inj_SortGasUsedCell x => some x
    | _ => none

instance : Inj SortCodeCell SortKItem where
  inj := SortKItem.inj_SortCodeCell
  retr
    | SortKItem.inj_SortCodeCell x => some x
    | _ => none

instance : Inj SortTransientStorageCell SortKItem where
  inj := SortKItem.inj_SortTransientStorageCell
  retr
    | SortKItem.inj_SortTransientStorageCell x => some x
    | _ => none

instance : Inj SortPcCell SortKItem where
  inj := SortKItem.inj_SortPcCell
  retr
    | SortKItem.inj_SortPcCell x => some x
    | _ => none

instance : Inj SortAccessedAccountsCell SortKItem where
  inj := SortKItem.inj_SortAccessedAccountsCell
  retr
    | SortKItem.inj_SortAccessedAccountsCell x => some x
    | _ => none

instance : Inj SortCoinbaseCell SortKItem where
  inj := SortKItem.inj_SortCoinbaseCell
  retr
    | SortKItem.inj_SortCoinbaseCell x => some x
    | _ => none

instance : Inj SortScheduleFlag SortKItem where
  inj := SortKItem.inj_SortScheduleFlag
  retr
    | SortKItem.inj_SortScheduleFlag x => some x
    | _ => none

instance : Inj SortAddressCell SortKItem where
  inj := SortKItem.inj_SortAddressCell
  retr
    | SortKItem.inj_SortAddressCell x => some x
    | _ => none

instance : Inj SortPreviousHashCell SortKItem where
  inj := SortKItem.inj_SortPreviousHashCell
  retr
    | SortKItem.inj_SortPreviousHashCell x => some x
    | _ => none

instance : Inj SortBaseFeeCell SortKItem where
  inj := SortKItem.inj_SortBaseFeeCell
  retr
    | SortKItem.inj_SortBaseFeeCell x => some x
    | _ => none

instance : Inj SortTransactionsRootCell SortKItem where
  inj := SortKItem.inj_SortTransactionsRootCell
  retr
    | SortKItem.inj_SortTransactionsRootCell x => some x
    | _ => none

instance : Inj SortEthereumCell SortKItem where
  inj := SortKItem.inj_SortEthereumCell
  retr
    | SortKItem.inj_SortEthereumCell x => some x
    | _ => none

instance : Inj SortDifficultyCell SortKItem where
  inj := SortKItem.inj_SortDifficultyCell
  retr
    | SortKItem.inj_SortDifficultyCell x => some x
    | _ => none

instance : Inj SortList SortKItem where
  inj := SortKItem.inj_SortList
  retr
    | SortKItem.inj_SortList x => some x
    | _ => none

instance : Inj SortWithdrawalsPendingCell SortKItem where
  inj := SortKItem.inj_SortWithdrawalsPendingCell
  retr
    | SortKItem.inj_SortWithdrawalsPendingCell x => some x
    | _ => none

instance : Inj SortSigSCell SortKItem where
  inj := SortKItem.inj_SortSigSCell
  retr
    | SortKItem.inj_SortSigSCell x => some x
    | _ => none

instance : Inj SortSigVCell SortKItem where
  inj := SortKItem.inj_SortSigVCell
  retr
    | SortKItem.inj_SortSigVCell x => some x
    | _ => none

instance : Inj SortAcctIDCell SortKItem where
  inj := SortKItem.inj_SortAcctIDCell
  retr
    | SortKItem.inj_SortAcctIDCell x => some x
    | _ => none

instance : Inj SortWithdrawalsCell SortKItem where
  inj := SortKItem.inj_SortWithdrawalsCell
  retr
    | SortKItem.inj_SortWithdrawalsCell x => some x
    | _ => none

instance : Inj SortUseGasCell SortKItem where
  inj := SortKItem.inj_SortUseGasCell
  retr
    | SortKItem.inj_SortUseGasCell x => some x
    | _ => none

instance : Inj SortLogsBloomCell SortKItem where
  inj := SortKItem.inj_SortLogsBloomCell
  retr
    | SortKItem.inj_SortLogsBloomCell x => some x
    | _ => none

instance : Inj SortMemoryUsedCell SortKItem where
  inj := SortKItem.inj_SortMemoryUsedCell
  retr
    | SortKItem.inj_SortMemoryUsedCell x => some x
    | _ => none

instance : Inj SortInternalOp SortKItem where
  inj := SortKItem.inj_SortInternalOp
  retr
    | SortKItem.inj_SortInternalOp x => some x
    | _ => none

instance : Inj SortTxPriorityFeeCell SortKItem where
  inj := SortKItem.inj_SortTxPriorityFeeCell
  retr
    | SortKItem.inj_SortTxPriorityFeeCell x => some x
    | _ => none

instance : Inj SortTxOrderCell SortKItem where
  inj := SortKItem.inj_SortTxOrderCell
  retr
    | SortKItem.inj_SortTxOrderCell x => some x
    | _ => none

instance : Inj SortNetworkCell SortKItem where
  inj := SortKItem.inj_SortNetworkCell
  retr
    | SortKItem.inj_SortNetworkCell x => some x
    | _ => none

instance : Inj SortOmmerBlockHeadersCell SortKItem where
  inj := SortKItem.inj_SortOmmerBlockHeadersCell
  retr
    | SortKItem.inj_SortOmmerBlockHeadersCell x => some x
    | _ => none

instance : Inj SortValueCell SortKItem where
  inj := SortKItem.inj_SortValueCell
  retr
    | SortKItem.inj_SortValueCell x => some x
    | _ => none

instance : Inj SortCreatedAccountsCell SortKItem where
  inj := SortKItem.inj_SortCreatedAccountsCell
  retr
    | SortKItem.inj_SortCreatedAccountsCell x => some x
    | _ => none

instance : Inj SortOriginCell SortKItem where
  inj := SortKItem.inj_SortOriginCell
  retr
    | SortKItem.inj_SortOriginCell x => some x
    | _ => none

instance : Inj SortAccountCellMap SortKItem where
  inj := SortKItem.inj_SortAccountCellMap
  retr
    | SortKItem.inj_SortAccountCellMap x => some x
    | _ => none

instance : Inj SortReceiptsRootCell SortKItem where
  inj := SortKItem.inj_SortReceiptsRootCell
  retr
    | SortKItem.inj_SortReceiptsRootCell x => some x
    | _ => none

instance : Inj SortAccountCode SortKItem where
  inj
    | SortAccountCode.inj_SortBytes x => SortKItem.inj_SortBytes x
  retr
    | SortKItem.inj_SortBytes x => some (SortAccountCode.inj_SortBytes x)
    | SortKItem.inj_SortAccountCode x => some x
    | _ => none

instance : Inj SortSchedule SortKItem where
  inj := SortKItem.inj_SortSchedule
  retr
    | SortKItem.inj_SortSchedule x => some x
    | _ => none

instance : Inj SortOrigStorageCell SortKItem where
  inj := SortKItem.inj_SortOrigStorageCell
  retr
    | SortKItem.inj_SortOrigStorageCell x => some x
    | _ => none

instance : Inj SortProgramCell SortKItem where
  inj := SortKItem.inj_SortProgramCell
  retr
    | SortKItem.inj_SortProgramCell x => some x
    | _ => none

instance : Inj SortVersionedHashesCell SortKItem where
  inj := SortKItem.inj_SortVersionedHashesCell
  retr
    | SortKItem.inj_SortVersionedHashesCell x => some x
    | _ => none

instance : Inj SortChainIDCell SortKItem where
  inj := SortKItem.inj_SortChainIDCell
  retr
    | SortKItem.inj_SortChainIDCell x => some x
    | _ => none

instance : Inj SortIdCell SortKItem where
  inj := SortKItem.inj_SortIdCell
  retr
    | SortKItem.inj_SortIdCell x => some x
    | _ => none

instance : Inj SortMessageCell SortKItem where
  inj := SortKItem.inj_SortMessageCell
  retr
    | SortKItem.inj_SortMessageCell x => some x
    | _ => none

instance : Inj SortTxGasLimitCell SortKItem where
  inj := SortKItem.inj_SortTxGasLimitCell
  retr
    | SortKItem.inj_SortTxGasLimitCell x => some x
    | _ => none

instance : Inj SortCallerCell SortKItem where
  inj := SortKItem.inj_SortCallerCell
  retr
    | SortKItem.inj_SortCallerCell x => some x
    | _ => none

instance : Inj SortWordStack SortKItem where
  inj := SortKItem.inj_SortWordStack
  retr
    | SortKItem.inj_SortWordStack x => some x
    | _ => none

instance : Inj SortExtraDataCell SortKItem where
  inj := SortKItem.inj_SortExtraDataCell
  retr
    | SortKItem.inj_SortExtraDataCell x => some x
    | _ => none

instance : Inj SortTxVersionedHashesCell SortKItem where
  inj := SortKItem.inj_SortTxVersionedHashesCell
  retr
    | SortKItem.inj_SortTxVersionedHashesCell x => some x
    | _ => none

instance : Inj SortGas SortKItem where
  inj
    | SortGas.inj_SortInt x => SortKItem.inj_SortInt x
  retr
    | SortKItem.inj_SortInt x => some (SortGas.inj_SortInt x)
    | SortKItem.inj_SortGas x => some x
    | _ => none

instance : Inj SortBytes SortKItem where
  inj := SortKItem.inj_SortBytes
  retr
    | SortKItem.inj_SortBytes x => some x
    | _ => none

instance : Inj SortWithdrawalIDCell SortKItem where
  inj := SortKItem.inj_SortWithdrawalIDCell
  retr
    | SortKItem.inj_SortWithdrawalIDCell x => some x
    | _ => none

instance : Inj SortWordStackCell SortKItem where
  inj := SortKItem.inj_SortWordStackCell
  retr
    | SortKItem.inj_SortWordStackCell x => some x
    | _ => none

instance : Inj SortGasLimitCell SortKItem where
  inj := SortKItem.inj_SortGasLimitCell
  retr
    | SortKItem.inj_SortGasLimitCell x => some x
    | _ => none

instance : Inj SortStatusCodeCell SortKItem where
  inj := SortKItem.inj_SortStatusCodeCell
  retr
    | SortKItem.inj_SortStatusCodeCell x => some x
    | _ => none

instance : Inj SortCallValueCell SortKItem where
  inj := SortKItem.inj_SortCallValueCell
  retr
    | SortKItem.inj_SortCallValueCell x => some x
    | _ => none

instance : Inj SortModeCell SortKItem where
  inj := SortKItem.inj_SortModeCell
  retr
    | SortKItem.inj_SortModeCell x => some x
    | _ => none

instance : Inj SortTxType SortKItem where
  inj := SortKItem.inj_SortTxType
  retr
    | SortKItem.inj_SortTxType x => some x
    | _ => none

instance : Inj SortRefundCell SortKItem where
  inj := SortKItem.inj_SortRefundCell
  retr
    | SortKItem.inj_SortRefundCell x => some x
    | _ => none

instance : Inj SortJSONKey SortKItem where
  inj
    | SortJSONKey.inj_SortInt x => SortKItem.inj_SortInt x
  retr
    | SortKItem.inj_SortInt x => some (SortJSONKey.inj_SortInt x)
    | SortKItem.inj_SortJSONKey x => some x
    | _ => none

instance : Inj SortTouchedAccountsCell SortKItem where
  inj := SortKItem.inj_SortTouchedAccountsCell
  retr
    | SortKItem.inj_SortTouchedAccountsCell x => some x
    | _ => none

instance : Inj SortWithdrawalCellMap SortKItem where
  inj := SortKItem.inj_SortWithdrawalCellMap
  retr
    | SortKItem.inj_SortWithdrawalCellMap x => some x
    | _ => none

instance : Inj SortAccessedStorageCell SortKItem where
  inj := SortKItem.inj_SortAccessedStorageCell
  retr
    | SortKItem.inj_SortAccessedStorageCell x => some x
    | _ => none

instance : Inj SortInt SortGas where
  inj := SortGas.inj_SortInt
  retr
    | SortGas.inj_SortInt x => some x

instance : Inj SortTxType SortJSON where
  inj := SortJSON.inj_SortTxType
  retr
    | SortJSON.inj_SortTxType x => some x
    | _ => none

instance : Inj SortInt SortJSON where
  inj := SortJSON.inj_SortInt
  retr
    | SortJSON.inj_SortInt x => some x
    | _ => none

instance : Inj SortAccount SortJSON where
  inj
    | SortAccount.inj_SortInt x => SortJSON.inj_SortInt x
    | x => SortJSON.inj_SortAccount x
  retr
    | SortJSON.inj_SortInt x => some (SortAccount.inj_SortInt x)
    | SortJSON.inj_SortAccount x => some x
    | _ => none

instance : Inj SortBytes SortJSON where
  inj := SortJSON.inj_SortBytes
  retr
    | SortJSON.inj_SortBytes x => some x
    | _ => none

instance : Inj SortBool SortJSON where
  inj := SortJSON.inj_SortBool
  retr
    | SortJSON.inj_SortBool x => some x
    | _ => none

instance : Inj SortMap SortJSON where
  inj := SortJSON.inj_SortMap
  retr
    | SortJSON.inj_SortMap x => some x
    | _ => none

instance : Inj SortInt SortJSONKey where
  inj := SortJSONKey.inj_SortInt
  retr
    | SortJSONKey.inj_SortInt x => some x

instance : Inj SortPushOp SortMaybeOpCode where
  inj := SortMaybeOpCode.inj_SortPushOp
  retr
    | SortMaybeOpCode.inj_SortPushOp x => some x
    | _ => none

instance : Inj SortInternalOp SortMaybeOpCode where
  inj := SortMaybeOpCode.inj_SortInternalOp
  retr
    | SortMaybeOpCode.inj_SortInternalOp x => some x
    | _ => none

instance : Inj SortTernStackOp SortMaybeOpCode where
  inj := SortMaybeOpCode.inj_SortTernStackOp
  retr
    | SortMaybeOpCode.inj_SortTernStackOp x => some x
    | _ => none

instance : Inj SortNullStackOp SortMaybeOpCode where
  inj := SortMaybeOpCode.inj_SortNullStackOp
  retr
    | SortMaybeOpCode.inj_SortNullStackOp x => some x
    | _ => none

instance : Inj SortUnStackOp SortMaybeOpCode where
  inj := SortMaybeOpCode.inj_SortUnStackOp
  retr
    | SortMaybeOpCode.inj_SortUnStackOp x => some x
    | _ => none

instance : Inj SortBinStackOp SortMaybeOpCode where
  inj := SortMaybeOpCode.inj_SortBinStackOp
  retr
    | SortMaybeOpCode.inj_SortBinStackOp x => some x
    | _ => none

instance : Inj SortInt SortAccount where
  inj := SortAccount.inj_SortInt
  retr
    | SortAccount.inj_SortInt x => some x
    | _ => none

instance : Inj SortBytes SortAccountCode where
  inj := SortAccountCode.inj_SortBytes
  retr
    | SortAccountCode.inj_SortBytes x => some x