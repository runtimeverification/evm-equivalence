import EvmEquivalence.KEVM2Lean.Prelude

inductive SortStatusCode : Type where
  | «.StatusCode_NETWORK_StatusCode» : SortStatusCode
  | EVMC_INTERNAL_ERROR_NETWORK_StatusCode : SortStatusCode
  | EVMC_REJECTED_NETWORK_StatusCode : SortStatusCode
  deriving BEq, DecidableEq

inductive SortTernStackOp : Type where
  | ADDMOD_EVM_TernStackOp : SortTernStackOp
  | MULMOD_EVM_TernStackOp : SortTernStackOp
  deriving BEq, DecidableEq

inductive SortScheduleConst : Type where
  | Gaccesslistaddress_SCHEDULE_ScheduleConst : SortScheduleConst
  | Gaccessliststoragekey_SCHEDULE_ScheduleConst : SortScheduleConst
  | Gbalance_SCHEDULE_ScheduleConst : SortScheduleConst
  | Gbase_SCHEDULE_ScheduleConst : SortScheduleConst
  | Gblockhash_SCHEDULE_ScheduleConst : SortScheduleConst
  | Gcall_SCHEDULE_ScheduleConst : SortScheduleConst
  | Gcallstipend_SCHEDULE_ScheduleConst : SortScheduleConst
  | Gcallvalue_SCHEDULE_ScheduleConst : SortScheduleConst
  | Gcodedeposit_SCHEDULE_ScheduleConst : SortScheduleConst
  | Gcoldaccountaccess_SCHEDULE_ScheduleConst : SortScheduleConst
  | Gcoldsload_SCHEDULE_ScheduleConst : SortScheduleConst
  | Gcopy_SCHEDULE_ScheduleConst : SortScheduleConst
  | Gcreate_SCHEDULE_ScheduleConst : SortScheduleConst
  | Gecadd_SCHEDULE_ScheduleConst : SortScheduleConst
  | Gecmul_SCHEDULE_ScheduleConst : SortScheduleConst
  | Gecpaircoeff_SCHEDULE_ScheduleConst : SortScheduleConst
  | Gecpairconst_SCHEDULE_ScheduleConst : SortScheduleConst
  | Gexp_SCHEDULE_ScheduleConst : SortScheduleConst
  | Gexpbyte_SCHEDULE_ScheduleConst : SortScheduleConst
  | Gextcodecopy_SCHEDULE_ScheduleConst : SortScheduleConst
  | Gextcodesize_SCHEDULE_ScheduleConst : SortScheduleConst
  | Gfround_SCHEDULE_ScheduleConst : SortScheduleConst
  | Ghigh_SCHEDULE_ScheduleConst : SortScheduleConst
  | Ginitcodewordcost_SCHEDULE_ScheduleConst : SortScheduleConst
  | Gjumpdest_SCHEDULE_ScheduleConst : SortScheduleConst
  | Glog_SCHEDULE_ScheduleConst : SortScheduleConst
  | Glogdata_SCHEDULE_ScheduleConst : SortScheduleConst
  | Glogtopic_SCHEDULE_ScheduleConst : SortScheduleConst
  | Glow_SCHEDULE_ScheduleConst : SortScheduleConst
  | Gmemory_SCHEDULE_ScheduleConst : SortScheduleConst
  | Gmid_SCHEDULE_ScheduleConst : SortScheduleConst
  | Gnewaccount_SCHEDULE_ScheduleConst : SortScheduleConst
  | Gpointeval_SCHEDULE_ScheduleConst : SortScheduleConst
  | Gquadcoeff_SCHEDULE_ScheduleConst : SortScheduleConst
  | Gquaddivisor_SCHEDULE_ScheduleConst : SortScheduleConst
  | Gselfdestruct_SCHEDULE_ScheduleConst : SortScheduleConst
  | Gsha3_SCHEDULE_ScheduleConst : SortScheduleConst
  | Gsha3word_SCHEDULE_ScheduleConst : SortScheduleConst
  | Gsload_SCHEDULE_ScheduleConst : SortScheduleConst
  | Gsstorereset_SCHEDULE_ScheduleConst : SortScheduleConst
  | Gsstoreset_SCHEDULE_ScheduleConst : SortScheduleConst
  | Gtransaction_SCHEDULE_ScheduleConst : SortScheduleConst
  | Gtxcreate_SCHEDULE_ScheduleConst : SortScheduleConst
  | Gtxdatanonzero_SCHEDULE_ScheduleConst : SortScheduleConst
  | Gtxdatazero_SCHEDULE_ScheduleConst : SortScheduleConst
  | Gverylow_SCHEDULE_ScheduleConst : SortScheduleConst
  | Gwarmstoragedirtystore_SCHEDULE_ScheduleConst : SortScheduleConst
  | Gwarmstorageread_SCHEDULE_ScheduleConst : SortScheduleConst
  | Gzero_SCHEDULE_ScheduleConst : SortScheduleConst
  | Rb_SCHEDULE_ScheduleConst : SortScheduleConst
  | Rmaxquotient_SCHEDULE_ScheduleConst : SortScheduleConst
  | Rselfdestruct_SCHEDULE_ScheduleConst : SortScheduleConst
  | Rsstoreclear_SCHEDULE_ScheduleConst : SortScheduleConst
  | maxCodeSize_SCHEDULE_ScheduleConst : SortScheduleConst
  | maxInitCodeSize_SCHEDULE_ScheduleConst : SortScheduleConst
  deriving BEq, DecidableEq

inductive SortPushOp : Type where
  | PUSHZERO_EVM_PushOp : SortPushOp
  deriving BEq, DecidableEq

inductive SortSchedule : Type where
  | BERLIN_EVM : SortSchedule
  | BYZANTIUM_EVM : SortSchedule
  | CANCUN_EVM : SortSchedule
  | CONSTANTINOPLE_EVM : SortSchedule
  | DEFAULT_EVM : SortSchedule
  | FRONTIER_EVM : SortSchedule
  | HOMESTEAD_EVM : SortSchedule
  | ISTANBUL_EVM : SortSchedule
  | LONDON_EVM : SortSchedule
  | MERGE_EVM : SortSchedule
  | PETERSBURG_EVM : SortSchedule
  | SHANGHAI_EVM : SortSchedule
  | SPURIOUS_DRAGON_EVM : SortSchedule
  | TANGERINE_WHISTLE_EVM : SortSchedule
  deriving BEq, DecidableEq

inductive SortUnStackOp : Type where
  | ISZERO_EVM_UnStackOp : SortUnStackOp
  | MLOAD_EVM_UnStackOp : SortUnStackOp
  | NOT_EVM_UnStackOp : SortUnStackOp
  | SLOAD_EVM_UnStackOp : SortUnStackOp
  deriving BEq, DecidableEq

inductive SortTxType : Type where
  | «.TxType_EVM-TYPES_TxType» : SortTxType
  | «AccessList_EVM-TYPES_TxType» : SortTxType
  | «Blob_EVM-TYPES_TxType» : SortTxType
  | «DynamicFee_EVM-TYPES_TxType» : SortTxType
  | «Legacy_EVM-TYPES_TxType» : SortTxType
  deriving BEq, DecidableEq

inductive SortScheduleFlag : Type where
  | Gemptyisnonexistent_SCHEDULE_ScheduleFlag : SortScheduleFlag
  | Ghasaccesslist_SCHEDULE_ScheduleFlag : SortScheduleFlag
  | Ghasbasefee_SCHEDULE_ScheduleFlag : SortScheduleFlag
  | Ghasbeaconroot_SCHEDULE_ScheduleFlag : SortScheduleFlag
  | Ghasblobbasefee_SCHEDULE_ScheduleFlag : SortScheduleFlag
  | Ghasblobhash_SCHEDULE_ScheduleFlag : SortScheduleFlag
  | Ghaschainid_SCHEDULE_ScheduleFlag : SortScheduleFlag
  | Ghascreate2_SCHEDULE_ScheduleFlag : SortScheduleFlag
  | Ghasdirtysstore_SCHEDULE_ScheduleFlag : SortScheduleFlag
  | Ghaseip6780_SCHEDULE_ScheduleFlag : SortScheduleFlag
  | Ghasextcodehash_SCHEDULE_ScheduleFlag : SortScheduleFlag
  | Ghasmaxinitcodesize_SCHEDULE_ScheduleFlag : SortScheduleFlag
  | Ghasmcopy_SCHEDULE_ScheduleFlag : SortScheduleFlag
  | Ghasprevrandao_SCHEDULE_ScheduleFlag : SortScheduleFlag
  | Ghaspushzero_SCHEDULE_ScheduleFlag : SortScheduleFlag
  | Ghasrejectedfirstbyte_SCHEDULE_ScheduleFlag : SortScheduleFlag
  | Ghasreturndata_SCHEDULE_ScheduleFlag : SortScheduleFlag
  | Ghasrevert_SCHEDULE_ScheduleFlag : SortScheduleFlag
  | Ghasselfbalance_SCHEDULE_ScheduleFlag : SortScheduleFlag
  | Ghasshift_SCHEDULE_ScheduleFlag : SortScheduleFlag
  | Ghassstorestipend_SCHEDULE_ScheduleFlag : SortScheduleFlag
  | Ghasstaticcall_SCHEDULE_ScheduleFlag : SortScheduleFlag
  | Ghastransient_SCHEDULE_ScheduleFlag : SortScheduleFlag
  | Ghaswarmcoinbase_SCHEDULE_ScheduleFlag : SortScheduleFlag
  | Ghaswithdrawals_SCHEDULE_ScheduleFlag : SortScheduleFlag
  | Gselfdestructnewaccount_SCHEDULE_ScheduleFlag : SortScheduleFlag
  | Gstaticcalldepth_SCHEDULE_ScheduleFlag : SortScheduleFlag
  | Gzerovaluenewaccountgas_SCHEDULE_ScheduleFlag : SortScheduleFlag
  deriving BEq, DecidableEq

inductive SortBinStackOp : Type where
  | ADD_EVM_BinStackOp : SortBinStackOp
  | AND_EVM_BinStackOp : SortBinStackOp
  | BYTE_EVM_BinStackOp : SortBinStackOp
  | DIV_EVM_BinStackOp : SortBinStackOp
  | EQ_EVM_BinStackOp : SortBinStackOp
  | EXP_EVM_BinStackOp : SortBinStackOp
  | GT_EVM_BinStackOp : SortBinStackOp
  | LT_EVM_BinStackOp : SortBinStackOp
  | MOD_EVM_BinStackOp : SortBinStackOp
  | MSTORE_EVM_BinStackOp : SortBinStackOp
  | MSTORE8_EVM_BinStackOp : SortBinStackOp
  | SAR_EVM_BinStackOp : SortBinStackOp
  | SDIV_EVM_BinStackOp : SortBinStackOp
  | SGT_EVM_BinStackOp : SortBinStackOp
  | SHL_EVM_BinStackOp : SortBinStackOp
  | SHR_EVM_BinStackOp : SortBinStackOp
  | SIGNEXTEND_EVM_BinStackOp : SortBinStackOp
  | SLT_EVM_BinStackOp : SortBinStackOp
  | SMOD_EVM_BinStackOp : SortBinStackOp
  | SSTORE_EVM_BinStackOp : SortBinStackOp
  | SUB_EVM_BinStackOp : SortBinStackOp
  | XOR_EVM_BinStackOp : SortBinStackOp
  deriving BEq, DecidableEq

inductive SortMode : Type where
  | NORMAL : SortMode
  | «SUCCESS_ETHEREUM-SIMULATION-PURE_Mode» : SortMode
  | VMTESTS : SortMode
  deriving BEq, DecidableEq

structure SortStatusCodeCell : Type where
  val : SortStatusCode
  deriving BEq, DecidableEq

structure SortScheduleCell : Type where
  val : SortSchedule
  deriving BEq, DecidableEq

structure SortTxTypeCell : Type where
  val : SortTxType
  deriving BEq, DecidableEq

structure SortBalanceCell : Type where
  val : SortInt
  deriving BEq, DecidableEq

structure SortCoinbaseCell : Type where
  val : SortInt
  deriving BEq, DecidableEq

structure SortBlockNonceCell : Type where
  val : SortInt
  deriving BEq, DecidableEq

structure SortTimestampCell : Type where
  val : SortInt
  deriving BEq, DecidableEq

structure SortPreviousHashCell : Type where
  val : SortInt
  deriving BEq, DecidableEq

structure SortValueCell : Type where
  val : SortInt
  deriving BEq, DecidableEq

structure SortRefundCell : Type where
  val : SortInt
  deriving BEq, DecidableEq

structure SortCallDepthCell : Type where
  val : SortInt
  deriving BEq, DecidableEq

structure SortBlobGasUsedCell : Type where
  val : SortInt
  deriving BEq, DecidableEq

inductive SortJSONKey : Type where
  | inj_SortInt (x : SortInt) : SortJSONKey
  deriving BEq, DecidableEq

structure SortTxChainIDCell : Type where
  val : SortInt
  deriving BEq, DecidableEq

structure SortAcctIDCell : Type where
  val : SortInt
  deriving BEq, DecidableEq

inductive SortWordStack : Type where
  | «.WordStack_EVM-TYPES_WordStack» : SortWordStack
  | «_:__EVM-TYPES_WordStack_Int_WordStack» (x0 : SortInt) (x1 : SortWordStack) : SortWordStack
  deriving BEq, DecidableEq

structure SortGeneratedCounterCell : Type where
  val : SortInt
  deriving BEq, DecidableEq

structure SortNumberCell : Type where
  val : SortInt
  deriving BEq, DecidableEq

structure SortTxMaxFeeCell : Type where
  val : SortInt
  deriving BEq, DecidableEq

structure SortTxGasLimitCell : Type where
  val : SortInt
  deriving BEq, DecidableEq

inductive SortGas : Type where
  | inj_SortInt (x : SortInt) : SortGas
  deriving BEq, DecidableEq

structure SortExcessBlobGasCell : Type where
  val : SortInt
  deriving BEq, DecidableEq

structure SortTxNonceCell : Type where
  val : SortInt
  deriving BEq, DecidableEq

structure SortPcCell : Type where
  val : SortInt
  deriving BEq, DecidableEq

structure SortAmountCell : Type where
  val : SortInt
  deriving BEq, DecidableEq

structure SortGasLimitCell : Type where
  val : SortInt
  deriving BEq, DecidableEq

structure SortTxGasPriceCell : Type where
  val : SortInt
  deriving BEq, DecidableEq

structure SortGasPriceCell : Type where
  val : SortInt
  deriving BEq, DecidableEq

structure SortMemoryUsedCell : Type where
  val : SortInt
  deriving BEq, DecidableEq

structure SortMsgIDCell : Type where
  val : SortInt
  deriving BEq, DecidableEq

structure SortWithdrawalIDCell : Type where
  val : SortInt
  deriving BEq, DecidableEq

structure SortBeaconRootCell : Type where
  val : SortInt
  deriving BEq, DecidableEq

structure SortBaseFeeCell : Type where
  val : SortInt
  deriving BEq, DecidableEq

inductive SortAccount : Type where
  | inj_SortInt (x : SortInt) : SortAccount
  | «.Account_EVM-TYPES_Account» : SortAccount
  deriving BEq, DecidableEq

structure SortIndexCell : Type where
  val : SortInt
  deriving BEq, DecidableEq

structure SortTransactionsRootCell : Type where
  val : SortInt
  deriving BEq, DecidableEq

structure SortOmmersHashCell : Type where
  val : SortInt
  deriving BEq, DecidableEq

structure SortMixHashCell : Type where
  val : SortInt
  deriving BEq, DecidableEq

structure SortCallValueCell : Type where
  val : SortInt
  deriving BEq, DecidableEq

structure SortNonceCell : Type where
  val : SortInt
  deriving BEq, DecidableEq

structure SortWithdrawalsRootCell : Type where
  val : SortInt
  deriving BEq, DecidableEq

structure SortStateRootCell : Type where
  val : SortInt
  deriving BEq, DecidableEq

structure SortSigVCell : Type where
  val : SortInt
  deriving BEq, DecidableEq

structure SortExitCodeCell : Type where
  val : SortInt
  deriving BEq, DecidableEq

structure SortValidatorIndexCell : Type where
  val : SortInt
  deriving BEq, DecidableEq

structure SortTxMaxBlobFeeCell : Type where
  val : SortInt
  deriving BEq, DecidableEq

structure SortReceiptsRootCell : Type where
  val : SortInt
  deriving BEq, DecidableEq

structure SortTxPriorityFeeCell : Type where
  val : SortInt
  deriving BEq, DecidableEq

structure SortDifficultyCell : Type where
  val : SortInt
  deriving BEq, DecidableEq

structure SortChainIDCell : Type where
  val : SortInt
  deriving BEq, DecidableEq

inductive SortAccountCode : Type where
  | inj_SortBytes (x : SortBytes) : SortAccountCode
  deriving BEq, DecidableEq

structure SortExtraDataCell : Type where
  val : SortBytes
  deriving BEq, DecidableEq

structure SortProgramCell : Type where
  val : SortBytes
  deriving BEq, DecidableEq

structure SortJumpDestsCell : Type where
  val : SortBytes
  deriving BEq, DecidableEq

structure SortSigSCell : Type where
  val : SortBytes
  deriving BEq, DecidableEq

structure SortOutputCell : Type where
  val : SortBytes
  deriving BEq, DecidableEq

structure SortDataCell : Type where
  val : SortBytes
  deriving BEq, DecidableEq

structure SortCallDataCell : Type where
  val : SortBytes
  deriving BEq, DecidableEq

structure SortSigRCell : Type where
  val : SortBytes
  deriving BEq, DecidableEq

structure SortLocalMemCell : Type where
  val : SortBytes
  deriving BEq, DecidableEq

structure SortLogsBloomCell : Type where
  val : SortBytes
  deriving BEq, DecidableEq

mutual
  inductive SortInternalOp : Type where
    | «#next[_]_EVM_InternalOp_MaybeOpCode» (x0 : SortMaybeOpCode) : SortInternalOp
    deriving BEq, DecidableEq

  inductive SortMaybeOpCode : Type where
    | inj_SortBinStackOp (x : SortBinStackOp) : SortMaybeOpCode
    | inj_SortInternalOp (x : SortInternalOp) : SortMaybeOpCode
    | inj_SortPushOp (x : SortPushOp) : SortMaybeOpCode
    | inj_SortTernStackOp (x : SortTernStackOp) : SortMaybeOpCode
    | inj_SortUnStackOp (x : SortUnStackOp) : SortMaybeOpCode
    deriving BEq, DecidableEq
end

structure SortStaticCell : Type where
  val : SortBool
  deriving BEq, DecidableEq

structure SortUseGasCell : Type where
  val : SortBool
  deriving BEq, DecidableEq

structure SortModeCell : Type where
  val : SortMode
  deriving BEq, DecidableEq

structure SortWordStackCell : Type where
  val : SortWordStack
  deriving BEq, DecidableEq

structure SortGasCell : Type where
  val : SortGas
  deriving BEq, DecidableEq

structure SortCallGasCell : Type where
  val : SortGas
  deriving BEq, DecidableEq

structure SortGasUsedCell : Type where
  val : SortGas
  deriving BEq, DecidableEq

structure SortIdCell : Type where
  val : SortAccount
  deriving BEq, DecidableEq

structure SortToCell : Type where
  val : SortAccount
  deriving BEq, DecidableEq

structure SortAddressCell : Type where
  val : SortAccount
  deriving BEq, DecidableEq

structure SortOriginCell : Type where
  val : SortAccount
  deriving BEq, DecidableEq

structure SortCallerCell : Type where
  val : SortAccount
  deriving BEq, DecidableEq

structure SortCodeCell : Type where
  val : SortAccountCode
  deriving BEq, DecidableEq

structure SortWithdrawalCell : Type where
  withdrawalID : SortWithdrawalIDCell
  index : SortIndexCell
  validatorIndex : SortValidatorIndexCell
  address : SortAddressCell
  amount : SortAmountCell
  deriving BEq, DecidableEq

structure SortCallStateCell : Type where
  program : SortProgramCell
  jumpDests : SortJumpDestsCell
  id : SortIdCell
  caller : SortCallerCell
  callData : SortCallDataCell
  callValue : SortCallValueCell
  wordStack : SortWordStackCell
  localMem : SortLocalMemCell
  pc : SortPcCell
  gas : SortGasCell
  memoryUsed : SortMemoryUsedCell
  callGas : SortCallGasCell
  static : SortStaticCell
  callDepth : SortCallDepthCell
  deriving BEq, DecidableEq

structure SortWithdrawalCellMap : Type where
  coll : List (SortWithdrawalIDCell × SortWithdrawalCell)
  deriving BEq, DecidableEq

structure SortWithdrawalsCell : Type where
  val : SortWithdrawalCellMap
  deriving BEq, DecidableEq

mutual
  structure SortAccessedAccountsCell : Type where
    val : SortSet
    deriving BEq

  structure SortAccessedStorageCell : Type where
    val : SortMap
    deriving BEq

  structure SortAccountCell : Type where
    acctID : SortAcctIDCell
    balance : SortBalanceCell
    code : SortCodeCell
    storage : SortStorageCell
    origStorage : SortOrigStorageCell
    transientStorage : SortTransientStorageCell
    nonce : SortNonceCell
    deriving BEq

  structure SortAccountCellMap : Type where
    coll : List (SortAcctIDCell × SortAccountCell)
    deriving BEq

  structure SortAccountsCell : Type where
    val : SortAccountCellMap
    deriving BEq

  structure SortBlockCell : Type where
    previousHash : SortPreviousHashCell
    ommersHash : SortOmmersHashCell
    coinbase : SortCoinbaseCell
    stateRoot : SortStateRootCell
    transactionsRoot : SortTransactionsRootCell
    receiptsRoot : SortReceiptsRootCell
    logsBloom : SortLogsBloomCell
    difficulty : SortDifficultyCell
    number : SortNumberCell
    gasLimit : SortGasLimitCell
    gasUsed : SortGasUsedCell
    timestamp : SortTimestampCell
    extraData : SortExtraDataCell
    mixHash : SortMixHashCell
    blockNonce : SortBlockNonceCell
    baseFee : SortBaseFeeCell
    withdrawalsRoot : SortWithdrawalsRootCell
    blobGasUsed : SortBlobGasUsedCell
    excessBlobGas : SortExcessBlobGasCell
    beaconRoot : SortBeaconRootCell
    ommerBlockHeaders : SortOmmerBlockHeadersCell
    deriving BEq

  structure SortBlockhashesCell : Type where
    val : SortList
    deriving BEq

  structure SortCallStackCell : Type where
    val : SortList
    deriving BEq

  structure SortCreatedAccountsCell : Type where
    val : SortSet
    deriving BEq

  structure SortEthereumCell : Type where
    evm : SortEvmCell
    network : SortNetworkCell
    deriving BEq

  structure SortEvmCell : Type where
    output : SortOutputCell
    statusCode : SortStatusCodeCell
    callStack : SortCallStackCell
    interimStates : SortInterimStatesCell
    touchedAccounts : SortTouchedAccountsCell
    callState : SortCallStateCell
    versionedHashes : SortVersionedHashesCell
    substate : SortSubstateCell
    gasPrice : SortGasPriceCell
    origin : SortOriginCell
    blockhashes : SortBlockhashesCell
    block : SortBlockCell
    deriving BEq

  structure SortGeneratedTopCell : Type where
    kevm : SortKevmCell
    generatedCounter : SortGeneratedCounterCell
    deriving BEq

  structure SortInterimStatesCell : Type where
    val : SortList
    deriving BEq

  inductive SortJSON : Type where
    | inj_SortAccount (x : SortAccount) : SortJSON
    | inj_SortBool (x : SortBool) : SortJSON
    | inj_SortBytes (x : SortBytes) : SortJSON
    | inj_SortInt (x : SortInt) : SortJSON
    | inj_SortMap (x : SortMap) : SortJSON
    | inj_SortTxType (x : SortTxType) : SortJSON
    | JSONEntry (x0 : SortJSONKey) (x1 : SortJSON) : SortJSON
    | JSONList (x0 : SortJSONs) : SortJSON
    | JSONObject (x0 : SortJSONs) : SortJSON
    | JSONnull : SortJSON
    deriving BEq

  inductive SortJSONs : Type where
    | «.List{"JSONs"}» : SortJSONs
    | JSONs (x0 : SortJSON) (x1 : SortJSONs) : SortJSONs
    deriving BEq

  inductive SortK : Type where
    | dotk : SortK
    | kseq (x0 : SortKItem) (x1 : SortK) : SortK
    deriving BEq

  structure SortKCell : Type where
    val : SortK
    deriving BEq

  inductive SortKItem : Type where
    | inj_SortAccessedAccountsCell (x : SortAccessedAccountsCell) : SortKItem
    | inj_SortAccessedStorageCell (x : SortAccessedStorageCell) : SortKItem
    | inj_SortAccount (x : SortAccount) : SortKItem
    | inj_SortAccountCell (x : SortAccountCell) : SortKItem
    | inj_SortAccountCellMap (x : SortAccountCellMap) : SortKItem
    | inj_SortAccountCode (x : SortAccountCode) : SortKItem
    | inj_SortAccountsCell (x : SortAccountsCell) : SortKItem
    | inj_SortAcctIDCell (x : SortAcctIDCell) : SortKItem
    | inj_SortAddressCell (x : SortAddressCell) : SortKItem
    | inj_SortAmountCell (x : SortAmountCell) : SortKItem
    | inj_SortBalanceCell (x : SortBalanceCell) : SortKItem
    | inj_SortBaseFeeCell (x : SortBaseFeeCell) : SortKItem
    | inj_SortBeaconRootCell (x : SortBeaconRootCell) : SortKItem
    | inj_SortBinStackOp (x : SortBinStackOp) : SortKItem
    | inj_SortBlobGasUsedCell (x : SortBlobGasUsedCell) : SortKItem
    | inj_SortBlockCell (x : SortBlockCell) : SortKItem
    | inj_SortBlockNonceCell (x : SortBlockNonceCell) : SortKItem
    | inj_SortBlockhashesCell (x : SortBlockhashesCell) : SortKItem
    | inj_SortBool (x : SortBool) : SortKItem
    | inj_SortBytes (x : SortBytes) : SortKItem
    | inj_SortCallDataCell (x : SortCallDataCell) : SortKItem
    | inj_SortCallDepthCell (x : SortCallDepthCell) : SortKItem
    | inj_SortCallGasCell (x : SortCallGasCell) : SortKItem
    | inj_SortCallStackCell (x : SortCallStackCell) : SortKItem
    | inj_SortCallStateCell (x : SortCallStateCell) : SortKItem
    | inj_SortCallValueCell (x : SortCallValueCell) : SortKItem
    | inj_SortCallerCell (x : SortCallerCell) : SortKItem
    | inj_SortChainIDCell (x : SortChainIDCell) : SortKItem
    | inj_SortCodeCell (x : SortCodeCell) : SortKItem
    | inj_SortCoinbaseCell (x : SortCoinbaseCell) : SortKItem
    | inj_SortCreatedAccountsCell (x : SortCreatedAccountsCell) : SortKItem
    | inj_SortDataCell (x : SortDataCell) : SortKItem
    | inj_SortDifficultyCell (x : SortDifficultyCell) : SortKItem
    | inj_SortEndianness (x : SortEndianness) : SortKItem
    | inj_SortEthereumCell (x : SortEthereumCell) : SortKItem
    | inj_SortEvmCell (x : SortEvmCell) : SortKItem
    | inj_SortExcessBlobGasCell (x : SortExcessBlobGasCell) : SortKItem
    | inj_SortExitCodeCell (x : SortExitCodeCell) : SortKItem
    | inj_SortExtraDataCell (x : SortExtraDataCell) : SortKItem
    | inj_SortGas (x : SortGas) : SortKItem
    | inj_SortGasCell (x : SortGasCell) : SortKItem
    | inj_SortGasLimitCell (x : SortGasLimitCell) : SortKItem
    | inj_SortGasPriceCell (x : SortGasPriceCell) : SortKItem
    | inj_SortGasUsedCell (x : SortGasUsedCell) : SortKItem
    | inj_SortGeneratedCounterCell (x : SortGeneratedCounterCell) : SortKItem
    | inj_SortGeneratedTopCell (x : SortGeneratedTopCell) : SortKItem
    | inj_SortIdCell (x : SortIdCell) : SortKItem
    | inj_SortIndexCell (x : SortIndexCell) : SortKItem
    | inj_SortInt (x : SortInt) : SortKItem
    | inj_SortInterimStatesCell (x : SortInterimStatesCell) : SortKItem
    | inj_SortInternalOp (x : SortInternalOp) : SortKItem
    | inj_SortJSON (x : SortJSON) : SortKItem
    | inj_SortJSONKey (x : SortJSONKey) : SortKItem
    | inj_SortJSONs (x : SortJSONs) : SortKItem
    | inj_SortJumpDestsCell (x : SortJumpDestsCell) : SortKItem
    | inj_SortKCell (x : SortKCell) : SortKItem
    | inj_SortKevmCell (x : SortKevmCell) : SortKItem
    | inj_SortList (x : SortList) : SortKItem
    | inj_SortLocalMemCell (x : SortLocalMemCell) : SortKItem
    | inj_SortLogCell (x : SortLogCell) : SortKItem
    | inj_SortLogsBloomCell (x : SortLogsBloomCell) : SortKItem
    | inj_SortMap (x : SortMap) : SortKItem
    | inj_SortMaybeOpCode (x : SortMaybeOpCode) : SortKItem
    | inj_SortMemoryUsedCell (x : SortMemoryUsedCell) : SortKItem
    | inj_SortMessageCell (x : SortMessageCell) : SortKItem
    | inj_SortMessageCellMap (x : SortMessageCellMap) : SortKItem
    | inj_SortMessagesCell (x : SortMessagesCell) : SortKItem
    | inj_SortMixHashCell (x : SortMixHashCell) : SortKItem
    | inj_SortMode (x : SortMode) : SortKItem
    | inj_SortModeCell (x : SortModeCell) : SortKItem
    | inj_SortMsgIDCell (x : SortMsgIDCell) : SortKItem
    | inj_SortNetworkCell (x : SortNetworkCell) : SortKItem
    | inj_SortNonceCell (x : SortNonceCell) : SortKItem
    | inj_SortNumberCell (x : SortNumberCell) : SortKItem
    | inj_SortOmmerBlockHeadersCell (x : SortOmmerBlockHeadersCell) : SortKItem
    | inj_SortOmmersHashCell (x : SortOmmersHashCell) : SortKItem
    | inj_SortOrigStorageCell (x : SortOrigStorageCell) : SortKItem
    | inj_SortOriginCell (x : SortOriginCell) : SortKItem
    | inj_SortOutputCell (x : SortOutputCell) : SortKItem
    | inj_SortPcCell (x : SortPcCell) : SortKItem
    | inj_SortPreviousHashCell (x : SortPreviousHashCell) : SortKItem
    | inj_SortProgramCell (x : SortProgramCell) : SortKItem
    | inj_SortPushOp (x : SortPushOp) : SortKItem
    | inj_SortReceiptsRootCell (x : SortReceiptsRootCell) : SortKItem
    | inj_SortRefundCell (x : SortRefundCell) : SortKItem
    | inj_SortSchedule (x : SortSchedule) : SortKItem
    | inj_SortScheduleCell (x : SortScheduleCell) : SortKItem
    | inj_SortScheduleConst (x : SortScheduleConst) : SortKItem
    | inj_SortScheduleFlag (x : SortScheduleFlag) : SortKItem
    | inj_SortSelfDestructCell (x : SortSelfDestructCell) : SortKItem
    | inj_SortSet (x : SortSet) : SortKItem
    | inj_SortSigRCell (x : SortSigRCell) : SortKItem
    | inj_SortSigSCell (x : SortSigSCell) : SortKItem
    | inj_SortSigVCell (x : SortSigVCell) : SortKItem
    | inj_SortSignedness (x : SortSignedness) : SortKItem
    | inj_SortStateRootCell (x : SortStateRootCell) : SortKItem
    | inj_SortStaticCell (x : SortStaticCell) : SortKItem
    | inj_SortStatusCode (x : SortStatusCode) : SortKItem
    | inj_SortStatusCodeCell (x : SortStatusCodeCell) : SortKItem
    | inj_SortStorageCell (x : SortStorageCell) : SortKItem
    | inj_SortSubstateCell (x : SortSubstateCell) : SortKItem
    | inj_SortTernStackOp (x : SortTernStackOp) : SortKItem
    | inj_SortTimestampCell (x : SortTimestampCell) : SortKItem
    | inj_SortToCell (x : SortToCell) : SortKItem
    | inj_SortTouchedAccountsCell (x : SortTouchedAccountsCell) : SortKItem
    | inj_SortTransactionsRootCell (x : SortTransactionsRootCell) : SortKItem
    | inj_SortTransientStorageCell (x : SortTransientStorageCell) : SortKItem
    | inj_SortTxAccessCell (x : SortTxAccessCell) : SortKItem
    | inj_SortTxChainIDCell (x : SortTxChainIDCell) : SortKItem
    | inj_SortTxGasLimitCell (x : SortTxGasLimitCell) : SortKItem
    | inj_SortTxGasPriceCell (x : SortTxGasPriceCell) : SortKItem
    | inj_SortTxMaxBlobFeeCell (x : SortTxMaxBlobFeeCell) : SortKItem
    | inj_SortTxMaxFeeCell (x : SortTxMaxFeeCell) : SortKItem
    | inj_SortTxNonceCell (x : SortTxNonceCell) : SortKItem
    | inj_SortTxOrderCell (x : SortTxOrderCell) : SortKItem
    | inj_SortTxPendingCell (x : SortTxPendingCell) : SortKItem
    | inj_SortTxPriorityFeeCell (x : SortTxPriorityFeeCell) : SortKItem
    | inj_SortTxType (x : SortTxType) : SortKItem
    | inj_SortTxTypeCell (x : SortTxTypeCell) : SortKItem
    | inj_SortTxVersionedHashesCell (x : SortTxVersionedHashesCell) : SortKItem
    | inj_SortUnStackOp (x : SortUnStackOp) : SortKItem
    | inj_SortUseGasCell (x : SortUseGasCell) : SortKItem
    | inj_SortValidatorIndexCell (x : SortValidatorIndexCell) : SortKItem
    | inj_SortValueCell (x : SortValueCell) : SortKItem
    | inj_SortVersionedHashesCell (x : SortVersionedHashesCell) : SortKItem
    | inj_SortWithdrawalCell (x : SortWithdrawalCell) : SortKItem
    | inj_SortWithdrawalCellMap (x : SortWithdrawalCellMap) : SortKItem
    | inj_SortWithdrawalIDCell (x : SortWithdrawalIDCell) : SortKItem
    | inj_SortWithdrawalsCell (x : SortWithdrawalsCell) : SortKItem
    | inj_SortWithdrawalsOrderCell (x : SortWithdrawalsOrderCell) : SortKItem
    | inj_SortWithdrawalsPendingCell (x : SortWithdrawalsPendingCell) : SortKItem
    | inj_SortWithdrawalsRootCell (x : SortWithdrawalsRootCell) : SortKItem
    | inj_SortWordStack (x : SortWordStack) : SortKItem
    | inj_SortWordStackCell (x : SortWordStackCell) : SortKItem
    | «#accessAccounts__EVM_KItem_Account» (x0 : SortAccount) : SortKItem
    | «#accessAccounts__EVM_KItem_Set» (x0 : SortSet) : SortKItem
    | «#accessAccounts___EVM_KItem_Account_Account» (x0 : SortAccount) (x1 : SortAccount) : SortKItem
    | «#accessAccounts____EVM_KItem_Account_Account_Set» (x0 : SortAccount) (x1 : SortAccount) (x2 : SortSet) : SortKItem
    | «#accessStorage___EVM_KItem_Account_Int» (x0 : SortAccount) (x1 : SortInt) : SortKItem
    | «#codeDeposit__EVM_KItem_Int» (x0 : SortInt) : SortKItem
    | «#finishCodeDeposit___EVM_KItem_Int_Bytes» (x0 : SortInt) (x1 : SortBytes) : SortKItem
    | «#freezerCcall1_» (x0 : SortK) (x1 : SortK) (x2 : SortK) (x3 : SortK) (x4 : SortK) : SortKItem
    | «#freezerCcallgas1_» (x0 : SortK) (x1 : SortK) (x2 : SortK) (x3 : SortK) (x4 : SortK) : SortKItem
    | «#freezerCselfdestruct1_» (x0 : SortK) (x1 : SortK) : SortKItem
    | «#initVM_EVM_KItem» : SortKItem
    | «#mkCodeDeposit__EVM_KItem_Int» (x0 : SortInt) : SortKItem
    | «#return___EVM_KItem_Int_Int» (x0 : SortInt) (x1 : SortInt) : SortKItem
    | «#touchAccounts__EVM_KItem_Account» (x0 : SortAccount) : SortKItem
    | «#touchAccounts___EVM_KItem_Account_Account» (x0 : SortAccount) (x1 : SortAccount) : SortKItem
    | end (x0 : SortStatusCode) : SortKItem
    | execute : SortKItem
    | halt : SortKItem
    | «loadCallState__STATE-UTILS_KItem_JSON» (x0 : SortJSON) : SortKItem
    | loadProgram (x0 : SortBytes) : SortKItem
    deriving BEq

  structure SortKevmCell : Type where
    k : SortKCell
    exitCode : SortExitCodeCell
    mode : SortModeCell
    schedule : SortScheduleCell
    useGas : SortUseGasCell
    ethereum : SortEthereumCell
    deriving BEq

  structure SortList : Type where
    coll : List SortKItem
    deriving BEq

  structure SortLogCell : Type where
    val : SortList
    deriving BEq

  structure SortMap : Type where
    coll : List (SortKItem × SortKItem)
    deriving BEq

  structure SortMessageCell : Type where
    msgID : SortMsgIDCell
    txNonce : SortTxNonceCell
    txGasPrice : SortTxGasPriceCell
    txGasLimit : SortTxGasLimitCell
    to : SortToCell
    value : SortValueCell
    sigV : SortSigVCell
    sigR : SortSigRCell
    sigS : SortSigSCell
    data : SortDataCell
    txAccess : SortTxAccessCell
    txChainID : SortTxChainIDCell
    txPriorityFee : SortTxPriorityFeeCell
    txMaxFee : SortTxMaxFeeCell
    txType : SortTxTypeCell
    txMaxBlobFee : SortTxMaxBlobFeeCell
    txVersionedHashes : SortTxVersionedHashesCell
    deriving BEq

  structure SortMessageCellMap : Type where
    coll : List (SortMsgIDCell × SortMessageCell)
    deriving BEq

  structure SortMessagesCell : Type where
    val : SortMessageCellMap
    deriving BEq

  structure SortNetworkCell : Type where
    chainID : SortChainIDCell
    accounts : SortAccountsCell
    txOrder : SortTxOrderCell
    txPending : SortTxPendingCell
    messages : SortMessagesCell
    withdrawalsPending : SortWithdrawalsPendingCell
    withdrawalsOrder : SortWithdrawalsOrderCell
    withdrawals : SortWithdrawalsCell
    deriving BEq

  structure SortOmmerBlockHeadersCell : Type where
    val : SortJSON
    deriving BEq

  structure SortOrigStorageCell : Type where
    val : SortMap
    deriving BEq

  structure SortSelfDestructCell : Type where
    val : SortSet
    deriving BEq

  structure SortSet : Type where
    coll : List SortKItem
    deriving BEq

  structure SortStorageCell : Type where
    val : SortMap
    deriving BEq

  structure SortSubstateCell : Type where
    selfDestruct : SortSelfDestructCell
    log : SortLogCell
    refund : SortRefundCell
    accessedAccounts : SortAccessedAccountsCell
    accessedStorage : SortAccessedStorageCell
    createdAccounts : SortCreatedAccountsCell
    deriving BEq

  structure SortTouchedAccountsCell : Type where
    val : SortSet
    deriving BEq

  structure SortTransientStorageCell : Type where
    val : SortMap
    deriving BEq

  structure SortTxAccessCell : Type where
    val : SortJSON
    deriving BEq

  structure SortTxOrderCell : Type where
    val : SortList
    deriving BEq

  structure SortTxPendingCell : Type where
    val : SortList
    deriving BEq

  structure SortTxVersionedHashesCell : Type where
    val : SortList
    deriving BEq

  structure SortVersionedHashesCell : Type where
    val : SortList
    deriving BEq

  structure SortWithdrawalsOrderCell : Type where
    val : SortList
    deriving BEq

  structure SortWithdrawalsPendingCell : Type where
    val : SortList
    deriving BEq
end