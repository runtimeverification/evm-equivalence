import EvmEquivalence.KEVM2Lean.Func

inductive Rewrites : SortGeneratedTopCell → SortGeneratedTopCell → Prop where
  | tran
    {s1 s2 s3 : SortGeneratedTopCell}
    (t1 : Rewrites s1 s2)
    (t2 : Rewrites s2 s3)
    : Rewrites s1 s3
  | SUMMARY_ADD_2_SPEC_BASIC_BLOCK_21_TO_20
    {GAS_CELL PC_CELL W0 W1 _Val0 _Val3 _Val4 _Val5 _Val6 _Val7 : SortInt}
    {K_CELL : SortK}
    {SCHEDULE_CELL : SortSchedule}
    {USEGAS_CELL _Val1 _Val2 : SortBool}
    {WS : SortWordStack}
    {_DotVar0 : SortGeneratedCounterCell}
    {_DotVar2 : SortNetworkCell}
    {_Gen0 : SortProgramCell}
    {_Gen1 : SortJumpDestsCell}
    {_Gen10 : SortCallDepthCell}
    {_Gen11 : SortOutputCell}
    {_Gen12 : SortStatusCodeCell}
    {_Gen13 : SortCallStackCell}
    {_Gen14 : SortInterimStatesCell}
    {_Gen15 : SortTouchedAccountsCell}
    {_Gen16 : SortVersionedHashesCell}
    {_Gen17 : SortSubstateCell}
    {_Gen18 : SortGasPriceCell}
    {_Gen19 : SortOriginCell}
    {_Gen2 : SortIdCell}
    {_Gen20 : SortBlockhashesCell}
    {_Gen21 : SortBlockCell}
    {_Gen22 : SortExitCodeCell}
    {_Gen23 : SortModeCell}
    {_Gen3 : SortCallerCell}
    {_Gen4 : SortCallDataCell}
    {_Gen5 : SortCallValueCell}
    {_Gen6 : SortLocalMemCell}
    {_Gen7 : SortMemoryUsedCell}
    {_Gen8 : SortCallGasCell}
    {_Gen9 : SortStaticCell}
    (defn_Val0 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gverylow_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val0)
    (defn_Val1 : «_<=Int_» _Val0 GAS_CELL = some _Val1)
    (defn_Val2 : _andBool_ USEGAS_CELL _Val1 = some _Val2)
    (defn_Val3 : «_+Int_» W0 W1 = some _Val3)
    (defn_Val4 : chop _Val3 = some _Val4)
    (defn_Val5 : «_+Int_» PC_CELL 1 = some _Val5)
    (defn_Val6 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gverylow_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val6)
    (defn_Val7 : «_-Int_» GAS_CELL _Val6 = some _Val7)
    (req : _Val2 = true)
    : Rewrites {
      kevm := {
        k := { val := SortK.kseq ((@inj SortInternalOp SortKItem) (SortInternalOp.«#next[_]_EVM_InternalOp_MaybeOpCode» ((@inj SortBinStackOp SortMaybeOpCode) SortBinStackOp.ADD_EVM_BinStackOp))) K_CELL },
        exitCode := _Gen22,
        mode := _Gen23,
        schedule := { val := SCHEDULE_CELL },
        useGas := { val := USEGAS_CELL },
        ethereum := {
          evm := {
            output := _Gen11,
            statusCode := _Gen12,
            callStack := _Gen13,
            interimStates := _Gen14,
            touchedAccounts := _Gen15,
            callState := {
              program := _Gen0,
              jumpDests := _Gen1,
              id := _Gen2,
              caller := _Gen3,
              callData := _Gen4,
              callValue := _Gen5,
              wordStack := { val := SortWordStack.«_:__EVM-TYPES_WordStack_Int_WordStack» W0 (SortWordStack.«_:__EVM-TYPES_WordStack_Int_WordStack» W1 WS) },
              localMem := _Gen6,
              pc := { val := PC_CELL },
              gas := { val := (@inj SortInt SortGas) GAS_CELL },
              memoryUsed := _Gen7,
              callGas := _Gen8,
              static := _Gen9,
              callDepth := _Gen10 },
            versionedHashes := _Gen16,
            substate := _Gen17,
            gasPrice := _Gen18,
            origin := _Gen19,
            blockhashes := _Gen20,
            block := _Gen21 },
          network := _DotVar2 } },
      generatedCounter := _DotVar0 } {
      kevm := {
        k := { val := K_CELL },
        exitCode := _Gen22,
        mode := _Gen23,
        schedule := { val := SCHEDULE_CELL },
        useGas := { val := true },
        ethereum := {
          evm := {
            output := _Gen11,
            statusCode := _Gen12,
            callStack := _Gen13,
            interimStates := _Gen14,
            touchedAccounts := _Gen15,
            callState := {
              program := _Gen0,
              jumpDests := _Gen1,
              id := _Gen2,
              caller := _Gen3,
              callData := _Gen4,
              callValue := _Gen5,
              wordStack := { val := SortWordStack.«_:__EVM-TYPES_WordStack_Int_WordStack» _Val4 WS },
              localMem := _Gen6,
              pc := { val := _Val5 },
              gas := { val := (@inj SortInt SortGas) _Val7 },
              memoryUsed := _Gen7,
              callGas := _Gen8,
              static := _Gen9,
              callDepth := _Gen10 },
            versionedHashes := _Gen16,
            substate := _Gen17,
            gasPrice := _Gen18,
            origin := _Gen19,
            blockhashes := _Gen20,
            block := _Gen21 },
          network := _DotVar2 } },
      generatedCounter := _DotVar0 }
  | SUMMARY_PUSHZERO_0_SPEC_BASIC_BLOCK_25_TO_24
    {GAS_CELL PC_CELL _Val0 _Val11 _Val12 _Val13 _Val3 _Val6 : SortInt}
    {K_CELL : SortK}
    {SCHEDULE_CELL : SortSchedule}
    {USEGAS_CELL _Val1 _Val10 _Val2 _Val4 _Val5 _Val7 _Val8 _Val9 : SortBool}
    {WS : SortWordStack}
    {_DotVar0 : SortGeneratedCounterCell}
    {_DotVar2 : SortNetworkCell}
    {_Gen0 : SortProgramCell}
    {_Gen1 : SortJumpDestsCell}
    {_Gen10 : SortCallDepthCell}
    {_Gen11 : SortOutputCell}
    {_Gen12 : SortStatusCodeCell}
    {_Gen13 : SortCallStackCell}
    {_Gen14 : SortInterimStatesCell}
    {_Gen15 : SortTouchedAccountsCell}
    {_Gen16 : SortVersionedHashesCell}
    {_Gen17 : SortSubstateCell}
    {_Gen18 : SortGasPriceCell}
    {_Gen19 : SortOriginCell}
    {_Gen2 : SortIdCell}
    {_Gen20 : SortBlockhashesCell}
    {_Gen21 : SortBlockCell}
    {_Gen22 : SortExitCodeCell}
    {_Gen23 : SortModeCell}
    {_Gen3 : SortCallerCell}
    {_Gen4 : SortCallDataCell}
    {_Gen5 : SortCallValueCell}
    {_Gen6 : SortLocalMemCell}
    {_Gen7 : SortMemoryUsedCell}
    {_Gen8 : SortCallGasCell}
    {_Gen9 : SortStaticCell}
    (defn_Val0 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gbase_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val0)
    (defn_Val1 : «_<=Int_» _Val0 GAS_CELL = some _Val1)
    (defn_Val2 : _andBool_ USEGAS_CELL _Val1 = some _Val2)
    (defn_Val3 : sizeWordStackAux WS 0 = some _Val3)
    (defn_Val4 : «_<Int_» _Val3 0 = some _Val4)
    (defn_Val5 : notBool_ _Val4 = some _Val5)
    (defn_Val6 : sizeWordStackAux WS 0 = some _Val6)
    (defn_Val7 : «_<Int_» 1023 _Val6 = some _Val7)
    (defn_Val8 : notBool_ _Val7 = some _Val8)
    (defn_Val9 : _andBool_ _Val5 _Val8 = some _Val9)
    (defn_Val10 : _andBool_ _Val2 _Val9 = some _Val10)
    (defn_Val11 : «_+Int_» PC_CELL 1 = some _Val11)
    (defn_Val12 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gbase_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val12)
    (defn_Val13 : «_-Int_» GAS_CELL _Val12 = some _Val13)
    (req : _Val10 = true)
    : Rewrites {
      kevm := {
        k := { val := SortK.kseq ((@inj SortInternalOp SortKItem) (SortInternalOp.«#next[_]_EVM_InternalOp_MaybeOpCode» ((@inj SortPushOp SortMaybeOpCode) SortPushOp.PUSHZERO_EVM_PushOp))) K_CELL },
        exitCode := _Gen22,
        mode := _Gen23,
        schedule := { val := SCHEDULE_CELL },
        useGas := { val := USEGAS_CELL },
        ethereum := {
          evm := {
            output := _Gen11,
            statusCode := _Gen12,
            callStack := _Gen13,
            interimStates := _Gen14,
            touchedAccounts := _Gen15,
            callState := {
              program := _Gen0,
              jumpDests := _Gen1,
              id := _Gen2,
              caller := _Gen3,
              callData := _Gen4,
              callValue := _Gen5,
              wordStack := { val := WS },
              localMem := _Gen6,
              pc := { val := PC_CELL },
              gas := { val := (@inj SortInt SortGas) GAS_CELL },
              memoryUsed := _Gen7,
              callGas := _Gen8,
              static := _Gen9,
              callDepth := _Gen10 },
            versionedHashes := _Gen16,
            substate := _Gen17,
            gasPrice := _Gen18,
            origin := _Gen19,
            blockhashes := _Gen20,
            block := _Gen21 },
          network := _DotVar2 } },
      generatedCounter := _DotVar0 } {
      kevm := {
        k := { val := K_CELL },
        exitCode := _Gen22,
        mode := _Gen23,
        schedule := { val := SCHEDULE_CELL },
        useGas := { val := true },
        ethereum := {
          evm := {
            output := _Gen11,
            statusCode := _Gen12,
            callStack := _Gen13,
            interimStates := _Gen14,
            touchedAccounts := _Gen15,
            callState := {
              program := _Gen0,
              jumpDests := _Gen1,
              id := _Gen2,
              caller := _Gen3,
              callData := _Gen4,
              callValue := _Gen5,
              wordStack := { val := SortWordStack.«_:__EVM-TYPES_WordStack_Int_WordStack» 0 WS },
              localMem := _Gen6,
              pc := { val := _Val11 },
              gas := { val := (@inj SortInt SortGas) _Val13 },
              memoryUsed := _Gen7,
              callGas := _Gen8,
              static := _Gen9,
              callDepth := _Gen10 },
            versionedHashes := _Gen16,
            substate := _Gen17,
            gasPrice := _Gen18,
            origin := _Gen19,
            blockhashes := _Gen20,
            block := _Gen21 },
          network := _DotVar2 } },
      generatedCounter := _DotVar0 }
