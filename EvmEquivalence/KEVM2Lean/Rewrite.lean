import EvmEquivalence.KEVM2Lean.Func

inductive Rewrites : SortGeneratedTopCell → SortGeneratedTopCell → Prop where
  | tran
    {s1 s2 s3 : SortGeneratedTopCell}
    (t1 : Rewrites s1 s2)
    (t2 : Rewrites s2 s3)
    : Rewrites s1 s3
  | ADDMOD_SUMMARY_ADDMOD_SUMMARY_USEGAS
    {GAS_CELL PC_CELL W0 W1 W2 _Val0 _Val3 _Val4 _Val5 _Val6 _Val7 : SortInt}
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
    {_K_CELL : SortK}
    (defn_Val0 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gmid_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val0)
    (defn_Val1 : «_<=Int_» _Val0 GAS_CELL = some _Val1)
    (defn_Val2 : _andBool_ USEGAS_CELL _Val1 = some _Val2)
    (defn_Val3 : «_+Int_» W0 W1 = some _Val3)
    (defn_Val4 : «_%Word__EVM-TYPES_Int_Int_Int» _Val3 W2 = some _Val4)
    (defn_Val5 : «_+Int_» PC_CELL 1 = some _Val5)
    (defn_Val6 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gmid_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val6)
    (defn_Val7 : «_-Int_» GAS_CELL _Val6 = some _Val7)
    (req : _Val2 = true)
    : Rewrites {
      kevm := {
        k := { val := SortK.kseq ((@inj SortInternalOp SortKItem) (SortInternalOp.«#next[_]_EVM_InternalOp_MaybeOpCode» ((@inj SortTernStackOp SortMaybeOpCode) SortTernStackOp.ADDMOD_EVM_TernStackOp))) _K_CELL },
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
              wordStack := { val := SortWordStack.«_:__EVM-TYPES_WordStack_Int_WordStack» W0 (SortWordStack.«_:__EVM-TYPES_WordStack_Int_WordStack» W1 (SortWordStack.«_:__EVM-TYPES_WordStack_Int_WordStack» W2 WS)) },
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
        k := { val := _K_CELL },
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
  | ADDRESS_SUMMARY_ADDRESS_SUMMARY_USEGAS
    {GAS_CELL ID_CELL PC_CELL _Val0 _Val2 _Val6 _Val7 _Val8 : SortInt}
    {SCHEDULE_CELL : SortSchedule}
    {USEGAS_CELL _Val1 _Val3 _Val4 _Val5 : SortBool}
    {WS : SortWordStack}
    {_DotVar0 : SortGeneratedCounterCell}
    {_DotVar2 : SortNetworkCell}
    {_Gen0 : SortProgramCell}
    {_Gen1 : SortJumpDestsCell}
    {_Gen10 : SortOutputCell}
    {_Gen11 : SortStatusCodeCell}
    {_Gen12 : SortCallStackCell}
    {_Gen13 : SortInterimStatesCell}
    {_Gen14 : SortTouchedAccountsCell}
    {_Gen15 : SortVersionedHashesCell}
    {_Gen16 : SortSubstateCell}
    {_Gen17 : SortGasPriceCell}
    {_Gen18 : SortOriginCell}
    {_Gen19 : SortBlockhashesCell}
    {_Gen2 : SortCallerCell}
    {_Gen20 : SortBlockCell}
    {_Gen21 : SortExitCodeCell}
    {_Gen22 : SortModeCell}
    {_Gen3 : SortCallDataCell}
    {_Gen4 : SortCallValueCell}
    {_Gen5 : SortLocalMemCell}
    {_Gen6 : SortMemoryUsedCell}
    {_Gen7 : SortCallGasCell}
    {_Gen8 : SortStaticCell}
    {_Gen9 : SortCallDepthCell}
    {_K_CELL : SortK}
    (defn_Val0 : sizeWordStackAux WS 0 = some _Val0)
    (defn_Val1 : «_<=Int_» _Val0 1023 = some _Val1)
    (defn_Val2 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gbase_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val2)
    (defn_Val3 : «_<=Int_» _Val2 GAS_CELL = some _Val3)
    (defn_Val4 : _andBool_ _Val1 _Val3 = some _Val4)
    (defn_Val5 : _andBool_ USEGAS_CELL _Val4 = some _Val5)
    (defn_Val6 : «_+Int_» PC_CELL 1 = some _Val6)
    (defn_Val7 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gbase_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val7)
    (defn_Val8 : «_-Int_» GAS_CELL _Val7 = some _Val8)
    (req : _Val5 = true)
    : Rewrites {
      kevm := {
        k := { val := SortK.kseq ((@inj SortInternalOp SortKItem) (SortInternalOp.«#next[_]_EVM_InternalOp_MaybeOpCode» ((@inj SortNullStackOp SortMaybeOpCode) SortNullStackOp.ADDRESS_EVM_NullStackOp))) _K_CELL },
        exitCode := _Gen21,
        mode := _Gen22,
        schedule := { val := SCHEDULE_CELL },
        useGas := { val := USEGAS_CELL },
        ethereum := {
          evm := {
            output := _Gen10,
            statusCode := _Gen11,
            callStack := _Gen12,
            interimStates := _Gen13,
            touchedAccounts := _Gen14,
            callState := {
              program := _Gen0,
              jumpDests := _Gen1,
              id := { val := (@inj SortInt SortAccount) ID_CELL },
              caller := _Gen2,
              callData := _Gen3,
              callValue := _Gen4,
              wordStack := { val := WS },
              localMem := _Gen5,
              pc := { val := PC_CELL },
              gas := { val := (@inj SortInt SortGas) GAS_CELL },
              memoryUsed := _Gen6,
              callGas := _Gen7,
              static := _Gen8,
              callDepth := _Gen9 },
            versionedHashes := _Gen15,
            substate := _Gen16,
            gasPrice := _Gen17,
            origin := _Gen18,
            blockhashes := _Gen19,
            block := _Gen20 },
          network := _DotVar2 } },
      generatedCounter := _DotVar0 } {
      kevm := {
        k := { val := _K_CELL },
        exitCode := _Gen21,
        mode := _Gen22,
        schedule := { val := SCHEDULE_CELL },
        useGas := { val := true },
        ethereum := {
          evm := {
            output := _Gen10,
            statusCode := _Gen11,
            callStack := _Gen12,
            interimStates := _Gen13,
            touchedAccounts := _Gen14,
            callState := {
              program := _Gen0,
              jumpDests := _Gen1,
              id := { val := (@inj SortInt SortAccount) ID_CELL },
              caller := _Gen2,
              callData := _Gen3,
              callValue := _Gen4,
              wordStack := { val := SortWordStack.«_:__EVM-TYPES_WordStack_Int_WordStack» ID_CELL WS },
              localMem := _Gen5,
              pc := { val := _Val6 },
              gas := { val := (@inj SortInt SortGas) _Val8 },
              memoryUsed := _Gen6,
              callGas := _Gen7,
              static := _Gen8,
              callDepth := _Gen9 },
            versionedHashes := _Gen15,
            substate := _Gen16,
            gasPrice := _Gen17,
            origin := _Gen18,
            blockhashes := _Gen19,
            block := _Gen20 },
          network := _DotVar2 } },
      generatedCounter := _DotVar0 }
  | ADD_SUMMARY_ADD_SUMMARY_USEGAS
    {GAS_CELL PC_CELL W0 W1 _Val0 _Val3 _Val4 _Val5 _Val6 _Val7 : SortInt}
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
    {_K_CELL : SortK}
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
        k := { val := SortK.kseq ((@inj SortInternalOp SortKItem) (SortInternalOp.«#next[_]_EVM_InternalOp_MaybeOpCode» ((@inj SortBinStackOp SortMaybeOpCode) SortBinStackOp.ADD_EVM_BinStackOp))) _K_CELL },
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
        k := { val := _K_CELL },
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
  | AND_SUMMARY_AND_SUMMARY_USEGAS
    {GAS_CELL PC_CELL W0 W1 _Val0 _Val3 _Val4 _Val5 _Val6 : SortInt}
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
    {_K_CELL : SortK}
    (defn_Val0 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gverylow_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val0)
    (defn_Val1 : «_<=Int_» _Val0 GAS_CELL = some _Val1)
    (defn_Val2 : _andBool_ USEGAS_CELL _Val1 = some _Val2)
    (defn_Val3 : «_&Int_» W0 W1 = some _Val3)
    (defn_Val4 : «_+Int_» PC_CELL 1 = some _Val4)
    (defn_Val5 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gverylow_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val5)
    (defn_Val6 : «_-Int_» GAS_CELL _Val5 = some _Val6)
    (req : _Val2 = true)
    : Rewrites {
      kevm := {
        k := { val := SortK.kseq ((@inj SortInternalOp SortKItem) (SortInternalOp.«#next[_]_EVM_InternalOp_MaybeOpCode» ((@inj SortBinStackOp SortMaybeOpCode) SortBinStackOp.AND_EVM_BinStackOp))) _K_CELL },
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
        k := { val := _K_CELL },
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
              wordStack := { val := SortWordStack.«_:__EVM-TYPES_WordStack_Int_WordStack» _Val3 WS },
              localMem := _Gen6,
              pc := { val := _Val4 },
              gas := { val := (@inj SortInt SortGas) _Val6 },
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
  | BYTE_SUMMARY_BYTE_SUMMARY_USEGAS
    {GAS_CELL PC_CELL W0 W1 _Val0 _Val3 _Val4 _Val5 _Val6 : SortInt}
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
    {_K_CELL : SortK}
    (defn_Val0 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gverylow_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val0)
    (defn_Val1 : «_<=Int_» _Val0 GAS_CELL = some _Val1)
    (defn_Val2 : _andBool_ USEGAS_CELL _Val1 = some _Val2)
    (defn_Val3 : byte W0 W1 = some _Val3)
    (defn_Val4 : «_+Int_» PC_CELL 1 = some _Val4)
    (defn_Val5 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gverylow_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val5)
    (defn_Val6 : «_-Int_» GAS_CELL _Val5 = some _Val6)
    (req : _Val2 = true)
    : Rewrites {
      kevm := {
        k := { val := SortK.kseq ((@inj SortInternalOp SortKItem) (SortInternalOp.«#next[_]_EVM_InternalOp_MaybeOpCode» ((@inj SortBinStackOp SortMaybeOpCode) SortBinStackOp.BYTE_EVM_BinStackOp))) _K_CELL },
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
        k := { val := _K_CELL },
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
              wordStack := { val := SortWordStack.«_:__EVM-TYPES_WordStack_Int_WordStack» _Val3 WS },
              localMem := _Gen6,
              pc := { val := _Val4 },
              gas := { val := (@inj SortInt SortGas) _Val6 },
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
  | CALLER_SUMMARY_CALLER_SUMMARY_USEGAS
    {CALLER_CELL GAS_CELL PC_CELL _Val0 _Val2 _Val6 _Val7 _Val8 : SortInt}
    {SCHEDULE_CELL : SortSchedule}
    {USEGAS_CELL _Val1 _Val3 _Val4 _Val5 : SortBool}
    {WS : SortWordStack}
    {_DotVar0 : SortGeneratedCounterCell}
    {_DotVar2 : SortNetworkCell}
    {_Gen0 : SortProgramCell}
    {_Gen1 : SortJumpDestsCell}
    {_Gen10 : SortOutputCell}
    {_Gen11 : SortStatusCodeCell}
    {_Gen12 : SortCallStackCell}
    {_Gen13 : SortInterimStatesCell}
    {_Gen14 : SortTouchedAccountsCell}
    {_Gen15 : SortVersionedHashesCell}
    {_Gen16 : SortSubstateCell}
    {_Gen17 : SortGasPriceCell}
    {_Gen18 : SortOriginCell}
    {_Gen19 : SortBlockhashesCell}
    {_Gen2 : SortIdCell}
    {_Gen20 : SortBlockCell}
    {_Gen21 : SortExitCodeCell}
    {_Gen22 : SortModeCell}
    {_Gen3 : SortCallDataCell}
    {_Gen4 : SortCallValueCell}
    {_Gen5 : SortLocalMemCell}
    {_Gen6 : SortMemoryUsedCell}
    {_Gen7 : SortCallGasCell}
    {_Gen8 : SortStaticCell}
    {_Gen9 : SortCallDepthCell}
    {_K_CELL : SortK}
    (defn_Val0 : sizeWordStackAux WS 0 = some _Val0)
    (defn_Val1 : «_<=Int_» _Val0 1023 = some _Val1)
    (defn_Val2 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gbase_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val2)
    (defn_Val3 : «_<=Int_» _Val2 GAS_CELL = some _Val3)
    (defn_Val4 : _andBool_ _Val1 _Val3 = some _Val4)
    (defn_Val5 : _andBool_ USEGAS_CELL _Val4 = some _Val5)
    (defn_Val6 : «_+Int_» PC_CELL 1 = some _Val6)
    (defn_Val7 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gbase_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val7)
    (defn_Val8 : «_-Int_» GAS_CELL _Val7 = some _Val8)
    (req : _Val5 = true)
    : Rewrites {
      kevm := {
        k := { val := SortK.kseq ((@inj SortInternalOp SortKItem) (SortInternalOp.«#next[_]_EVM_InternalOp_MaybeOpCode» ((@inj SortNullStackOp SortMaybeOpCode) SortNullStackOp.CALLER_EVM_NullStackOp))) _K_CELL },
        exitCode := _Gen21,
        mode := _Gen22,
        schedule := { val := SCHEDULE_CELL },
        useGas := { val := USEGAS_CELL },
        ethereum := {
          evm := {
            output := _Gen10,
            statusCode := _Gen11,
            callStack := _Gen12,
            interimStates := _Gen13,
            touchedAccounts := _Gen14,
            callState := {
              program := _Gen0,
              jumpDests := _Gen1,
              id := _Gen2,
              caller := { val := (@inj SortInt SortAccount) CALLER_CELL },
              callData := _Gen3,
              callValue := _Gen4,
              wordStack := { val := WS },
              localMem := _Gen5,
              pc := { val := PC_CELL },
              gas := { val := (@inj SortInt SortGas) GAS_CELL },
              memoryUsed := _Gen6,
              callGas := _Gen7,
              static := _Gen8,
              callDepth := _Gen9 },
            versionedHashes := _Gen15,
            substate := _Gen16,
            gasPrice := _Gen17,
            origin := _Gen18,
            blockhashes := _Gen19,
            block := _Gen20 },
          network := _DotVar2 } },
      generatedCounter := _DotVar0 } {
      kevm := {
        k := { val := _K_CELL },
        exitCode := _Gen21,
        mode := _Gen22,
        schedule := { val := SCHEDULE_CELL },
        useGas := { val := true },
        ethereum := {
          evm := {
            output := _Gen10,
            statusCode := _Gen11,
            callStack := _Gen12,
            interimStates := _Gen13,
            touchedAccounts := _Gen14,
            callState := {
              program := _Gen0,
              jumpDests := _Gen1,
              id := _Gen2,
              caller := { val := (@inj SortInt SortAccount) CALLER_CELL },
              callData := _Gen3,
              callValue := _Gen4,
              wordStack := { val := SortWordStack.«_:__EVM-TYPES_WordStack_Int_WordStack» CALLER_CELL WS },
              localMem := _Gen5,
              pc := { val := _Val6 },
              gas := { val := (@inj SortInt SortGas) _Val8 },
              memoryUsed := _Gen6,
              callGas := _Gen7,
              static := _Gen8,
              callDepth := _Gen9 },
            versionedHashes := _Gen15,
            substate := _Gen16,
            gasPrice := _Gen17,
            origin := _Gen18,
            blockhashes := _Gen19,
            block := _Gen20 },
          network := _DotVar2 } },
      generatedCounter := _DotVar0 }
  | DIV_SUMMARY_DIV_SUMMARY_USEGAS
    {GAS_CELL PC_CELL W0 W1 _Val0 _Val3 _Val4 _Val5 _Val6 : SortInt}
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
    {_K_CELL : SortK}
    (defn_Val0 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Glow_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val0)
    (defn_Val1 : «_<=Int_» _Val0 GAS_CELL = some _Val1)
    (defn_Val2 : _andBool_ USEGAS_CELL _Val1 = some _Val2)
    (defn_Val3 : «_/Word__EVM-TYPES_Int_Int_Int» W0 W1 = some _Val3)
    (defn_Val4 : «_+Int_» PC_CELL 1 = some _Val4)
    (defn_Val5 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Glow_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val5)
    (defn_Val6 : «_-Int_» GAS_CELL _Val5 = some _Val6)
    (req : _Val2 = true)
    : Rewrites {
      kevm := {
        k := { val := SortK.kseq ((@inj SortInternalOp SortKItem) (SortInternalOp.«#next[_]_EVM_InternalOp_MaybeOpCode» ((@inj SortBinStackOp SortMaybeOpCode) SortBinStackOp.DIV_EVM_BinStackOp))) _K_CELL },
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
        k := { val := _K_CELL },
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
              wordStack := { val := SortWordStack.«_:__EVM-TYPES_WordStack_Int_WordStack» _Val3 WS },
              localMem := _Gen6,
              pc := { val := _Val4 },
              gas := { val := (@inj SortInt SortGas) _Val6 },
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
  | EQ_SUMMARY_EQ_SUMMARY_USEGAS
    {GAS_CELL PC_CELL W0 W1 _Val0 _Val4 _Val5 _Val6 _Val7 : SortInt}
    {SCHEDULE_CELL : SortSchedule}
    {USEGAS_CELL _Val1 _Val2 _Val3 : SortBool}
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
    {_K_CELL : SortK}
    (defn_Val0 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gverylow_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val0)
    (defn_Val1 : «_<=Int_» _Val0 GAS_CELL = some _Val1)
    (defn_Val2 : _andBool_ USEGAS_CELL _Val1 = some _Val2)
    (defn_Val3 : «_==Int_» W0 W1 = some _Val3)
    (defn_Val4 : bool2Word _Val3 = some _Val4)
    (defn_Val5 : «_+Int_» PC_CELL 1 = some _Val5)
    (defn_Val6 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gverylow_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val6)
    (defn_Val7 : «_-Int_» GAS_CELL _Val6 = some _Val7)
    (req : _Val2 = true)
    : Rewrites {
      kevm := {
        k := { val := SortK.kseq ((@inj SortInternalOp SortKItem) (SortInternalOp.«#next[_]_EVM_InternalOp_MaybeOpCode» ((@inj SortBinStackOp SortMaybeOpCode) SortBinStackOp.EQ_EVM_BinStackOp))) _K_CELL },
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
        k := { val := _K_CELL },
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
  | EXP_SUMMARY_EXP_SUMMARY_USEGAS
    {GAS_CELL PC_CELL W0 W1 _Val1 _Val11 _Val12 _Val13 _Val14 _Val15 _Val16 _Val17 _Val18 _Val19 _Val2 _Val20 _Val3 _Val4 _Val5 _Val6 _Val7 : SortInt}
    {SCHEDULE_CELL : SortSchedule}
    {USEGAS_CELL _Val0 _Val10 _Val8 _Val9 : SortBool}
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
    {_K_CELL : SortK}
    (defn_Val0 : «_<Int_» 0 W1 = some _Val0)
    (defn_Val1 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gexp_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val1)
    (defn_Val2 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gexpbyte_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val2)
    (defn_Val3 : «log2Int(_)_INT-COMMON_Int_Int» W1 = some _Val3)
    (defn_Val4 : «_/Int_» _Val3 8 = some _Val4)
    (defn_Val5 : «_+Int_» _Val4 1 = some _Val5)
    (defn_Val6 : «_*Int_» _Val2 _Val5 = some _Val6)
    (defn_Val7 : «_+Int_» _Val1 _Val6 = some _Val7)
    (defn_Val8 : «_<=Int_» _Val7 GAS_CELL = some _Val8)
    (defn_Val9 : _andBool_ _Val0 _Val8 = some _Val9)
    (defn_Val10 : _andBool_ USEGAS_CELL _Val9 = some _Val10)
    (defn_Val11 : powmod W0 W1 115792089237316195423570985008687907853269984665640564039457584007913129639936 = some _Val11)
    (defn_Val12 : «_+Int_» PC_CELL 1 = some _Val12)
    (defn_Val13 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gexp_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val13)
    (defn_Val14 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gexpbyte_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val14)
    (defn_Val15 : «log2Int(_)_INT-COMMON_Int_Int» W1 = some _Val15)
    (defn_Val16 : «_/Int_» _Val15 8 = some _Val16)
    (defn_Val17 : «_+Int_» _Val16 1 = some _Val17)
    (defn_Val18 : «_*Int_» _Val14 _Val17 = some _Val18)
    (defn_Val19 : «_+Int_» _Val13 _Val18 = some _Val19)
    (defn_Val20 : «_-Int_» GAS_CELL _Val19 = some _Val20)
    (req : _Val10 = true)
    : Rewrites {
      kevm := {
        k := { val := SortK.kseq ((@inj SortInternalOp SortKItem) (SortInternalOp.«#next[_]_EVM_InternalOp_MaybeOpCode» ((@inj SortBinStackOp SortMaybeOpCode) SortBinStackOp.EXP_EVM_BinStackOp))) _K_CELL },
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
        k := { val := _K_CELL },
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
              wordStack := { val := SortWordStack.«_:__EVM-TYPES_WordStack_Int_WordStack» _Val11 WS },
              localMem := _Gen6,
              pc := { val := _Val12 },
              gas := { val := (@inj SortInt SortGas) _Val20 },
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
  | EXP_SUMMARY_EXP_SUMMARY_USEGAS_LE0
    {GAS_CELL PC_CELL W0 W1 _Val1 _Val5 _Val6 _Val7 _Val8 : SortInt}
    {SCHEDULE_CELL : SortSchedule}
    {USEGAS_CELL _Val0 _Val2 _Val3 _Val4 : SortBool}
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
    {_K_CELL : SortK}
    (defn_Val0 : «_<=Int_» W1 0 = some _Val0)
    (defn_Val1 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gexp_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val1)
    (defn_Val2 : «_<=Int_» _Val1 GAS_CELL = some _Val2)
    (defn_Val3 : _andBool_ _Val0 _Val2 = some _Val3)
    (defn_Val4 : _andBool_ USEGAS_CELL _Val3 = some _Val4)
    (defn_Val5 : powmod W0 W1 115792089237316195423570985008687907853269984665640564039457584007913129639936 = some _Val5)
    (defn_Val6 : «_+Int_» PC_CELL 1 = some _Val6)
    (defn_Val7 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gexp_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val7)
    (defn_Val8 : «_-Int_» GAS_CELL _Val7 = some _Val8)
    (req : _Val4 = true)
    : Rewrites {
      kevm := {
        k := { val := SortK.kseq ((@inj SortInternalOp SortKItem) (SortInternalOp.«#next[_]_EVM_InternalOp_MaybeOpCode» ((@inj SortBinStackOp SortMaybeOpCode) SortBinStackOp.EXP_EVM_BinStackOp))) _K_CELL },
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
        k := { val := _K_CELL },
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
              wordStack := { val := SortWordStack.«_:__EVM-TYPES_WordStack_Int_WordStack» _Val5 WS },
              localMem := _Gen6,
              pc := { val := _Val6 },
              gas := { val := (@inj SortInt SortGas) _Val8 },
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
  | GT_SUMMARY_GT_SUMMARY_USEGAS
    {GAS_CELL PC_CELL W0 W1 _Val0 _Val4 _Val5 _Val6 _Val7 : SortInt}
    {SCHEDULE_CELL : SortSchedule}
    {USEGAS_CELL _Val1 _Val2 _Val3 : SortBool}
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
    {_K_CELL : SortK}
    (defn_Val0 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gverylow_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val0)
    (defn_Val1 : «_<=Int_» _Val0 GAS_CELL = some _Val1)
    (defn_Val2 : _andBool_ USEGAS_CELL _Val1 = some _Val2)
    (defn_Val3 : «_<Int_» W1 W0 = some _Val3)
    (defn_Val4 : bool2Word _Val3 = some _Val4)
    (defn_Val5 : «_+Int_» PC_CELL 1 = some _Val5)
    (defn_Val6 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gverylow_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val6)
    (defn_Val7 : «_-Int_» GAS_CELL _Val6 = some _Val7)
    (req : _Val2 = true)
    : Rewrites {
      kevm := {
        k := { val := SortK.kseq ((@inj SortInternalOp SortKItem) (SortInternalOp.«#next[_]_EVM_InternalOp_MaybeOpCode» ((@inj SortBinStackOp SortMaybeOpCode) SortBinStackOp.GT_EVM_BinStackOp))) _K_CELL },
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
        k := { val := _K_CELL },
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
  | ISZERO_SUMMARY_ISZERO_SUMMARY_USEGAS
    {GAS_CELL PC_CELL W0 _Val0 _Val4 _Val5 _Val6 _Val7 : SortInt}
    {SCHEDULE_CELL : SortSchedule}
    {USEGAS_CELL _Val1 _Val2 _Val3 : SortBool}
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
    {_K_CELL : SortK}
    {_WS : SortWordStack}
    (defn_Val0 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gverylow_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val0)
    (defn_Val1 : «_<=Int_» _Val0 GAS_CELL = some _Val1)
    (defn_Val2 : _andBool_ USEGAS_CELL _Val1 = some _Val2)
    (defn_Val3 : «_==Int_» W0 0 = some _Val3)
    (defn_Val4 : bool2Word _Val3 = some _Val4)
    (defn_Val5 : «_+Int_» PC_CELL 1 = some _Val5)
    (defn_Val6 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gverylow_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val6)
    (defn_Val7 : «_-Int_» GAS_CELL _Val6 = some _Val7)
    (req : _Val2 = true)
    : Rewrites {
      kevm := {
        k := { val := SortK.kseq ((@inj SortInternalOp SortKItem) (SortInternalOp.«#next[_]_EVM_InternalOp_MaybeOpCode» ((@inj SortUnStackOp SortMaybeOpCode) SortUnStackOp.ISZERO_EVM_UnStackOp))) _K_CELL },
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
              wordStack := { val := SortWordStack.«_:__EVM-TYPES_WordStack_Int_WordStack» W0 _WS },
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
        k := { val := _K_CELL },
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
              wordStack := { val := SortWordStack.«_:__EVM-TYPES_WordStack_Int_WordStack» _Val4 _WS },
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
  | LT_SUMMARY_LT_SUMMARY_USEGAS
    {GAS_CELL PC_CELL W0 W1 _Val0 _Val4 _Val5 _Val6 _Val7 : SortInt}
    {SCHEDULE_CELL : SortSchedule}
    {USEGAS_CELL _Val1 _Val2 _Val3 : SortBool}
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
    {_K_CELL : SortK}
    (defn_Val0 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gverylow_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val0)
    (defn_Val1 : «_<=Int_» _Val0 GAS_CELL = some _Val1)
    (defn_Val2 : _andBool_ USEGAS_CELL _Val1 = some _Val2)
    (defn_Val3 : «_<Int_» W0 W1 = some _Val3)
    (defn_Val4 : bool2Word _Val3 = some _Val4)
    (defn_Val5 : «_+Int_» PC_CELL 1 = some _Val5)
    (defn_Val6 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gverylow_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val6)
    (defn_Val7 : «_-Int_» GAS_CELL _Val6 = some _Val7)
    (req : _Val2 = true)
    : Rewrites {
      kevm := {
        k := { val := SortK.kseq ((@inj SortInternalOp SortKItem) (SortInternalOp.«#next[_]_EVM_InternalOp_MaybeOpCode» ((@inj SortBinStackOp SortMaybeOpCode) SortBinStackOp.LT_EVM_BinStackOp))) _K_CELL },
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
        k := { val := _K_CELL },
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
  | MLOAD_SUMMARY_MLOAD_SUMMARY_USEGAS
    {GAS_CELL MEMORYUSED_CELL PC_CELL W0 _Val0 _Val1 _Val10 _Val15 _Val16 _Val17 _Val18 _Val19 _Val2 _Val20 _Val21 _Val22 _Val23 _Val24 _Val3 _Val5 _Val6 _Val7 _Val8 _Val9 : SortInt}
    {LOCALMEM_CELL _Val14 : SortBytes}
    {SCHEDULE_CELL : SortSchedule}
    {USEGAS_CELL _Val11 _Val12 _Val13 _Val4 : SortBool}
    {_DotVar0 : SortGeneratedCounterCell}
    {_DotVar2 : SortNetworkCell}
    {_Gen0 : SortProgramCell}
    {_Gen1 : SortJumpDestsCell}
    {_Gen10 : SortStatusCodeCell}
    {_Gen11 : SortCallStackCell}
    {_Gen12 : SortInterimStatesCell}
    {_Gen13 : SortTouchedAccountsCell}
    {_Gen14 : SortVersionedHashesCell}
    {_Gen15 : SortSubstateCell}
    {_Gen16 : SortGasPriceCell}
    {_Gen17 : SortOriginCell}
    {_Gen18 : SortBlockhashesCell}
    {_Gen19 : SortBlockCell}
    {_Gen2 : SortIdCell}
    {_Gen20 : SortExitCodeCell}
    {_Gen21 : SortModeCell}
    {_Gen3 : SortCallerCell}
    {_Gen4 : SortCallDataCell}
    {_Gen5 : SortCallValueCell}
    {_Gen6 : SortCallGasCell}
    {_Gen7 : SortStaticCell}
    {_Gen8 : SortCallDepthCell}
    {_Gen9 : SortOutputCell}
    {_K_CELL : SortK}
    {_WS : SortWordStack}
    (defn_Val0 : «#memoryUsageUpdate» MEMORYUSED_CELL W0 32 = some _Val0)
    (defn_Val1 : Cmem SCHEDULE_CELL _Val0 = some _Val1)
    (defn_Val2 : Cmem SCHEDULE_CELL MEMORYUSED_CELL = some _Val2)
    (defn_Val3 : «_-Int_» _Val1 _Val2 = some _Val3)
    (defn_Val4 : «_<=Int_» _Val3 GAS_CELL = some _Val4)
    (defn_Val5 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gverylow_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val5)
    (defn_Val6 : «#memoryUsageUpdate» MEMORYUSED_CELL W0 32 = some _Val6)
    (defn_Val7 : Cmem SCHEDULE_CELL _Val6 = some _Val7)
    (defn_Val8 : Cmem SCHEDULE_CELL MEMORYUSED_CELL = some _Val8)
    (defn_Val9 : «_-Int_» _Val7 _Val8 = some _Val9)
    (defn_Val10 : «_-Int_» GAS_CELL _Val9 = some _Val10)
    (defn_Val11 : «_<=Int_» _Val5 _Val10 = some _Val11)
    (defn_Val12 : _andBool_ _Val4 _Val11 = some _Val12)
    (defn_Val13 : _andBool_ USEGAS_CELL _Val12 = some _Val13)
    (defn_Val14 : «#range» LOCALMEM_CELL W0 32 = some _Val14)
    (defn_Val15 : asWord _Val14 = some _Val15)
    (defn_Val16 : «_+Int_» PC_CELL 1 = some _Val16)
    (defn_Val17 : «#memoryUsageUpdate» MEMORYUSED_CELL W0 32 = some _Val17)
    (defn_Val18 : Cmem SCHEDULE_CELL _Val17 = some _Val18)
    (defn_Val19 : Cmem SCHEDULE_CELL MEMORYUSED_CELL = some _Val19)
    (defn_Val20 : «_-Int_» _Val18 _Val19 = some _Val20)
    (defn_Val21 : «_-Int_» GAS_CELL _Val20 = some _Val21)
    (defn_Val22 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gverylow_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val22)
    (defn_Val23 : «_-Int_» _Val21 _Val22 = some _Val23)
    (defn_Val24 : «#memoryUsageUpdate» MEMORYUSED_CELL W0 32 = some _Val24)
    (req : _Val13 = true)
    : Rewrites {
      kevm := {
        k := { val := SortK.kseq ((@inj SortInternalOp SortKItem) (SortInternalOp.«#next[_]_EVM_InternalOp_MaybeOpCode» ((@inj SortUnStackOp SortMaybeOpCode) SortUnStackOp.MLOAD_EVM_UnStackOp))) _K_CELL },
        exitCode := _Gen20,
        mode := _Gen21,
        schedule := { val := SCHEDULE_CELL },
        useGas := { val := USEGAS_CELL },
        ethereum := {
          evm := {
            output := _Gen9,
            statusCode := _Gen10,
            callStack := _Gen11,
            interimStates := _Gen12,
            touchedAccounts := _Gen13,
            callState := {
              program := _Gen0,
              jumpDests := _Gen1,
              id := _Gen2,
              caller := _Gen3,
              callData := _Gen4,
              callValue := _Gen5,
              wordStack := { val := SortWordStack.«_:__EVM-TYPES_WordStack_Int_WordStack» W0 _WS },
              localMem := { val := LOCALMEM_CELL },
              pc := { val := PC_CELL },
              gas := { val := (@inj SortInt SortGas) GAS_CELL },
              memoryUsed := { val := MEMORYUSED_CELL },
              callGas := _Gen6,
              static := _Gen7,
              callDepth := _Gen8 },
            versionedHashes := _Gen14,
            substate := _Gen15,
            gasPrice := _Gen16,
            origin := _Gen17,
            blockhashes := _Gen18,
            block := _Gen19 },
          network := _DotVar2 } },
      generatedCounter := _DotVar0 } {
      kevm := {
        k := { val := _K_CELL },
        exitCode := _Gen20,
        mode := _Gen21,
        schedule := { val := SCHEDULE_CELL },
        useGas := { val := true },
        ethereum := {
          evm := {
            output := _Gen9,
            statusCode := _Gen10,
            callStack := _Gen11,
            interimStates := _Gen12,
            touchedAccounts := _Gen13,
            callState := {
              program := _Gen0,
              jumpDests := _Gen1,
              id := _Gen2,
              caller := _Gen3,
              callData := _Gen4,
              callValue := _Gen5,
              wordStack := { val := SortWordStack.«_:__EVM-TYPES_WordStack_Int_WordStack» _Val15 _WS },
              localMem := { val := LOCALMEM_CELL },
              pc := { val := _Val16 },
              gas := { val := (@inj SortInt SortGas) _Val23 },
              memoryUsed := { val := _Val24 },
              callGas := _Gen6,
              static := _Gen7,
              callDepth := _Gen8 },
            versionedHashes := _Gen14,
            substate := _Gen15,
            gasPrice := _Gen16,
            origin := _Gen17,
            blockhashes := _Gen18,
            block := _Gen19 },
          network := _DotVar2 } },
      generatedCounter := _DotVar0 }
  | MOD_SUMMARY_MOD_SUMMARY_USEGAS
    {GAS_CELL PC_CELL W0 W1 _Val0 _Val3 _Val4 _Val5 _Val6 : SortInt}
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
    {_K_CELL : SortK}
    (defn_Val0 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Glow_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val0)
    (defn_Val1 : «_<=Int_» _Val0 GAS_CELL = some _Val1)
    (defn_Val2 : _andBool_ USEGAS_CELL _Val1 = some _Val2)
    (defn_Val3 : «_%Word__EVM-TYPES_Int_Int_Int» W0 W1 = some _Val3)
    (defn_Val4 : «_+Int_» PC_CELL 1 = some _Val4)
    (defn_Val5 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Glow_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val5)
    (defn_Val6 : «_-Int_» GAS_CELL _Val5 = some _Val6)
    (req : _Val2 = true)
    : Rewrites {
      kevm := {
        k := { val := SortK.kseq ((@inj SortInternalOp SortKItem) (SortInternalOp.«#next[_]_EVM_InternalOp_MaybeOpCode» ((@inj SortBinStackOp SortMaybeOpCode) SortBinStackOp.MOD_EVM_BinStackOp))) _K_CELL },
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
        k := { val := _K_CELL },
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
              wordStack := { val := SortWordStack.«_:__EVM-TYPES_WordStack_Int_WordStack» _Val3 WS },
              localMem := _Gen6,
              pc := { val := _Val4 },
              gas := { val := (@inj SortInt SortGas) _Val6 },
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
  | MSTORE8_SUMMARY_MSTORE8_SUMMARY_USEGAS
    {GAS_CELL MEMORYUSED_CELL PC_CELL W0 W1 _Val0 _Val1 _Val10 _Val14 _Val17 _Val18 _Val19 _Val2 _Val20 _Val21 _Val22 _Val23 _Val24 _Val25 _Val3 _Val5 _Val6 _Val7 _Val8 _Val9 : SortInt}
    {LOCALMEM_CELL _Val15 _Val16 : SortBytes}
    {SCHEDULE_CELL : SortSchedule}
    {USEGAS_CELL _Val11 _Val12 _Val13 _Val4 : SortBool}
    {WS : SortWordStack}
    {_DotVar0 : SortGeneratedCounterCell}
    {_DotVar2 : SortNetworkCell}
    {_Gen0 : SortProgramCell}
    {_Gen1 : SortJumpDestsCell}
    {_Gen10 : SortStatusCodeCell}
    {_Gen11 : SortCallStackCell}
    {_Gen12 : SortInterimStatesCell}
    {_Gen13 : SortTouchedAccountsCell}
    {_Gen14 : SortVersionedHashesCell}
    {_Gen15 : SortSubstateCell}
    {_Gen16 : SortGasPriceCell}
    {_Gen17 : SortOriginCell}
    {_Gen18 : SortBlockhashesCell}
    {_Gen19 : SortBlockCell}
    {_Gen2 : SortIdCell}
    {_Gen20 : SortExitCodeCell}
    {_Gen21 : SortModeCell}
    {_Gen3 : SortCallerCell}
    {_Gen4 : SortCallDataCell}
    {_Gen5 : SortCallValueCell}
    {_Gen6 : SortCallGasCell}
    {_Gen7 : SortStaticCell}
    {_Gen8 : SortCallDepthCell}
    {_Gen9 : SortOutputCell}
    {_K_CELL : SortK}
    (defn_Val0 : «#memoryUsageUpdate» MEMORYUSED_CELL W0 1 = some _Val0)
    (defn_Val1 : Cmem SCHEDULE_CELL _Val0 = some _Val1)
    (defn_Val2 : Cmem SCHEDULE_CELL MEMORYUSED_CELL = some _Val2)
    (defn_Val3 : «_-Int_» _Val1 _Val2 = some _Val3)
    (defn_Val4 : «_<=Int_» _Val3 GAS_CELL = some _Val4)
    (defn_Val5 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gverylow_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val5)
    (defn_Val6 : «#memoryUsageUpdate» MEMORYUSED_CELL W0 1 = some _Val6)
    (defn_Val7 : Cmem SCHEDULE_CELL _Val6 = some _Val7)
    (defn_Val8 : Cmem SCHEDULE_CELL MEMORYUSED_CELL = some _Val8)
    (defn_Val9 : «_-Int_» _Val7 _Val8 = some _Val9)
    (defn_Val10 : «_-Int_» GAS_CELL _Val9 = some _Val10)
    (defn_Val11 : «_<=Int_» _Val5 _Val10 = some _Val11)
    (defn_Val12 : _andBool_ _Val4 _Val11 = some _Val12)
    (defn_Val13 : _andBool_ USEGAS_CELL _Val12 = some _Val13)
    (defn_Val14 : _modInt_ W1 256 = some _Val14)
    (defn_Val15 : buf 1 _Val14 = some _Val15)
    (defn_Val16 : mapWriteRange LOCALMEM_CELL W0 _Val15 = some _Val16)
    (defn_Val17 : «_+Int_» PC_CELL 1 = some _Val17)
    (defn_Val18 : «#memoryUsageUpdate» MEMORYUSED_CELL W0 1 = some _Val18)
    (defn_Val19 : Cmem SCHEDULE_CELL _Val18 = some _Val19)
    (defn_Val20 : Cmem SCHEDULE_CELL MEMORYUSED_CELL = some _Val20)
    (defn_Val21 : «_-Int_» _Val19 _Val20 = some _Val21)
    (defn_Val22 : «_-Int_» GAS_CELL _Val21 = some _Val22)
    (defn_Val23 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gverylow_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val23)
    (defn_Val24 : «_-Int_» _Val22 _Val23 = some _Val24)
    (defn_Val25 : «#memoryUsageUpdate» MEMORYUSED_CELL W0 1 = some _Val25)
    (req : _Val13 = true)
    : Rewrites {
      kevm := {
        k := { val := SortK.kseq ((@inj SortInternalOp SortKItem) (SortInternalOp.«#next[_]_EVM_InternalOp_MaybeOpCode» ((@inj SortBinStackOp SortMaybeOpCode) SortBinStackOp.MSTORE8_EVM_BinStackOp))) _K_CELL },
        exitCode := _Gen20,
        mode := _Gen21,
        schedule := { val := SCHEDULE_CELL },
        useGas := { val := USEGAS_CELL },
        ethereum := {
          evm := {
            output := _Gen9,
            statusCode := _Gen10,
            callStack := _Gen11,
            interimStates := _Gen12,
            touchedAccounts := _Gen13,
            callState := {
              program := _Gen0,
              jumpDests := _Gen1,
              id := _Gen2,
              caller := _Gen3,
              callData := _Gen4,
              callValue := _Gen5,
              wordStack := { val := SortWordStack.«_:__EVM-TYPES_WordStack_Int_WordStack» W0 (SortWordStack.«_:__EVM-TYPES_WordStack_Int_WordStack» W1 WS) },
              localMem := { val := LOCALMEM_CELL },
              pc := { val := PC_CELL },
              gas := { val := (@inj SortInt SortGas) GAS_CELL },
              memoryUsed := { val := MEMORYUSED_CELL },
              callGas := _Gen6,
              static := _Gen7,
              callDepth := _Gen8 },
            versionedHashes := _Gen14,
            substate := _Gen15,
            gasPrice := _Gen16,
            origin := _Gen17,
            blockhashes := _Gen18,
            block := _Gen19 },
          network := _DotVar2 } },
      generatedCounter := _DotVar0 } {
      kevm := {
        k := { val := _K_CELL },
        exitCode := _Gen20,
        mode := _Gen21,
        schedule := { val := SCHEDULE_CELL },
        useGas := { val := true },
        ethereum := {
          evm := {
            output := _Gen9,
            statusCode := _Gen10,
            callStack := _Gen11,
            interimStates := _Gen12,
            touchedAccounts := _Gen13,
            callState := {
              program := _Gen0,
              jumpDests := _Gen1,
              id := _Gen2,
              caller := _Gen3,
              callData := _Gen4,
              callValue := _Gen5,
              wordStack := { val := WS },
              localMem := { val := _Val16 },
              pc := { val := _Val17 },
              gas := { val := (@inj SortInt SortGas) _Val24 },
              memoryUsed := { val := _Val25 },
              callGas := _Gen6,
              static := _Gen7,
              callDepth := _Gen8 },
            versionedHashes := _Gen14,
            substate := _Gen15,
            gasPrice := _Gen16,
            origin := _Gen17,
            blockhashes := _Gen18,
            block := _Gen19 },
          network := _DotVar2 } },
      generatedCounter := _DotVar0 }
  | MSTORE_SUMMARY_MSTORE_SUMMARY_USEGAS
    {GAS_CELL MEMORYUSED_CELL PC_CELL W0 W1 _Val0 _Val1 _Val10 _Val17 _Val18 _Val19 _Val2 _Val20 _Val21 _Val22 _Val23 _Val24 _Val25 _Val3 _Val5 _Val6 _Val7 _Val8 _Val9 : SortInt}
    {LOCALMEM_CELL _Val14 _Val15 _Val16 : SortBytes}
    {SCHEDULE_CELL : SortSchedule}
    {USEGAS_CELL _Val11 _Val12 _Val13 _Val4 : SortBool}
    {WS : SortWordStack}
    {_DotVar0 : SortGeneratedCounterCell}
    {_DotVar2 : SortNetworkCell}
    {_Gen0 : SortProgramCell}
    {_Gen1 : SortJumpDestsCell}
    {_Gen10 : SortStatusCodeCell}
    {_Gen11 : SortCallStackCell}
    {_Gen12 : SortInterimStatesCell}
    {_Gen13 : SortTouchedAccountsCell}
    {_Gen14 : SortVersionedHashesCell}
    {_Gen15 : SortSubstateCell}
    {_Gen16 : SortGasPriceCell}
    {_Gen17 : SortOriginCell}
    {_Gen18 : SortBlockhashesCell}
    {_Gen19 : SortBlockCell}
    {_Gen2 : SortIdCell}
    {_Gen20 : SortExitCodeCell}
    {_Gen21 : SortModeCell}
    {_Gen3 : SortCallerCell}
    {_Gen4 : SortCallDataCell}
    {_Gen5 : SortCallValueCell}
    {_Gen6 : SortCallGasCell}
    {_Gen7 : SortStaticCell}
    {_Gen8 : SortCallDepthCell}
    {_Gen9 : SortOutputCell}
    {_K_CELL : SortK}
    (defn_Val0 : «#memoryUsageUpdate» MEMORYUSED_CELL W0 32 = some _Val0)
    (defn_Val1 : Cmem SCHEDULE_CELL _Val0 = some _Val1)
    (defn_Val2 : Cmem SCHEDULE_CELL MEMORYUSED_CELL = some _Val2)
    (defn_Val3 : «_-Int_» _Val1 _Val2 = some _Val3)
    (defn_Val4 : «_<=Int_» _Val3 GAS_CELL = some _Val4)
    (defn_Val5 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gverylow_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val5)
    (defn_Val6 : «#memoryUsageUpdate» MEMORYUSED_CELL W0 32 = some _Val6)
    (defn_Val7 : Cmem SCHEDULE_CELL _Val6 = some _Val7)
    (defn_Val8 : Cmem SCHEDULE_CELL MEMORYUSED_CELL = some _Val8)
    (defn_Val9 : «_-Int_» _Val7 _Val8 = some _Val9)
    (defn_Val10 : «_-Int_» GAS_CELL _Val9 = some _Val10)
    (defn_Val11 : «_<=Int_» _Val5 _Val10 = some _Val11)
    (defn_Val12 : _andBool_ _Val4 _Val11 = some _Val12)
    (defn_Val13 : _andBool_ USEGAS_CELL _Val12 = some _Val13)
    (defn_Val14 : «#asByteStack» W1 = some _Val14)
    (defn_Val15 : «#padToWidth» 32 _Val14 = some _Val15)
    (defn_Val16 : mapWriteRange LOCALMEM_CELL W0 _Val15 = some _Val16)
    (defn_Val17 : «_+Int_» PC_CELL 1 = some _Val17)
    (defn_Val18 : «#memoryUsageUpdate» MEMORYUSED_CELL W0 32 = some _Val18)
    (defn_Val19 : Cmem SCHEDULE_CELL _Val18 = some _Val19)
    (defn_Val20 : Cmem SCHEDULE_CELL MEMORYUSED_CELL = some _Val20)
    (defn_Val21 : «_-Int_» _Val19 _Val20 = some _Val21)
    (defn_Val22 : «_-Int_» GAS_CELL _Val21 = some _Val22)
    (defn_Val23 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gverylow_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val23)
    (defn_Val24 : «_-Int_» _Val22 _Val23 = some _Val24)
    (defn_Val25 : «#memoryUsageUpdate» MEMORYUSED_CELL W0 32 = some _Val25)
    (req : _Val13 = true)
    : Rewrites {
      kevm := {
        k := { val := SortK.kseq ((@inj SortInternalOp SortKItem) (SortInternalOp.«#next[_]_EVM_InternalOp_MaybeOpCode» ((@inj SortBinStackOp SortMaybeOpCode) SortBinStackOp.MSTORE_EVM_BinStackOp))) _K_CELL },
        exitCode := _Gen20,
        mode := _Gen21,
        schedule := { val := SCHEDULE_CELL },
        useGas := { val := USEGAS_CELL },
        ethereum := {
          evm := {
            output := _Gen9,
            statusCode := _Gen10,
            callStack := _Gen11,
            interimStates := _Gen12,
            touchedAccounts := _Gen13,
            callState := {
              program := _Gen0,
              jumpDests := _Gen1,
              id := _Gen2,
              caller := _Gen3,
              callData := _Gen4,
              callValue := _Gen5,
              wordStack := { val := SortWordStack.«_:__EVM-TYPES_WordStack_Int_WordStack» W0 (SortWordStack.«_:__EVM-TYPES_WordStack_Int_WordStack» W1 WS) },
              localMem := { val := LOCALMEM_CELL },
              pc := { val := PC_CELL },
              gas := { val := (@inj SortInt SortGas) GAS_CELL },
              memoryUsed := { val := MEMORYUSED_CELL },
              callGas := _Gen6,
              static := _Gen7,
              callDepth := _Gen8 },
            versionedHashes := _Gen14,
            substate := _Gen15,
            gasPrice := _Gen16,
            origin := _Gen17,
            blockhashes := _Gen18,
            block := _Gen19 },
          network := _DotVar2 } },
      generatedCounter := _DotVar0 } {
      kevm := {
        k := { val := _K_CELL },
        exitCode := _Gen20,
        mode := _Gen21,
        schedule := { val := SCHEDULE_CELL },
        useGas := { val := true },
        ethereum := {
          evm := {
            output := _Gen9,
            statusCode := _Gen10,
            callStack := _Gen11,
            interimStates := _Gen12,
            touchedAccounts := _Gen13,
            callState := {
              program := _Gen0,
              jumpDests := _Gen1,
              id := _Gen2,
              caller := _Gen3,
              callData := _Gen4,
              callValue := _Gen5,
              wordStack := { val := WS },
              localMem := { val := _Val16 },
              pc := { val := _Val17 },
              gas := { val := (@inj SortInt SortGas) _Val24 },
              memoryUsed := { val := _Val25 },
              callGas := _Gen6,
              static := _Gen7,
              callDepth := _Gen8 },
            versionedHashes := _Gen14,
            substate := _Gen15,
            gasPrice := _Gen16,
            origin := _Gen17,
            blockhashes := _Gen18,
            block := _Gen19 },
          network := _DotVar2 } },
      generatedCounter := _DotVar0 }
  | MULMOD_SUMMARY_MULMOD_SUMMARY_USEGAS
    {GAS_CELL PC_CELL W0 W1 W2 _Val0 _Val3 _Val4 _Val5 _Val6 _Val7 : SortInt}
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
    {_K_CELL : SortK}
    (defn_Val0 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gmid_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val0)
    (defn_Val1 : «_<=Int_» _Val0 GAS_CELL = some _Val1)
    (defn_Val2 : _andBool_ USEGAS_CELL _Val1 = some _Val2)
    (defn_Val3 : «_*Int_» W0 W1 = some _Val3)
    (defn_Val4 : «_%Word__EVM-TYPES_Int_Int_Int» _Val3 W2 = some _Val4)
    (defn_Val5 : «_+Int_» PC_CELL 1 = some _Val5)
    (defn_Val6 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gmid_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val6)
    (defn_Val7 : «_-Int_» GAS_CELL _Val6 = some _Val7)
    (req : _Val2 = true)
    : Rewrites {
      kevm := {
        k := { val := SortK.kseq ((@inj SortInternalOp SortKItem) (SortInternalOp.«#next[_]_EVM_InternalOp_MaybeOpCode» ((@inj SortTernStackOp SortMaybeOpCode) SortTernStackOp.MULMOD_EVM_TernStackOp))) _K_CELL },
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
              wordStack := { val := SortWordStack.«_:__EVM-TYPES_WordStack_Int_WordStack» W0 (SortWordStack.«_:__EVM-TYPES_WordStack_Int_WordStack» W1 (SortWordStack.«_:__EVM-TYPES_WordStack_Int_WordStack» W2 WS)) },
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
        k := { val := _K_CELL },
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
  | NOT_SUMMARY_NOT_SUMMARY_USEGAS
    {GAS_CELL PC_CELL W0 _Val0 _Val3 _Val4 _Val5 _Val6 : SortInt}
    {SCHEDULE_CELL : SortSchedule}
    {USEGAS_CELL _Val1 _Val2 : SortBool}
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
    {_K_CELL : SortK}
    {_WS : SortWordStack}
    (defn_Val0 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gverylow_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val0)
    (defn_Val1 : «_<=Int_» _Val0 GAS_CELL = some _Val1)
    (defn_Val2 : _andBool_ USEGAS_CELL _Val1 = some _Val2)
    (defn_Val3 : _xorInt_ W0 115792089237316195423570985008687907853269984665640564039457584007913129639935 = some _Val3)
    (defn_Val4 : «_+Int_» PC_CELL 1 = some _Val4)
    (defn_Val5 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gverylow_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val5)
    (defn_Val6 : «_-Int_» GAS_CELL _Val5 = some _Val6)
    (req : _Val2 = true)
    : Rewrites {
      kevm := {
        k := { val := SortK.kseq ((@inj SortInternalOp SortKItem) (SortInternalOp.«#next[_]_EVM_InternalOp_MaybeOpCode» ((@inj SortUnStackOp SortMaybeOpCode) SortUnStackOp.NOT_EVM_UnStackOp))) _K_CELL },
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
              wordStack := { val := SortWordStack.«_:__EVM-TYPES_WordStack_Int_WordStack» W0 _WS },
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
        k := { val := _K_CELL },
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
              wordStack := { val := SortWordStack.«_:__EVM-TYPES_WordStack_Int_WordStack» _Val3 _WS },
              localMem := _Gen6,
              pc := { val := _Val4 },
              gas := { val := (@inj SortInt SortGas) _Val6 },
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
  | ORIGIN_SUMMARY_ORIGIN_SUMMARY_USEGAS
    {GAS_CELL ORIGIN_CELL PC_CELL _Val0 _Val2 _Val6 _Val7 _Val8 : SortInt}
    {SCHEDULE_CELL : SortSchedule}
    {USEGAS_CELL _Val1 _Val3 _Val4 _Val5 : SortBool}
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
    {_Gen19 : SortBlockhashesCell}
    {_Gen2 : SortIdCell}
    {_Gen20 : SortBlockCell}
    {_Gen21 : SortExitCodeCell}
    {_Gen22 : SortModeCell}
    {_Gen3 : SortCallerCell}
    {_Gen4 : SortCallDataCell}
    {_Gen5 : SortCallValueCell}
    {_Gen6 : SortLocalMemCell}
    {_Gen7 : SortMemoryUsedCell}
    {_Gen8 : SortCallGasCell}
    {_Gen9 : SortStaticCell}
    {_K_CELL : SortK}
    (defn_Val0 : sizeWordStackAux WS 0 = some _Val0)
    (defn_Val1 : «_<=Int_» _Val0 1023 = some _Val1)
    (defn_Val2 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gbase_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val2)
    (defn_Val3 : «_<=Int_» _Val2 GAS_CELL = some _Val3)
    (defn_Val4 : _andBool_ _Val1 _Val3 = some _Val4)
    (defn_Val5 : _andBool_ USEGAS_CELL _Val4 = some _Val5)
    (defn_Val6 : «_+Int_» PC_CELL 1 = some _Val6)
    (defn_Val7 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gbase_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val7)
    (defn_Val8 : «_-Int_» GAS_CELL _Val7 = some _Val8)
    (req : _Val5 = true)
    : Rewrites {
      kevm := {
        k := { val := SortK.kseq ((@inj SortInternalOp SortKItem) (SortInternalOp.«#next[_]_EVM_InternalOp_MaybeOpCode» ((@inj SortNullStackOp SortMaybeOpCode) SortNullStackOp.ORIGIN_EVM_NullStackOp))) _K_CELL },
        exitCode := _Gen21,
        mode := _Gen22,
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
            origin := { val := (@inj SortInt SortAccount) ORIGIN_CELL },
            blockhashes := _Gen19,
            block := _Gen20 },
          network := _DotVar2 } },
      generatedCounter := _DotVar0 } {
      kevm := {
        k := { val := _K_CELL },
        exitCode := _Gen21,
        mode := _Gen22,
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
              wordStack := { val := SortWordStack.«_:__EVM-TYPES_WordStack_Int_WordStack» ORIGIN_CELL WS },
              localMem := _Gen6,
              pc := { val := _Val6 },
              gas := { val := (@inj SortInt SortGas) _Val8 },
              memoryUsed := _Gen7,
              callGas := _Gen8,
              static := _Gen9,
              callDepth := _Gen10 },
            versionedHashes := _Gen16,
            substate := _Gen17,
            gasPrice := _Gen18,
            origin := { val := (@inj SortInt SortAccount) ORIGIN_CELL },
            blockhashes := _Gen19,
            block := _Gen20 },
          network := _DotVar2 } },
      generatedCounter := _DotVar0 }
  | PUSHZERO_SUMMARY_PUSHZERO_SUMMARY_USEGAS
    {GAS_CELL PC_CELL _Val0 _Val2 _Val6 _Val7 _Val8 : SortInt}
    {SCHEDULE_CELL : SortSchedule}
    {USEGAS_CELL _Val1 _Val3 _Val4 _Val5 : SortBool}
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
    {_K_CELL : SortK}
    (defn_Val0 : sizeWordStackAux WS 0 = some _Val0)
    (defn_Val1 : «_<=Int_» _Val0 1023 = some _Val1)
    (defn_Val2 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gbase_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val2)
    (defn_Val3 : «_<=Int_» _Val2 GAS_CELL = some _Val3)
    (defn_Val4 : _andBool_ _Val1 _Val3 = some _Val4)
    (defn_Val5 : _andBool_ USEGAS_CELL _Val4 = some _Val5)
    (defn_Val6 : «_+Int_» PC_CELL 1 = some _Val6)
    (defn_Val7 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gbase_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val7)
    (defn_Val8 : «_-Int_» GAS_CELL _Val7 = some _Val8)
    (req : _Val5 = true)
    : Rewrites {
      kevm := {
        k := { val := SortK.kseq ((@inj SortInternalOp SortKItem) (SortInternalOp.«#next[_]_EVM_InternalOp_MaybeOpCode» ((@inj SortPushOp SortMaybeOpCode) SortPushOp.PUSHZERO_EVM_PushOp))) _K_CELL },
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
        k := { val := _K_CELL },
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
              pc := { val := _Val6 },
              gas := { val := (@inj SortInt SortGas) _Val8 },
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
  | SAR_SUMMARY_SAR_SUMMARY_USEGAS
    {GAS_CELL PC_CELL W0 W1 _Val0 _Val3 _Val4 _Val5 _Val6 : SortInt}
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
    {_K_CELL : SortK}
    (defn_Val0 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gverylow_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val0)
    (defn_Val1 : «_<=Int_» _Val0 GAS_CELL = some _Val1)
    (defn_Val2 : _andBool_ USEGAS_CELL _Val1 = some _Val2)
    (defn_Val3 : «_>>sWord__EVM-TYPES_Int_Int_Int» W1 W0 = some _Val3)
    (defn_Val4 : «_+Int_» PC_CELL 1 = some _Val4)
    (defn_Val5 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gverylow_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val5)
    (defn_Val6 : «_-Int_» GAS_CELL _Val5 = some _Val6)
    (req : _Val2 = true)
    : Rewrites {
      kevm := {
        k := { val := SortK.kseq ((@inj SortInternalOp SortKItem) (SortInternalOp.«#next[_]_EVM_InternalOp_MaybeOpCode» ((@inj SortBinStackOp SortMaybeOpCode) SortBinStackOp.SAR_EVM_BinStackOp))) _K_CELL },
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
        k := { val := _K_CELL },
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
              wordStack := { val := SortWordStack.«_:__EVM-TYPES_WordStack_Int_WordStack» _Val3 WS },
              localMem := _Gen6,
              pc := { val := _Val4 },
              gas := { val := (@inj SortInt SortGas) _Val6 },
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
  | SDIV_SUMMARY_SDIV_SUMMARY_USEGAS
    {GAS_CELL PC_CELL W0 W1 _Val0 _Val3 _Val4 _Val5 _Val6 : SortInt}
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
    {_K_CELL : SortK}
    (defn_Val0 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Glow_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val0)
    (defn_Val1 : «_<=Int_» _Val0 GAS_CELL = some _Val1)
    (defn_Val2 : _andBool_ USEGAS_CELL _Val1 = some _Val2)
    (defn_Val3 : «_/sWord__EVM-TYPES_Int_Int_Int» W0 W1 = some _Val3)
    (defn_Val4 : «_+Int_» PC_CELL 1 = some _Val4)
    (defn_Val5 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Glow_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val5)
    (defn_Val6 : «_-Int_» GAS_CELL _Val5 = some _Val6)
    (req : _Val2 = true)
    : Rewrites {
      kevm := {
        k := { val := SortK.kseq ((@inj SortInternalOp SortKItem) (SortInternalOp.«#next[_]_EVM_InternalOp_MaybeOpCode» ((@inj SortBinStackOp SortMaybeOpCode) SortBinStackOp.SDIV_EVM_BinStackOp))) _K_CELL },
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
        k := { val := _K_CELL },
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
              wordStack := { val := SortWordStack.«_:__EVM-TYPES_WordStack_Int_WordStack» _Val3 WS },
              localMem := _Gen6,
              pc := { val := _Val4 },
              gas := { val := (@inj SortInt SortGas) _Val6 },
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
  | SGT_SUMMARY_SGT_SUMMARY_USEGAS
    {GAS_CELL PC_CELL W0 W1 _Val0 _Val3 _Val4 _Val5 _Val6 : SortInt}
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
    {_K_CELL : SortK}
    (defn_Val0 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gverylow_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val0)
    (defn_Val1 : «_<=Int_» _Val0 GAS_CELL = some _Val1)
    (defn_Val2 : _andBool_ USEGAS_CELL _Val1 = some _Val2)
    (defn_Val3 : «_s<Word__EVM-TYPES_Int_Int_Int» W1 W0 = some _Val3)
    (defn_Val4 : «_+Int_» PC_CELL 1 = some _Val4)
    (defn_Val5 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gverylow_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val5)
    (defn_Val6 : «_-Int_» GAS_CELL _Val5 = some _Val6)
    (req : _Val2 = true)
    : Rewrites {
      kevm := {
        k := { val := SortK.kseq ((@inj SortInternalOp SortKItem) (SortInternalOp.«#next[_]_EVM_InternalOp_MaybeOpCode» ((@inj SortBinStackOp SortMaybeOpCode) SortBinStackOp.SGT_EVM_BinStackOp))) _K_CELL },
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
        k := { val := _K_CELL },
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
              wordStack := { val := SortWordStack.«_:__EVM-TYPES_WordStack_Int_WordStack» _Val3 WS },
              localMem := _Gen6,
              pc := { val := _Val4 },
              gas := { val := (@inj SortInt SortGas) _Val6 },
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
  | SHL_SUMMARY_SHL_SUMMARY_USEGAS
    {GAS_CELL PC_CELL W0 W1 _Val0 _Val3 _Val4 _Val5 _Val6 : SortInt}
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
    {_K_CELL : SortK}
    (defn_Val0 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gverylow_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val0)
    (defn_Val1 : «_<=Int_» _Val0 GAS_CELL = some _Val1)
    (defn_Val2 : _andBool_ USEGAS_CELL _Val1 = some _Val2)
    (defn_Val3 : «_<<Word__EVM-TYPES_Int_Int_Int» W1 W0 = some _Val3)
    (defn_Val4 : «_+Int_» PC_CELL 1 = some _Val4)
    (defn_Val5 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gverylow_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val5)
    (defn_Val6 : «_-Int_» GAS_CELL _Val5 = some _Val6)
    (req : _Val2 = true)
    : Rewrites {
      kevm := {
        k := { val := SortK.kseq ((@inj SortInternalOp SortKItem) (SortInternalOp.«#next[_]_EVM_InternalOp_MaybeOpCode» ((@inj SortBinStackOp SortMaybeOpCode) SortBinStackOp.SHL_EVM_BinStackOp))) _K_CELL },
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
        k := { val := _K_CELL },
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
              wordStack := { val := SortWordStack.«_:__EVM-TYPES_WordStack_Int_WordStack» _Val3 WS },
              localMem := _Gen6,
              pc := { val := _Val4 },
              gas := { val := (@inj SortInt SortGas) _Val6 },
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
  | SHR_SUMMARY_SHR_SUMMARY_USEGAS
    {GAS_CELL PC_CELL W0 W1 _Val0 _Val3 _Val4 _Val5 _Val6 : SortInt}
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
    {_K_CELL : SortK}
    (defn_Val0 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gverylow_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val0)
    (defn_Val1 : «_<=Int_» _Val0 GAS_CELL = some _Val1)
    (defn_Val2 : _andBool_ USEGAS_CELL _Val1 = some _Val2)
    (defn_Val3 : «_>>Word__EVM-TYPES_Int_Int_Int» W1 W0 = some _Val3)
    (defn_Val4 : «_+Int_» PC_CELL 1 = some _Val4)
    (defn_Val5 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gverylow_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val5)
    (defn_Val6 : «_-Int_» GAS_CELL _Val5 = some _Val6)
    (req : _Val2 = true)
    : Rewrites {
      kevm := {
        k := { val := SortK.kseq ((@inj SortInternalOp SortKItem) (SortInternalOp.«#next[_]_EVM_InternalOp_MaybeOpCode» ((@inj SortBinStackOp SortMaybeOpCode) SortBinStackOp.SHR_EVM_BinStackOp))) _K_CELL },
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
        k := { val := _K_CELL },
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
              wordStack := { val := SortWordStack.«_:__EVM-TYPES_WordStack_Int_WordStack» _Val3 WS },
              localMem := _Gen6,
              pc := { val := _Val4 },
              gas := { val := (@inj SortInt SortGas) _Val6 },
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
  | SIGNEXTEND_SUMMARY_SIGNEXTEND_SUMMARY_USEGAS
    {GAS_CELL PC_CELL W0 W1 _Val0 _Val3 _Val4 _Val5 _Val6 : SortInt}
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
    {_K_CELL : SortK}
    (defn_Val0 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Glow_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val0)
    (defn_Val1 : «_<=Int_» _Val0 GAS_CELL = some _Val1)
    (defn_Val2 : _andBool_ USEGAS_CELL _Val1 = some _Val2)
    (defn_Val3 : signextend W0 W1 = some _Val3)
    (defn_Val4 : «_+Int_» PC_CELL 1 = some _Val4)
    (defn_Val5 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Glow_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val5)
    (defn_Val6 : «_-Int_» GAS_CELL _Val5 = some _Val6)
    (req : _Val2 = true)
    : Rewrites {
      kevm := {
        k := { val := SortK.kseq ((@inj SortInternalOp SortKItem) (SortInternalOp.«#next[_]_EVM_InternalOp_MaybeOpCode» ((@inj SortBinStackOp SortMaybeOpCode) SortBinStackOp.SIGNEXTEND_EVM_BinStackOp))) _K_CELL },
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
        k := { val := _K_CELL },
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
              wordStack := { val := SortWordStack.«_:__EVM-TYPES_WordStack_Int_WordStack» _Val3 WS },
              localMem := _Gen6,
              pc := { val := _Val4 },
              gas := { val := (@inj SortInt SortGas) _Val6 },
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
  | SLOAD_SUMMARY_SLOAD_SUMMARY_USEGAS_BERLIN
    {ACCESSEDSTORAGE_CELL STORAGE_CELL _Val22 : SortMap}
    {GAS_CELL ID_CELL PC_CELL W0 _Val10 _Val11 _Val13 _Val14 _Val15 _Val16 _Val2 _Val3 _Val4 : SortInt}
    {SCHEDULE_CELL : SortSchedule}
    {USEGAS_CELL _Val0 _Val1 _Val12 _Val5 _Val6 _Val7 : SortBool}
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
    {_K_CELL : SortK}
    {_Val17 _Val19 _Val20 _Val21 : SortSet}
    {_Val18 : SortKItem}
    {_WS : SortWordStack}
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
    (req : _Val7 = true)
    : Rewrites {
      kevm := {
        k := { val := SortK.kseq ((@inj SortInternalOp SortKItem) (SortInternalOp.«#next[_]_EVM_InternalOp_MaybeOpCode» ((@inj SortUnStackOp SortMaybeOpCode) SortUnStackOp.SLOAD_EVM_UnStackOp))) _K_CELL },
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
              wordStack := { val := SortWordStack.«_:__EVM-TYPES_WordStack_Int_WordStack» W0 _WS },
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
      generatedCounter := _DotVar0 } {
      kevm := {
        k := { val := _K_CELL },
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
              wordStack := { val := SortWordStack.«_:__EVM-TYPES_WordStack_Int_WordStack» _Val10 _WS },
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
  | SLT_SUMMARY_SLT_SUMMARY_USEGAS
    {GAS_CELL PC_CELL W0 W1 _Val0 _Val3 _Val4 _Val5 _Val6 : SortInt}
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
    {_K_CELL : SortK}
    (defn_Val0 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gverylow_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val0)
    (defn_Val1 : «_<=Int_» _Val0 GAS_CELL = some _Val1)
    (defn_Val2 : _andBool_ USEGAS_CELL _Val1 = some _Val2)
    (defn_Val3 : «_s<Word__EVM-TYPES_Int_Int_Int» W0 W1 = some _Val3)
    (defn_Val4 : «_+Int_» PC_CELL 1 = some _Val4)
    (defn_Val5 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gverylow_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val5)
    (defn_Val6 : «_-Int_» GAS_CELL _Val5 = some _Val6)
    (req : _Val2 = true)
    : Rewrites {
      kevm := {
        k := { val := SortK.kseq ((@inj SortInternalOp SortKItem) (SortInternalOp.«#next[_]_EVM_InternalOp_MaybeOpCode» ((@inj SortBinStackOp SortMaybeOpCode) SortBinStackOp.SLT_EVM_BinStackOp))) _K_CELL },
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
        k := { val := _K_CELL },
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
              wordStack := { val := SortWordStack.«_:__EVM-TYPES_WordStack_Int_WordStack» _Val3 WS },
              localMem := _Gen6,
              pc := { val := _Val4 },
              gas := { val := (@inj SortInt SortGas) _Val6 },
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
  | SMOD_SUMMARY_SMOD_SUMMARY_USEGAS
    {GAS_CELL PC_CELL W0 W1 _Val0 _Val3 _Val4 _Val5 _Val6 : SortInt}
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
    {_K_CELL : SortK}
    (defn_Val0 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Glow_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val0)
    (defn_Val1 : «_<=Int_» _Val0 GAS_CELL = some _Val1)
    (defn_Val2 : _andBool_ USEGAS_CELL _Val1 = some _Val2)
    (defn_Val3 : «_%sWord__EVM-TYPES_Int_Int_Int» W0 W1 = some _Val3)
    (defn_Val4 : «_+Int_» PC_CELL 1 = some _Val4)
    (defn_Val5 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Glow_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val5)
    (defn_Val6 : «_-Int_» GAS_CELL _Val5 = some _Val6)
    (req : _Val2 = true)
    : Rewrites {
      kevm := {
        k := { val := SortK.kseq ((@inj SortInternalOp SortKItem) (SortInternalOp.«#next[_]_EVM_InternalOp_MaybeOpCode» ((@inj SortBinStackOp SortMaybeOpCode) SortBinStackOp.SMOD_EVM_BinStackOp))) _K_CELL },
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
        k := { val := _K_CELL },
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
              wordStack := { val := SortWordStack.«_:__EVM-TYPES_WordStack_Int_WordStack» _Val3 WS },
              localMem := _Gen6,
              pc := { val := _Val4 },
              gas := { val := (@inj SortInt SortGas) _Val6 },
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
  | SSTORE_SUMMARY_SSTORE_SUMMARY_USEGAS_BERLIN
    {ACCESSEDSTORAGE_CELL ORIG_STORAGE_CELL STORAGE_CELL _Val39 _Val40 : SortMap}
    {GAS_CELL ID_CELL PC_CELL REFUND_CELL W0 W1 _Val1 _Val10 _Val11 _Val13 _Val2 _Val21 _Val22 _Val23 _Val24 _Val25 _Val27 _Val28 _Val29 _Val3 _Val30 _Val31 _Val32 _Val33 _Val6 _Val7 _Val8 _Val9 : SortInt}
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
    {_K_CELL : SortK}
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
    : Rewrites {
      kevm := {
        k := { val := SortK.kseq ((@inj SortInternalOp SortKItem) (SortInternalOp.«#next[_]_EVM_InternalOp_MaybeOpCode» ((@inj SortBinStackOp SortMaybeOpCode) SortBinStackOp.SSTORE_EVM_BinStackOp))) _K_CELL },
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
      generatedCounter := _DotVar0 } {
      kevm := {
        k := { val := _K_CELL },
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
  | SUB_SUMMARY_SUB_SUMMARY_USEGAS
    {GAS_CELL PC_CELL W0 W1 _Val0 _Val3 _Val4 _Val5 _Val6 _Val7 : SortInt}
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
    {_K_CELL : SortK}
    (defn_Val0 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gverylow_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val0)
    (defn_Val1 : «_<=Int_» _Val0 GAS_CELL = some _Val1)
    (defn_Val2 : _andBool_ USEGAS_CELL _Val1 = some _Val2)
    (defn_Val3 : «_-Int_» W0 W1 = some _Val3)
    (defn_Val4 : chop _Val3 = some _Val4)
    (defn_Val5 : «_+Int_» PC_CELL 1 = some _Val5)
    (defn_Val6 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gverylow_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val6)
    (defn_Val7 : «_-Int_» GAS_CELL _Val6 = some _Val7)
    (req : _Val2 = true)
    : Rewrites {
      kevm := {
        k := { val := SortK.kseq ((@inj SortInternalOp SortKItem) (SortInternalOp.«#next[_]_EVM_InternalOp_MaybeOpCode» ((@inj SortBinStackOp SortMaybeOpCode) SortBinStackOp.SUB_EVM_BinStackOp))) _K_CELL },
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
        k := { val := _K_CELL },
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
  | XOR_SUMMARY_XOR_SUMMARY_USEGAS
    {GAS_CELL PC_CELL W0 W1 _Val0 _Val3 _Val4 _Val5 _Val6 : SortInt}
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
    {_K_CELL : SortK}
    (defn_Val0 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gverylow_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val0)
    (defn_Val1 : «_<=Int_» _Val0 GAS_CELL = some _Val1)
    (defn_Val2 : _andBool_ USEGAS_CELL _Val1 = some _Val2)
    (defn_Val3 : _xorInt_ W0 W1 = some _Val3)
    (defn_Val4 : «_+Int_» PC_CELL 1 = some _Val4)
    (defn_Val5 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gverylow_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val5)
    (defn_Val6 : «_-Int_» GAS_CELL _Val5 = some _Val6)
    (req : _Val2 = true)
    : Rewrites {
      kevm := {
        k := { val := SortK.kseq ((@inj SortInternalOp SortKItem) (SortInternalOp.«#next[_]_EVM_InternalOp_MaybeOpCode» ((@inj SortBinStackOp SortMaybeOpCode) SortBinStackOp.XOR_EVM_BinStackOp))) _K_CELL },
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
        k := { val := _K_CELL },
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
              wordStack := { val := SortWordStack.«_:__EVM-TYPES_WordStack_Int_WordStack» _Val3 WS },
              localMem := _Gen6,
              pc := { val := _Val4 },
              gas := { val := (@inj SortInt SortGas) _Val6 },
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
