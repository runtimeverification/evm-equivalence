import EvmEquivalence.KEVM2Lean.Func

inductive Rewrites : SortGeneratedTopCell → SortGeneratedTopCell → Prop where
  | tran {s1 s2 s3 : SortGeneratedTopCell} (t1 : Rewrites s1 s2) (t2 : Rewrites s2 s3) : Rewrites s1 s3
  | EVM_OPTIMIZATIONS_optimized_add {GAVAIL _Val10 _Val11 : SortGas} {PCOUNT W0 W1 _Val0 _Val3 _Val6 _Val7 _Val8 _Val9 : SortInt} {SCHED : SortSchedule} {USEGAS _Val1 _Val2 _Val4 _Val5 : SortBool} {WS : SortWordStack} {_DotVar0 : SortGeneratedCounterCell} {_DotVar2 : SortK} {_DotVar3 : SortNetworkCell} {_Gen0 : SortProgramCell} {_Gen1 : SortJumpDestsCell} {_Gen10 : SortCallDepthCell} {_Gen11 : SortOutputCell} {_Gen12 : SortStatusCodeCell} {_Gen13 : SortCallStackCell} {_Gen14 : SortInterimStatesCell} {_Gen15 : SortTouchedAccountsCell} {_Gen16 : SortSubstateCell} {_Gen17 : SortGasPriceCell} {_Gen18 : SortOriginCell} {_Gen19 : SortBlockhashesCell} {_Gen2 : SortIdCell} {_Gen20 : SortBlockCell} {_Gen21 : SortExitCodeCell} {_Gen22 : SortModeCell} {_Gen3 : SortCallerCell} {_Gen4 : SortCallDataCell} {_Gen5 : SortCallValueCell} {_Gen6 : SortLocalMemCell} {_Gen7 : SortMemoryUsedCell} {_Gen8 : SortCallGasCell} {_Gen9 : SortStaticCell} (defn_Val0 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gverylow_SCHEDULE_ScheduleConst SCHED = some _Val0) (defn_Val1 : «_<=Gas__GAS-SYNTAX_Bool_Gas_Gas» ((@inj SortInt SortGas) _Val0) GAVAIL = some _Val1) (defn_Val2 : kite USEGAS _Val1 true = some _Val2) (defn_Val3 : «#sizeWordStack» WS = some _Val3) (defn_Val4 : «_<=Int_» _Val3 1023 = some _Val4) (defn_Val5 : _andBool_ _Val2 _Val4 = some _Val5) (defn_Val6 : «_+Int_» W0 W1 = some _Val6) (defn_Val7 : chop _Val6 = some _Val7) (defn_Val8 : «_+Int_» PCOUNT 1 = some _Val8) (defn_Val9 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gverylow_SCHEDULE_ScheduleConst SCHED = some _Val9) (defn_Val10 : «_-Gas__GAS-SYNTAX_Gas_Gas_Gas» GAVAIL ((@inj SortInt SortGas) _Val9) = some _Val10) (defn_Val11 : kite USEGAS _Val10 GAVAIL = some _Val11) (req : _Val5 = true) : Rewrites { kevm := { k := { val := SortK.kseq ((@inj SortInternalOp SortKItem) (SortInternalOp.«#next[_]_EVM_InternalOp_MaybeOpCode» ((@inj SortBinStackOp SortMaybeOpCode) SortBinStackOp.ADD_EVM_BinStackOp))) _DotVar2 }, exitCode := _Gen21, mode := _Gen22, schedule := { val := SCHED }, useGas := { val := USEGAS }, ethereum := { evm := { output := _Gen11, statusCode := _Gen12, callStack := _Gen13, interimStates := _Gen14, touchedAccounts := _Gen15, callState := { program := _Gen0, jumpDests := _Gen1, id := _Gen2, caller := _Gen3, callData := _Gen4, callValue := _Gen5, wordStack := { val := SortWordStack.«_:__EVM-TYPES_WordStack_Int_WordStack» W0 (SortWordStack.«_:__EVM-TYPES_WordStack_Int_WordStack» W1 WS) }, localMem := _Gen6, pc := { val := PCOUNT }, gas := { val := GAVAIL }, memoryUsed := _Gen7, callGas := _Gen8, static := _Gen9, callDepth := _Gen10 }, substate := _Gen16, gasPrice := _Gen17, origin := _Gen18, blockhashes := _Gen19, block := _Gen20 }, network := _DotVar3 } }, generatedCounter := _DotVar0 } { kevm := { k := { val := _DotVar2 }, exitCode := _Gen21, mode := _Gen22, schedule := { val := SCHED }, useGas := { val := USEGAS }, ethereum := { evm := { output := _Gen11, statusCode := _Gen12, callStack := _Gen13, interimStates := _Gen14, touchedAccounts := _Gen15, callState := { program := _Gen0, jumpDests := _Gen1, id := _Gen2, caller := _Gen3, callData := _Gen4, callValue := _Gen5, wordStack := { val := SortWordStack.«_:__EVM-TYPES_WordStack_Int_WordStack» _Val7 WS }, localMem := _Gen6, pc := { val := _Val8 }, gas := { val := _Val11 }, memoryUsed := _Gen7, callGas := _Gen8, static := _Gen9, callDepth := _Gen10 }, substate := _Gen16, gasPrice := _Gen17, origin := _Gen18, blockhashes := _Gen19, block := _Gen20 }, network := _DotVar3 } }, generatedCounter := _DotVar0 }
