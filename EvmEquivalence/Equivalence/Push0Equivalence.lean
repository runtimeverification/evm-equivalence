import EvmEquivalence.Summaries.Push0Summary
import EvmEquivalence.StateMap
import EvmEquivalence.Interfaces.FuncInterface
import EvmEquivalence.Interfaces.GasInterface
import EvmEquivalence.Interfaces.EvmYulInterface

open EvmYul
open StateMap
open KEVMInterface

namespace Push0Equivalence

def push0LHS
  {GAS_CELL PC_CELL /- _Val0 _Val10 _Val3 _Val8 _Val9 -/ : SortInt}
  {K_CELL : SortK}
  {SCHEDULE_CELL : SortSchedule}
  {USEGAS_CELL /- _Val1 _Val2 _Val4 _Val5 _Val6 _Val7 -/ : SortBool}
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
  /- (defn_Val0 : sizeWordStackAux WS 0 = some _Val0)
  (defn_Val1 : «_<Int_» _Val0 0 = some _Val1)
  (defn_Val2 : notBool_ _Val1 = some _Val2)
  (defn_Val3 : sizeWordStackAux WS 0 = some _Val3)
  (defn_Val4 : «_<Int_» 1023 _Val3 = some _Val4)
  (defn_Val5 : notBool_ _Val4 = some _Val5)
  (defn_Val6 : _andBool_ _Val2 _Val5 = some _Val6)
  (defn_Val7 : _andBool_ USEGAS_CELL _Val6 = some _Val7)
  (defn_Val8 : «_+Int_» PC_CELL 1 = some _Val8)
  (defn_Val9 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gbase_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val9)
  (defn_Val10 : «_-Int_» GAS_CELL _Val9 = some _Val10)
  (req : _Val7 = true) -/ : SortGeneratedTopCell :=
  { kevm := {
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
    generatedCounter := _DotVar0 }

def push0RHS
  {/- GAS_CELL PC_CELL -/ _Val0 _Val10 _Val3 _Val8 _Val9 : SortInt}
  {K_CELL : SortK}
  {SCHEDULE_CELL : SortSchedule}
  {/- USEGAS_CELL -/ _Val1 _Val2 _Val4 _Val5 _Val6 _Val7 : SortBool}
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
  /- (defn_Val0 : sizeWordStackAux WS 0 = some _Val0)
  (defn_Val1 : «_<Int_» _Val0 0 = some _Val1)
  (defn_Val2 : notBool_ _Val1 = some _Val2)
  (defn_Val3 : sizeWordStackAux WS 0 = some _Val3)
  (defn_Val4 : «_<Int_» 1023 _Val3 = some _Val4)
  (defn_Val5 : notBool_ _Val4 = some _Val5)
  (defn_Val6 : _andBool_ _Val2 _Val5 = some _Val6)
  (defn_Val7 : _andBool_ USEGAS_CELL _Val6 = some _Val7)
  (defn_Val8 : «_+Int_» PC_CELL 1 = some _Val8)
  (defn_Val9 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gbase_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val9)
  (defn_Val10 : «_-Int_» GAS_CELL _Val9 = some _Val10)
  (req : _Val7 = true) -/ : SortGeneratedTopCell :=
  { kevm := {
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
          pc := { val := _Val8 },
          gas := { val := (@inj SortInt SortGas) _Val10 },
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

theorem rw_push0LHS_push0RHS
  {GAS_CELL PC_CELL _Val0 _Val10 _Val3 _Val8 _Val9 : SortInt}
  {K_CELL : SortK}
  {SCHEDULE_CELL : SortSchedule}
  {USEGAS_CELL _Val1 _Val2 _Val4 _Val5 _Val6 _Val7 : SortBool}
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
  (defn_Val0 : sizeWordStackAux WS 0 = some _Val0)
  (defn_Val1 : «_<Int_» _Val0 0 = some _Val1)
  (defn_Val2 : notBool_ _Val1 = some _Val2)
  (defn_Val3 : sizeWordStackAux WS 0 = some _Val3)
  (defn_Val4 : «_<Int_» 1023 _Val3 = some _Val4)
  (defn_Val5 : notBool_ _Val4 = some _Val5)
  (defn_Val6 : _andBool_ _Val2 _Val5 = some _Val6)
  (defn_Val7 : _andBool_ USEGAS_CELL _Val6 = some _Val7)
  (defn_Val8 : «_+Int_» PC_CELL 1 = some _Val8)
  (defn_Val9 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gbase_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val9)
  (defn_Val10 : «_-Int_» GAS_CELL _Val9 = some _Val10)
  (req : _Val7 = true):
  Rewrites
  (@push0LHS GAS_CELL PC_CELL K_CELL SCHEDULE_CELL USEGAS_CELL WS _DotVar0 _DotVar2 _Gen0 _Gen1 _Gen10 _Gen11 _Gen12 _Gen13 _Gen14 _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2 _Gen20 _Gen21 _Gen22 _Gen23 _Gen3 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 _Gen9)
  (@push0RHS _Val0 _Val10 _Val3 _Val8 _Val9 K_CELL SCHEDULE_CELL _Val1 _Val2 _Val4 _Val5 _Val6 _Val7 WS _DotVar0 _DotVar2 _Gen0 _Gen1 _Gen10 _Gen11 _Gen12 _Gen13 _Gen14 _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2 _Gen20 _Gen21 _Gen22 _Gen23 _Gen3 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 _Gen9) :=
  by
  apply Rewrites.SUMMARY_PUSHZERO_0_SPEC_BASIC_BLOCK_11_TO_9



end Push0Equivalence
