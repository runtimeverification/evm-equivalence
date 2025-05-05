import EvmEquivalence.Summaries.MstoreSummary
import EvmEquivalence.Interfaces.EvmYulInterface
import EvmEquivalence.Interfaces.GasInterface
import EvmEquivalence.Interfaces.FuncInterface
import EvmEquivalence.StateMap

open EvmYul
open StateMap
open KEVMInterface
open MstoreSummary

namespace MstoreOpcodeEquivalence

def mstoreLHS
  {GAS_CELL MEMORYUSED_CELL PC_CELL W0 W1 : SortInt}
  {LOCALMEM_CELL _Val14 _Val15 _Val16 : SortBytes}
  {SCHEDULE_CELL : SortSchedule}
  {USEGAS_CELL : SortBool}
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
  {_K_CELL : SortK} : SortGeneratedTopCell :=
  { kevm := {
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
    generatedCounter := _DotVar0 }

def mstoreRHS
  {_Val17 _Val24 _Val25 : SortInt}
  {_Val16 : SortBytes}
  {SCHEDULE_CELL : SortSchedule}
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
  {_K_CELL : SortK} : SortGeneratedTopCell :=
  { kevm := {
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

theorem rw_mstoreLHS_mstoreRHS
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
  (req : _Val13 = true) :
  Rewrites
  (@mstoreLHS GAS_CELL MEMORYUSED_CELL PC_CELL W0 W1 LOCALMEM_CELL _Val14 _Val15 _Val16 SCHEDULE_CELL USEGAS_CELL WS _DotVar0 _DotVar2 _Gen0 _Gen1 _Gen10 _Gen11 _Gen12 _Gen13 _Gen14 _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2 _Gen20 _Gen21 _Gen3 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 _Gen9 _K_CELL)
  (@mstoreRHS _Val17 _Val24 _Val25 _Val16 SCHEDULE_CELL WS _DotVar0 _DotVar2 _Gen0 _Gen1 _Gen10 _Gen11 _Gen12 _Gen13 _Gen14 _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2 _Gen20 _Gen21 _Gen3 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 _Gen9 _K_CELL)
  := by apply (@Rewrites.MSTORE_SUMMARY_MSTORE_SUMMARY_USEGAS GAS_CELL MEMORYUSED_CELL PC_CELL W0 W1 _Val0 _Val1 _Val10 _Val17 _Val18 _Val19 _Val2 _Val20 _Val21 _Val22 _Val23 _Val24 _Val25 _Val3 _Val5 _Val6 _Val7 _Val8 _Val9 LOCALMEM_CELL _Val14 _Val15 _Val16 SCHEDULE_CELL USEGAS_CELL _Val11 _Val12 _Val13 _Val4 WS _DotVar0 _DotVar2 _Gen0 _Gen1 _Gen10 _Gen11 _Gen12 _Gen13 _Gen14 _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2 _Gen20 _Gen21 _Gen3 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 _Gen9 _K_CELL)
  <;> assumption

end MstoreOpcodeEquivalence
