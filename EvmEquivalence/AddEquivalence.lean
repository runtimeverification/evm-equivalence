import EvmEquivalence.Summaries
import EvmEquivalence.StateMap
import EvmEquivalence.Interfaces.FuncInterface
import EvmEquivalence.Interfaces.GasInterface
import EvmEquivalence.Interfaces.EvmYulInterface

open EvmYul
open StateMap
open KEVMInterface

namespace AddOpcodeEquivalence

def addLHS
  {GAVAIL : SortGas}
  {PCOUNT W0 W1 : SortInt}
  {SCHED : SortSchedule}
  {USEGAS : SortBool}
  {WS : SortWordStack}
  {_DotVar0 : SortGeneratedCounterCell}
  {_DotVar2 : SortK}
  {_DotVar3 : SortNetworkCell}
  {_Gen0 : SortProgramCell}
  {_Gen1 : SortJumpDestsCell}
  {_Gen10 : SortCallDepthCell}
  {_Gen11 : SortOutputCell}
  {_Gen12 : SortStatusCodeCell}
  {_Gen13 : SortCallStackCell}
  {_Gen14 : SortInterimStatesCell}
  {_Gen15 : SortTouchedAccountsCell}
  {_Gen16 : SortSubstateCell}
  {_Gen17 : SortGasPriceCell}
  {_Gen18 : SortOriginCell}
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
  : SortGeneratedTopCell :=
  { kevm := {
        k := { val := SortK.kseq ((@inj SortInternalOp SortKItem) (SortInternalOp.«#next[_]_EVM_InternalOp_MaybeOpCode» ((@inj SortBinStackOp SortMaybeOpCode) (SortBinStackOp.ADD_EVM_BinStackOp)))) _DotVar2 },
        exitCode := _Gen21,
        mode := _Gen22,
        schedule := { val := SCHED },
        useGas := { val := USEGAS },
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
              pc := { val := PCOUNT },
              gas := { val := GAVAIL },
              memoryUsed := _Gen7,
              callGas := _Gen8,
              static := _Gen9,
              callDepth := _Gen10 },
            substate := _Gen16,
            gasPrice := _Gen17,
            origin := _Gen18,
            blockhashes := _Gen19,
            block := _Gen20 },
          network := _DotVar3 } },
      generatedCounter := _DotVar0 }

def addRHS
  {_Val10 _Val11 : SortGas}
  {_Val0 _Val3 _Val6 _Val7 _Val8 _Val9 : SortInt}
  {SCHED : SortSchedule}
  {USEGAS _Val1 _Val2 _Val4 _Val5 : SortBool}
  {WS : SortWordStack}
  {_DotVar0 : SortGeneratedCounterCell}
  {_DotVar2 : SortK}
  {_DotVar3 : SortNetworkCell}
  {_Gen0 : SortProgramCell}
  {_Gen1 : SortJumpDestsCell}
  {_Gen10 : SortCallDepthCell}
  {_Gen11 : SortOutputCell}
  {_Gen12 : SortStatusCodeCell}
  {_Gen13 : SortCallStackCell}
  {_Gen14 : SortInterimStatesCell}
  {_Gen15 : SortTouchedAccountsCell}
  {_Gen16 : SortSubstateCell}
  {_Gen17 : SortGasPriceCell}
  {_Gen18 : SortOriginCell}
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
  : SortGeneratedTopCell :=
  { kevm := {
      k := { val := _DotVar2 },
      exitCode := _Gen21,
      mode := _Gen22,
      schedule := { val := SCHED },
      useGas := { val := USEGAS },
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
            wordStack := { val := SortWordStack.«_:__EVM-TYPES_WordStack_Int_WordStack» _Val7 WS },
            localMem := _Gen6,
            pc := { val := _Val8 },
            gas := { val := _Val11 },
            memoryUsed := _Gen7,
            callGas := _Gen8,
            static := _Gen9,
            callDepth := _Gen10 },
          substate := _Gen16,
          gasPrice := _Gen17,
          origin := _Gen18,
          blockhashes := _Gen19,
          block := _Gen20 },
        network := _DotVar3 } },
    generatedCounter := _DotVar0 }

theorem rw_addLHS_addRHS
  {GAVAIL _Val10 _Val11 : SortGas}
  {PCOUNT W0 W1 _Val0 _Val3 _Val6 _Val7 _Val8 _Val9 : SortInt}
  {SCHED : SortSchedule}
  {USEGAS _Val1 _Val2 _Val4 _Val5 : SortBool}
  {WS : SortWordStack}
  {_DotVar0 : SortGeneratedCounterCell}
  {_DotVar2 : SortK}
  {_DotVar3 : SortNetworkCell}
  {_Gen0 : SortProgramCell}
  {_Gen1 : SortJumpDestsCell}
  {_Gen10 : SortCallDepthCell}
  {_Gen11 : SortOutputCell}
  {_Gen12 : SortStatusCodeCell}
  {_Gen13 : SortCallStackCell}
  {_Gen14 : SortInterimStatesCell}
  {_Gen15 : SortTouchedAccountsCell}
  {_Gen16 : SortSubstateCell}
  {_Gen17 : SortGasPriceCell}
  {_Gen18 : SortOriginCell}
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
  (defn_Val0 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» (SortScheduleConst.Gverylow_SCHEDULE_ScheduleConst) SCHED = some _Val0)
  (defn_Val1 : «_<=Gas__GAS-SYNTAX_Bool_Gas_Gas» ((@inj SortInt SortGas) _Val0) GAVAIL = some _Val1)
  (defn_Val2 : kite USEGAS _Val1 true = some _Val2)
  (defn_Val3 : «#sizeWordStack» WS = some _Val3)
  (defn_Val4 : «_<=Int_» _Val3 1023 = some _Val4)
  (defn_Val5 : _andBool_ _Val2 _Val4 = some _Val5)
  (defn_Val6 : «_+Int_» W0 W1 = some _Val6)
  (defn_Val7 : chop _Val6 = some _Val7)
  (defn_Val8 : «_+Int_» PCOUNT 1 = some _Val8)
  (defn_Val9 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» (SortScheduleConst.Gverylow_SCHEDULE_ScheduleConst) SCHED = some _Val9)
  (defn_Val10 : «_-Gas__GAS-SYNTAX_Gas_Gas_Gas» GAVAIL ((@inj SortInt SortGas) _Val9) = some _Val10)
  (defn_Val11 : kite USEGAS _Val10 GAVAIL = some _Val11)
  (req : _Val5 = true) :
  Rewrites
    (@addLHS GAVAIL PCOUNT W0 W1 SCHED USEGAS WS _DotVar0 _DotVar2 _DotVar3 _Gen0 _Gen1 _Gen10 _Gen11 _Gen12 _Gen13 _Gen14 _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2 _Gen20 _Gen21 _Gen22 _Gen3 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 _Gen9)
    (@addRHS _Val10 _Val11 _Val0 _Val3 _Val6 _Val7 _Val8 _Val9 SCHED USEGAS _Val1 _Val2 _Val4 _Val5 WS _DotVar0 _DotVar2 _DotVar3 _Gen0 _Gen1 _Gen10 _Gen11 _Gen12 _Gen13 _Gen14 _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2 _Gen20 _Gen21 _Gen22 _Gen3 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 _Gen9) := by
  apply Rewrites.EVM_OPTIMIZATIONS_optimized_add <;> try assumption
  cc

theorem add_prestate_equiv
  {GAVAIL : SortGas}
  {PCOUNT W0 W1 : SortInt}
  {SCHED : SortSchedule}
  {USEGAS : SortBool}
  {WS : SortWordStack}
  {_DotVar0 : SortGeneratedCounterCell}
  {_DotVar2 : SortK}
  {_DotVar3 : SortNetworkCell}
  {_Gen0 : SortProgramCell}
  {_Gen1 : SortJumpDestsCell}
  {_Gen10 : SortCallDepthCell}
  {_Gen11 : SortOutputCell}
  {_Gen12 : SortStatusCodeCell}
  {_Gen13 : SortCallStackCell}
  {_Gen14 : SortInterimStatesCell}
  {_Gen15 : SortTouchedAccountsCell}
  {_Gen16 : SortSubstateCell}
  {_Gen17 : SortGasPriceCell}
  {_Gen18 : SortOriginCell}
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
  (symState : EVM.State):
  stateMap symState (@addLHS GAVAIL PCOUNT W0 W1 SCHED USEGAS WS _DotVar0 _DotVar2 _DotVar3 _Gen0 _Gen1 _Gen10 _Gen11 _Gen12 _Gen13 _Gen14 _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2 _Gen20 _Gen21 _Gen22 _Gen3 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 _Gen9) =
  {symState with
    stack := (intMap W0) :: (intMap W1) :: wordStackMap WS
    pc := intMap PCOUNT
    gasAvailable := intMap GAVAIL.1
    executionEnv := {symState.executionEnv with code := _Gen0.val}
    returnData := _Gen11.val
    } := by rfl

theorem add_poststate_equiv
  {GAVAIL _Val10 _Val11 : SortGas}
  {PCOUNT W0 W1 _Val0 _Val3 _Val6 _Val7 _Val8 _Val9 : SortInt}
  {SCHED : SortSchedule}
  {USEGAS _Val1 _Val2 _Val4 _Val5 : SortBool}
  {WS : SortWordStack}
  {_DotVar0 : SortGeneratedCounterCell}
  {_DotVar2 : SortK}
  {_DotVar3 : SortNetworkCell}
  {_Gen0 : SortProgramCell}
  {_Gen1 : SortJumpDestsCell}
  {_Gen10 : SortCallDepthCell}
  {_Gen11 : SortOutputCell}
  {_Gen12 : SortStatusCodeCell}
  {_Gen13 : SortCallStackCell}
  {_Gen14 : SortInterimStatesCell}
  {_Gen15 : SortTouchedAccountsCell}
  {_Gen16 : SortSubstateCell}
  {_Gen17 : SortGasPriceCell}
  {_Gen18 : SortOriginCell}
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
  /- (defn_Val0 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» (SortScheduleConst.Gverylow_SCHEDULE_ScheduleConst) SCHED = some _Val0)
  (defn_Val1 : «_<=Gas__GAS-SYNTAX_Bool_Gas_Gas» ((@inj SortInt SortGas) _Val0) GAVAIL = some _Val1)
  (defn_Val2 : kite USEGAS _Val1 true = some _Val2)
  (defn_Val3 : «#sizeWordStack» WS = some _Val3)
  (defn_Val4 : «_<=Int_» _Val3 1023 = some _Val4)
  (defn_Val5 : _andBool_ _Val2 _Val4 = some _Val5) -/
  (defn_Val6 : «_+Int_» W0 W1 = some _Val6)
  (defn_Val7 : chop _Val6 = some _Val7)
  (defn_Val8 : «_+Int_» PCOUNT 1 = some _Val8)
  /- (defn_Val9 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» (SortScheduleConst.Gverylow_SCHEDULE_ScheduleConst) SCHED = some _Val9)
  (defn_Val10 : «_-Gas__GAS-SYNTAX_Gas_Gas_Gas» GAVAIL ((@inj SortInt SortGas) _Val9) = some _Val10) -/
  (defn_Val11 : kite USEGAS _Val10 GAVAIL = some _Val11)
  /- (req : _Val5 = true) -/
  (symState : EVM.State)
  (gasOn: USEGAS = true):
  stateMap symState (@addRHS _Val10 _Val11 _Val0 _Val3 _Val6 _Val7 _Val8 _Val9 SCHED USEGAS _Val1 _Val2 _Val4 _Val5 WS _DotVar0 _DotVar2 _DotVar3 _Gen0 _Gen1 _Gen10 _Gen11 _Gen12 _Gen13 _Gen14 _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2 _Gen20 _Gen21 _Gen22 _Gen3 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 _Gen9) =
  {symState with
    stack := (intMap (chop' («_+Int'_» W0 W1))) :: wordStackMap WS
    pc := intMap («_+Int'_» PCOUNT 1)
    gasAvailable := intMap _Val10.1
    executionEnv := {symState.executionEnv with code := _Gen0.val}
    returnData := _Gen11.val
    } := by
  simp [stateMap, addRHS, programOfGTC]
  constructor <;> try constructor
  all_goals congr
  · simp [iteMap, gasOn] at defn_Val11; rw [defn_Val11]
  · simp [«_+Int'_», defn_Val8]
  · simp [«_+Int'_», chop', defn_Val6, defn_Val7]

open AddSummary

-- We cannot prove full equivalence for the `EVM.step` function
-- This is because it doesn't include all semantics such as gas computation
theorem step_add_equiv
  {GAVAIL _Val10 _Val11 : SortGas}
  {PCOUNT W0 W1 _Val0 _Val3 _Val6 _Val7 _Val8 _Val9 : SortInt}
  {SCHED : SortSchedule}
  {USEGAS _Val1 _Val2 _Val4 _Val5 : SortBool}
  {WS : SortWordStack}
  {_DotVar0 : SortGeneratedCounterCell}
  {_DotVar2 : SortK}
  {_DotVar3 : SortNetworkCell}
  {_Gen0 : SortProgramCell}
  {_Gen1 : SortJumpDestsCell}
  {_Gen10 : SortCallDepthCell}
  {_Gen11 : SortOutputCell}
  {_Gen12 : SortStatusCodeCell}
  {_Gen13 : SortCallStackCell}
  {_Gen14 : SortInterimStatesCell}
  {_Gen15 : SortTouchedAccountsCell}
  {_Gen16 : SortSubstateCell}
  {_Gen17 : SortGasPriceCell}
  {_Gen18 : SortOriginCell}
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
  (defn_Val0 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» (SortScheduleConst.Gverylow_SCHEDULE_ScheduleConst) SCHED = some _Val0)
  (defn_Val1 : «_<=Gas__GAS-SYNTAX_Bool_Gas_Gas» ((@inj SortInt SortGas) _Val0) GAVAIL = some _Val1)
  /- (defn_Val2 : kite USEGAS _Val1 true = some _Val2)
  (defn_Val3 : «#sizeWordStack» WS = some _Val3)
  (defn_Val4 : «_<=Int_» _Val3 1023 = some _Val4)
  (defn_Val5 : _andBool_ _Val2 _Val4 = some _Val5) -/
  (defn_Val6 : «_+Int_» W0 W1 = some _Val6)
  (defn_Val7 : chop _Val6 = some _Val7)
  (defn_Val8 : «_+Int_» PCOUNT 1 = some _Val8)
  (defn_Val9 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» (SortScheduleConst.Gverylow_SCHEDULE_ScheduleConst) SCHED = some _Val9)
  (defn_Val10 : «_-Gas__GAS-SYNTAX_Gas_Gas_Gas» GAVAIL ((@inj SortInt SortGas) _Val9) = some _Val10)
  (defn_Val11 : kite USEGAS _Val10 GAVAIL = some _Val11)
  /- (req : _Val5 = true) -/
  (symState : EVM.State)
  -- needed for EVM.step
  (gas gasCost : ℕ)
  -- Necessary assumptions for equivalence
  (gasOn: USEGAS = true)
  (cancun : SCHED = .CANCUN_EVM)
  (gasEnough : 0 < gas)
  (gavailEnough : 3 ≤ GAVAIL.1)
  (gavailSmall : GAVAIL.1 < ↑UInt256.size)
  (gasCostValue : gasCost = GasConstants.Gverylow)
  (pcountSmall : PCOUNT + 1 < UInt256.size)
  (pcountNonneg : 0 ≤ PCOUNT)
  (W0ge0 : 0 ≤ W0)
  (W1ge0 : 0 ≤ W1):
  EVM.step_add gas gasCost (stateMap symState (@addLHS GAVAIL PCOUNT W0 W1 SCHED USEGAS WS _DotVar0 _DotVar2 _DotVar3 _Gen0 _Gen1 _Gen10 _Gen11 _Gen12 _Gen13 _Gen14 _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2 _Gen20 _Gen21 _Gen22 _Gen3 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 _Gen9)) =
  .ok (stateMap {symState with execLength := symState.execLength + 1} (@addRHS _Val10 _Val11 _Val0 _Val3 _Val6 _Val7 _Val8 _Val9 SCHED USEGAS _Val1 _Val2 _Val4 _Val5 WS _DotVar0 _DotVar2 _DotVar3 _Gen0 _Gen1 _Gen10 _Gen11 _Gen12 _Gen13 _Gen14 _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2 _Gen20 _Gen21 _Gen22 _Gen3 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 _Gen9)) := by
  rw [add_prestate_equiv, add_poststate_equiv] <;> try assumption
  cases gas; contradiction
  case succ gas =>
    rw [EVM.step_add_summary] <;> try assumption
    congr
    . subst cancun
      simp_all [GasInterface.cancun_def]; subst defn_Val9
      simp_all [subGas_def]; subst defn_Val10
      simp [subInt_def]; try assumption
      simp [SortGas.val, inj, Inj.inj]
      rw [intMap_sub_dist] <;> first | assumption | try simp
      rfl
    . have mod_rw : (PCOUNT + 1) % UInt256.size = PCOUNT + 1 := by
        rw [Int.mod_cast, Int.toNat_ofNat, Nat.mod_eq_of_lt] <;> try linarith
        . rw [Int.ofNat_toNat, sup_eq_left]; linarith
        . rw [Int.toNat_lt] <;> linarith
      rw [plusInt_def, ←mod_rw, intMap_add_dist] <;> first | assumption | try simp
      congr
    . simp [intMap, chop_def, plusInt_def]; rw [←intMap, ←intMap, ←intMap, intMap_add_dist] <;> assumption

/- Deviations from the KEVM produced specifications:
 1. The program is not symbolic, it is instead a 1-opcode (`ADD`) program
 2. The program counter is also not symbolic, and it is set to 0
 3. In the RHS, the output cell (mapped to `returnData`) is set to `ByteArray.empty`
 4. The schedule is set to `CANCUN`
 5. `GAVAIL` is in the `UInt256` range
 6. `W0` and `W1` are nonnegative
 -/
theorem X_add_equiv
  {GAVAIL _Val10 _Val11 : SortGas}
  {PCOUNT W0 W1 _Val0 _Val3 _Val6 _Val7 _Val8 _Val9 : SortInt}
  {SCHED : SortSchedule}
  {USEGAS _Val1 _Val2 _Val4 _Val5 : SortBool}
  {WS : SortWordStack}
  {_DotVar0 : SortGeneratedCounterCell}
  {_DotVar2 : SortK}
  {_DotVar3 : SortNetworkCell}
  {_Gen0 : SortProgramCell}
  {_Gen1 : SortJumpDestsCell}
  {_Gen10 : SortCallDepthCell}
  {_Gen11 : SortOutputCell}
  {_Gen12 : SortStatusCodeCell}
  {_Gen13 : SortCallStackCell}
  {_Gen14 : SortInterimStatesCell}
  {_Gen15 : SortTouchedAccountsCell}
  {_Gen16 : SortSubstateCell}
  {_Gen17 : SortGasPriceCell}
  {_Gen18 : SortOriginCell}
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
  (defn_Val0 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» (SortScheduleConst.Gverylow_SCHEDULE_ScheduleConst) SCHED = some _Val0)
  (defn_Val1 : «_<=Gas__GAS-SYNTAX_Bool_Gas_Gas» ((@inj SortInt SortGas) _Val0) GAVAIL = some _Val1)
  (defn_Val2 : kite USEGAS _Val1 true = some _Val2)
  (defn_Val3 : «#sizeWordStack» WS = some _Val3)
  (defn_Val4 : «_<=Int_» _Val3 1023 = some _Val4)
  (defn_Val5 : _andBool_ _Val2 _Val4 = some _Val5)
  (defn_Val6 : «_+Int_» W0 W1 = some _Val6)
  (defn_Val7 : chop _Val6 = some _Val7)
  (defn_Val8 : «_+Int_» PCOUNT 1 = some _Val8)
  (defn_Val9 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» (SortScheduleConst.Gverylow_SCHEDULE_ScheduleConst) SCHED = some _Val9)
  (defn_Val10 : «_-Gas__GAS-SYNTAX_Gas_Gas_Gas» GAVAIL ((@inj SortInt SortGas) _Val9) = some _Val10)
  (defn_Val11 : kite USEGAS _Val10 GAVAIL = some _Val11)
  (req : _Val5 = true)
  (symExecLength : ℕ)
  (symState : EVM.State)
  -- Necessary assumptions for equivalence
  (gasOn: USEGAS = true)
  (cancun : SCHED = .CANCUN_EVM)
  (codeAdd : _Gen0 = ⟨⟨#[(1 : UInt8)]⟩⟩)
  (pcZero : PCOUNT = 0)
  (enoughGas : _Val1 = true)
  (boundedGas : GAVAIL.1 < ↑UInt256.size)
  (W0ge0 : 0 ≤ W0)
  (W1ge0 : 0 ≤ W1):
  EVM.X false (UInt256.toNat (intMap GAVAIL.1)) (stateMap symState (@addLHS GAVAIL PCOUNT W0 W1 SCHED USEGAS WS _DotVar0 _DotVar2 _DotVar3 _Gen0 _Gen1 _Gen10 _Gen11 _Gen12 _Gen13 _Gen14 _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2 _Gen20 _Gen21 _Gen22 _Gen3 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 _Gen9)) =
  .ok (.success (stateMap {symState with execLength := symState.execLength + 2} (@addRHS _Val10 _Val11 _Val0 _Val3 _Val6 _Val7 _Val8 _Val9 SCHED USEGAS _Val1 _Val2 _Val4 _Val5 WS _DotVar0 _DotVar2 _DotVar3 _Gen0 _Gen1 _Gen10 (⟨ByteArray.empty⟩) _Gen12 _Gen13 _Gen14 _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2 _Gen20 _Gen21 _Gen22 _Gen3 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 _Gen9)) ByteArray.empty) := by
  -- With `simp` doesn't work
  rw [codeAdd, pcZero, add_prestate_equiv, add_poststate_equiv] <;> try assumption
  -- If we don't apply this lemma we cannot rewrite X_add_summary
  have pc_equiv : intMap 0 = UInt256.ofNat 0 := by rfl
  rw [pc_equiv, X_add_summary]
  · congr
    · simp [subGas_def, subInt_def] at defn_Val10
      simp [cancun, GasInterface.cancun_def] at *
      simp [leGas_def, «_<=Int_», enoughGas, SortGas.val, ←defn_Val0, inj] at defn_Val1
      simp [←defn_Val9, ←defn_Val10, SortGas.val, inj, Inj.inj]
      rw [intMap_sub_dist] <;> first | simp | try assumption
      congr
    · simp [pcZero, plusInt_def]; rfl
    · simp [intMap, chop_def, plusInt_def]; rw [←intMap, ←intMap, ←intMap, intMap_add_dist] <;> assumption
  · sorry
  · cases WS <;> try simp
    simp [sizeWordStack_def] at defn_Val3; subst defn_Val3
    have true_cond: _Val4 = true := by
      subst req; rw [andBool_def] at defn_Val5
      subst cancun codeAdd pcZero enoughGas gasOn
      simp_all only [Option.some.injEq, Bool.and_eq_true]
    simp_all [true_cond, «_<=Int_», Int.add_one_le_iff, ←Nat.lt_sub_iff_add_lt]

end AddOpcodeEquivalence
