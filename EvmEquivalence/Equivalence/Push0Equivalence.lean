import EvmEquivalence.Summaries.Push0Summary
import EvmEquivalence.StateMap
import EvmEquivalence.Interfaces.FuncInterface
import EvmEquivalence.Interfaces.GasInterface
import EvmEquivalence.Interfaces.EvmYulInterface

open EvmYul
open StateMap
open GasInterface
open KEVMInterface
open Push0Summary

namespace Push0Equivalence

def push0LHS
  {GAS_CELL PC_CELL : SortInt}
  {K_CELL : SortK}
  {SCHEDULE_CELL : SortSchedule}
  {USEGAS_CELL : SortBool}
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
  {_Gen9 : SortStaticCell}: SortGeneratedTopCell :=
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
  {_Val11 _Val13 : SortInt}
  {K_CELL : SortK}
  {SCHEDULE_CELL : SortSchedule}
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
  {_Gen9 : SortStaticCell}: SortGeneratedTopCell :=
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

theorem rw_push0LHS_push0RHS
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
  (req : _Val10 = true) :
  Rewrites
  (@push0LHS GAS_CELL PC_CELL K_CELL SCHEDULE_CELL USEGAS_CELL WS _DotVar0 _DotVar2 _Gen0 _Gen1 _Gen10 _Gen11 _Gen12 _Gen13 _Gen14 _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2 _Gen20 _Gen21 _Gen22 _Gen23 _Gen3 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 _Gen9)
  (@push0RHS _Val11 _Val13 K_CELL SCHEDULE_CELL WS _DotVar0 _DotVar2 _Gen0 _Gen1 _Gen10 _Gen11 _Gen12 _Gen13 _Gen14 _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2 _Gen20 _Gen21 _Gen22 _Gen23 _Gen3 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 _Gen9) :=
  by apply Rewrites.PUSHZERO_SUMMARY_PUSHZERO_SUMMARY_1 <;> try assumption
     all_goals simp_all [notBool_def, andBool_def]

theorem push0_prestate_equiv
  {GAS_CELL PC_CELL : SortInt}
  {K_CELL : SortK}
  {SCHEDULE_CELL : SortSchedule}
  {USEGAS_CELL : SortBool}
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
  {symState : EVM.State}:
  let lhs := (@push0LHS GAS_CELL PC_CELL K_CELL SCHEDULE_CELL USEGAS_CELL WS _DotVar0 _DotVar2 _Gen0 _Gen1 _Gen10 _Gen11 _Gen12 _Gen13 _Gen14 _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2 _Gen20 _Gen21 _Gen22 _Gen23 _Gen3 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 _Gen9)
  stateMap symState lhs =
  {symState with
    stack := wordStackMap WS
    pc := intMap PC_CELL
    gasAvailable := intMap GAS_CELL
    executionEnv := {symState.executionEnv with
                  code := _Gen0.val,
                  codeOwner := idMap lhs.Iₐ,
                  perm := !lhs.isStatic.val}
    accountMap := Axioms.SortAccountsCellMap lhs.accounts
    substate := {symState.substate with
            accessedStorageKeys :=  Axioms.SortAccessedStorageCellMap lhs.accessedStorage
            refundBalance := intMap _Gen17.refund.val
           }
    returnData := _Gen11.val
    } := rfl

theorem push0_poststate_equiv
  (PC_CELL : SortInt)
  {_Val11 _Val13 : SortInt}
  {K_CELL : SortK}
  {SCHEDULE_CELL : SortSchedule}
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
  {symState : EVM.State}
  (defn_Val11 : «_+Int_» PC_CELL 1 = some _Val11):
  let rhs := (@push0RHS _Val11 _Val13 K_CELL SCHEDULE_CELL WS _DotVar0 _DotVar2 _Gen0 _Gen1 _Gen10 _Gen11 _Gen12 _Gen13 _Gen14 _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2 _Gen20 _Gen21 _Gen22 _Gen23 _Gen3 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 _Gen9)
  stateMap symState rhs =
  {symState with
    stack := .ofNat 0 :: wordStackMap WS
    pc := intMap («_+Int'_» PC_CELL 1)
    gasAvailable := intMap _Val13
    executionEnv := {symState.executionEnv with
                  code := _Gen0.val,
                  codeOwner := idMap rhs.Iₐ,
                  perm := !rhs.isStatic.val}
    accountMap := Axioms.SortAccountsCellMap rhs.accounts
    substate := {symState.substate with
            accessedStorageKeys :=  Axioms.SortAccessedStorageCellMap rhs.accessedStorage
            refundBalance := intMap _Gen17.refund.val
           }
    returnData := _Gen11.val
    } := by aesop (add simp [«_+Int'_»])

theorem step_push0_equiv
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
  /- (defn_Val2 : _andBool_ USEGAS_CELL _Val1 = some _Val2) -/
  (defn_Val3 : sizeWordStackAux WS 0 = some _Val3)
  (defn_Val4 : «_<Int_» _Val3 0 = some _Val4)
  /- (defn_Val5 : notBool_ _Val4 = some _Val5) -/
  (defn_Val6 : sizeWordStackAux WS 0 = some _Val6)
  (defn_Val7 : «_<Int_» 1023 _Val6 = some _Val7)
  /- (defn_Val8 : notBool_ _Val7 = some _Val8)
  (defn_Val9 : _andBool_ _Val5 _Val8 = some _Val9) -/
  (defn_Val10 : _andBool_ _Val2 _Val9 = some _Val10)
  (defn_Val11 : «_+Int_» PC_CELL 1 = some _Val11)
  (defn_Val12 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gbase_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val12)
  (defn_Val13 : «_-Int_» GAS_CELL _Val12 = some _Val13)
  (req : _Val10 = true)
  (symState : EVM.State)
  -- needed for EVM.step
  (gas gasCost : ℕ)
  -- Necessary assumptions for equivalence
  (cancun : SCHEDULE_CELL = .CANCUN_EVM)
  (gasEnough : 0 < gas)
  (gavailEnough : 2 ≤ GAS_CELL)
  (gavailSmall : GAS_CELL < ↑UInt256.size)
  (gasCostValue : gasCost = GasConstants.Gbase)
  (pcountSmall : PC_CELL + 1 < UInt256.size)
  (pcountNonneg : 0 ≤ PC_CELL):
  EVM.step_push0 gas gasCost (stateMap symState (@push0LHS GAS_CELL PC_CELL K_CELL SCHEDULE_CELL USEGAS_CELL WS _DotVar0 _DotVar2 _Gen0 _Gen1 _Gen10 _Gen11 _Gen12 _Gen13 _Gen14 _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2 _Gen20 _Gen21 _Gen22 _Gen23 _Gen3 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 _Gen9)) =
  .ok (stateMap {symState with execLength := symState.execLength + 1} (@push0RHS _Val11 _Val13 K_CELL SCHEDULE_CELL WS _DotVar0 _DotVar2 _Gen0 _Gen1 _Gen10 _Gen11 _Gen12 _Gen13 _Gen14 _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2 _Gen20 _Gen21 _Gen22 _Gen23 _Gen3 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 _Gen9)) := by
  rw [push0_prestate_equiv, (push0_poststate_equiv PC_CELL)]
  cases gas; contradiction
  rw [EVM.step_push0_summary] <;> try assumption
  simp [push0LHS, push0RHS]; constructor <;> try constructor
  . aesop (add simp [GasConstants.Gbase, «_-Int_», cancun_def, intMap_sub_dist])
  . rw [plusInt_def, ←UInt256.add_succ_mod_size, intMap_add_dist] <;> aesop
  . aesop (add simp [«_+Int_»])

attribute [local simp] GasConstants.Gbase

theorem X_push0_equiv
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
  --(defn_Val5 : notBool_ _Val4 = some _Val5)
  (defn_Val6 : sizeWordStackAux WS 0 = some _Val6)
  (defn_Val7 : «_<Int_» 1023 _Val6 = some _Val7)
  (defn_Val8 : notBool_ _Val7 = some _Val8)
  (defn_Val9 : _andBool_ _Val5 _Val8 = some _Val9)
  (defn_Val10 : _andBool_ _Val2 _Val9 = some _Val10)
  (defn_Val11 : «_+Int_» PC_CELL 1 = some _Val11)
  (defn_Val12 : «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gbase_SCHEDULE_ScheduleConst SCHEDULE_CELL = some _Val12)
  (defn_Val13 : «_-Int_» GAS_CELL _Val12 = some _Val13)
  (req : _Val10 = true)
  (symState : EVM.State)
  -- Necessary assumptions for equivalence
  (cancun : SCHEDULE_CELL = .CANCUN_EVM)
  --(gasEnough : 0 < gas)
  (gavailEnough : 2 < GAS_CELL)
  (gavailSmall : GAS_CELL < ↑UInt256.size)
  (pcountSmall : PC_CELL + 1 < UInt256.size)
  (pcountNonneg : 0 ≤ PC_CELL)
  -- Specific to executing a 1-opcode program
  (codePush0 : _Gen0 = ⟨⟨#[(0x5F : UInt8)]⟩⟩)
  (pcZero : PC_CELL = 0)
  (returnEmpty : _Gen11 = ⟨ByteArray.empty⟩):
  EVM.X false (UInt256.toNat (intMap GAS_CELL)) (stateMap symState (@push0LHS GAS_CELL PC_CELL K_CELL SCHEDULE_CELL USEGAS_CELL WS _DotVar0 _DotVar2 _Gen0 _Gen1 _Gen10 _Gen11 _Gen12 _Gen13 _Gen14 _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2 _Gen20 _Gen21 _Gen22 _Gen23 _Gen3 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 _Gen9)) =
  .ok (.success (stateMap {symState with execLength := symState.execLength + 2} (@push0RHS _Val11 _Val13 K_CELL SCHEDULE_CELL WS _DotVar0 _DotVar2 _Gen0 _Gen1 _Gen10 _Gen11 _Gen12 _Gen13 _Gen14 _Gen15 _Gen16 _Gen17 _Gen18 _Gen19 _Gen2 _Gen20 _Gen21 _Gen22 _Gen23 _Gen3 _Gen4 _Gen5 _Gen6 _Gen7 _Gen8 _Gen9)) ByteArray.empty) := by
  rw [codePush0, pcZero, push0_prestate_equiv, (push0_poststate_equiv PC_CELL)] <;> try assumption
  rw [intMap_toNat] <;> first | linarith | try assumption
  cases cgc: (UInt256.toNat (intMap GAS_CELL))
  . rw [intMap_toNat, Int.toNat_eq_zero] at cgc <;> linarith
  . have pc_equiv : intMap 0 = UInt256.ofNat 0 := rfl
    rw [pc_equiv, ←intMap_toNat, X_push0_summary] <;> first | linarith | try simp
    . aesop (add simp [«_-Int_», intMap_sub_dist, push0LHS, push0RHS])
      (add safe (by rw [intMap_sub_dist])) (add safe (by linarith))
    . rw [intMap_toNat] <;> aesop (add safe (by linarith))
    . simp [defn_Val3] at defn_Val6; subst defn_Val6
      aesop (add simp [sizeWordStack_def, andBool_def, notBool_def,  ltInt_def])
      (add safe (by linarith))

end Push0Equivalence
